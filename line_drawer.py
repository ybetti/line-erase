# -*- coding: utf-8 -*-
"""
Line-drawer: マウスでなぞった線をセグメント単位で抽出するツール
- 骨格線を分岐点で分割し、なぞったセグメント全体を抽出（途切れなし）
- 線は枝分かれしない前提
"""

import tkinter as tk
from tkinter import filedialog, ttk
import cv2
import numpy as np
from PIL import Image, ImageTk
import pymupdf
import os
from skeleton import skeletonize
import time


class LineDrawer:
    def __init__(self, root):
        self.root = root
        self.root.title("Line-drawer")
        self.root.geometry("1400x900")

        # Image state
        self.original_img = None
        self.source_bin = None
        self.segment_labels = None
        self.num_segments = 0
        self.seg_selected = None
        self.work_img = None

        # Display cache
        self.disp_base = None      # Pre-built base display (unselected ink as gray)
        self.display_dirty = True
        self.update_pending = False

        # Navigation
        self.pdf_doc = None
        self.current_page = 0
        self.total_pages = 0
        self.pdf_path = None
        self.dpi = 100  # Lower default for speed

        # View
        self.zoom = 1.0
        self.pan_x = 0
        self.pan_y = 0
        self.img_canvas_x = 0
        self.img_canvas_y = 0
        self.tk_img = None

        # Interaction
        self.painting = False
        self.erasing = False
        self.undo_saved = False
        self.drag_start = None
        self.last_seg = 0  # Track current line for sticky behavior
        self.last_cx = 0
        self.last_cy = 0

        # Undo
        self.undo_stack = []
        self.max_undo = 20

        self._build_ui()
        self._bind_events()

    def _build_ui(self):
        toolbar = tk.Frame(self.root, bd=1, relief=tk.RAISED)
        toolbar.pack(side=tk.TOP, fill=tk.X)

        tk.Button(toolbar, text="PDF開く", command=self.open_pdf, width=10).pack(side=tk.LEFT, padx=2, pady=2)

        tk.Label(toolbar, text="  ページ:").pack(side=tk.LEFT)
        self.page_var = tk.StringVar(value="0 / 0")
        tk.Label(toolbar, textvariable=self.page_var, width=10).pack(side=tk.LEFT)
        tk.Button(toolbar, text="◀", command=self.prev_page, width=3).pack(side=tk.LEFT)
        tk.Button(toolbar, text="▶", command=self.next_page, width=3).pack(side=tk.LEFT)

        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

        # Mode
        self.mode_var = tk.StringVar(value="draw")
        tk.Radiobutton(toolbar, text="抽出", variable=self.mode_var, value="draw").pack(side=tk.LEFT, padx=2)
        tk.Radiobutton(toolbar, text="削除", variable=self.mode_var, value="erase").pack(side=tk.LEFT, padx=2)

        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

        tk.Button(toolbar, text="元に戻す (Ctrl+Z)", command=self.undo, width=14).pack(side=tk.LEFT, padx=2)
        tk.Button(toolbar, text="クリア", command=self.clear_all, width=6).pack(side=tk.LEFT, padx=2)

        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

        tk.Button(toolbar, text="保存 (Ctrl+S)", command=self.save_current, width=12).pack(side=tk.LEFT, padx=2)

        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

        self.zoom_var = tk.StringVar(value="100%")
        tk.Label(toolbar, textvariable=self.zoom_var, width=5).pack(side=tk.LEFT)
        tk.Button(toolbar, text="−", command=self.zoom_out, width=2).pack(side=tk.LEFT)
        tk.Button(toolbar, text="+", command=self.zoom_in, width=2).pack(side=tk.LEFT)
        tk.Button(toolbar, text="全体", command=self.zoom_fit, width=4).pack(side=tk.LEFT)

        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)
        tk.Label(toolbar, text=" DPI:").pack(side=tk.LEFT)
        self.dpi_var = tk.IntVar(value=100)
        tk.Spinbox(toolbar, from_=72, to=600, textvariable=self.dpi_var, width=4).pack(side=tk.LEFT, padx=2)

        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)
        tk.Label(toolbar, text="  左ドラッグ:抽出/削除  右ドラッグ:移動  ホイール:ズーム",
                 fg="gray40").pack(side=tk.LEFT, padx=5)

        # Status
        status_bar = tk.Frame(self.root, bd=1, relief=tk.SUNKEN)
        status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        self.status_var = tk.StringVar(value="PDFファイルを開いてください")
        tk.Label(status_bar, textvariable=self.status_var, anchor=tk.W).pack(side=tk.LEFT, fill=tk.X, expand=True)
        tk.Label(status_bar, text="ホイール:上下  Shift+ホイール:左右  Ctrl+ホイール:ズーム", fg="gray50", anchor=tk.E).pack(side=tk.RIGHT)

        # Canvas
        self.canvas = tk.Canvas(self.root, bg="#888888", cursor="crosshair")
        self.canvas.pack(fill=tk.BOTH, expand=True)

    def _bind_events(self):
        self.canvas.bind("<ButtonPress-1>", self._on_left_press)
        self.canvas.bind("<B1-Motion>", self._on_left_drag)
        self.canvas.bind("<ButtonRelease-1>", self._on_left_release)
        self.canvas.bind("<ButtonPress-3>", self._on_right_press)
        self.canvas.bind("<B3-Motion>", self._on_right_drag)
        self.canvas.bind("<ButtonRelease-3>", self._on_right_release)
        self.canvas.bind("<MouseWheel>", self._on_mousewheel)
        self.canvas.bind("<Configure>", lambda e: self._schedule_display())
        self.root.bind("<Control-z>", lambda e: self.undo())
        self.root.bind("<Control-s>", lambda e: self.save_current())

    # ========== File Operations ==========

    def open_pdf(self):
        path = filedialog.askopenfilename(
            title="ファイルを選択",
            filetypes=[("PDF/画像", "*.pdf *.png *.jpg *.jpeg *.bmp *.tif *.tiff"), ("All files", "*.*")],
            initialdir=r"C:\Users\sealake\Desktop\東部支店図面\図面_PDF"
        )
        if not path:
            return
        self.pdf_path = path
        ext = os.path.splitext(path)[1].lower()
        if ext in ('.png', '.jpg', '.jpeg', '.bmp', '.tif', '.tiff'):
            self.pdf_doc = None
            self.total_pages = 1
            self.current_page = 0
            self.undo_stack.clear()
            self._load_image(path)
        else:
            self.pdf_doc = pymupdf.open(path)
            self.total_pages = len(self.pdf_doc)
            self.current_page = 0
            self.undo_stack.clear()
            self._load_page(0)
        self.root.title(f"Line-drawer - {os.path.basename(path)}")

    def _load_image(self, path):
        img = cv2.imdecode(np.fromfile(path, dtype=np.uint8), cv2.IMREAD_GRAYSCALE)
        if img is None:
            self.status_var.set("画像の読み込みに失敗しました")
            return
        self._process_gray_pair(img, img)

    def _render_gray(self, page, dpi):
        mat = pymupdf.Matrix(dpi / 72, dpi / 72)
        pix = page.get_pixmap(matrix=mat)
        img_array = np.frombuffer(pix.samples, dtype=np.uint8).reshape(pix.h, pix.w, pix.n)
        if pix.n == 4:
            return cv2.cvtColor(img_array, cv2.COLOR_RGBA2GRAY)
        elif pix.n == 3:
            return cv2.cvtColor(img_array, cv2.COLOR_RGB2GRAY)
        return img_array

    def _load_page(self, page_num):
        if not self.pdf_doc:
            return
        self.current_page = page_num
        self.dpi = self.dpi_var.get()
        self.status_var.set(f"ページ {page_num + 1} を読み込み中...")
        self.root.update()

        page = self.pdf_doc[page_num]

        self.display_dpi = 200
        gray_hi = self._render_gray(page, self.display_dpi)
        gray_lo = self._render_gray(page, self.dpi)
        self._process_gray_pair(gray_lo, gray_hi)

    def _process_gray_pair(self, gray_lo, gray_hi):
        self.scale = gray_hi.shape[0] / gray_lo.shape[0]

        self.original_img = gray_hi.copy()
        _, self.source_bin = cv2.threshold(gray_lo, 200, 255, cv2.THRESH_BINARY_INV)
        _, source_bin_hi = cv2.threshold(gray_hi, 200, 255, cv2.THRESH_BINARY_INV)
        self.source_bin_hi = source_bin_hi

        self.status_var.set("骨格線を計算中...")
        self.root.update()

        skel = skeletonize(self.source_bin > 0).astype(np.uint8)

        kernel = np.array([[1, 1, 1],
                           [1, 0, 1],
                           [1, 1, 1]], dtype=np.uint8)
        neighbor_count = cv2.filter2D(skel, cv2.CV_16S, kernel)
        junctions = (skel > 0) & (neighbor_count >= 5)

        # Detect corners on skeleton
        skel_f = skel.astype(np.float32)
        corners = cv2.cornerHarris(skel_f, blockSize=5, ksize=3, k=0.04)
        corner_mask = (skel > 0) & (corners > 0.01 * corners.max())

        # Split at ALL junctions and corners — every segment is a straight line
        split_points = junctions | corner_mask
        split_dilated = split_points.astype(np.uint8)

        skel_no_junc = skel.copy()
        skel_no_junc[split_dilated > 0] = 0

        n_seg, skel_labels = cv2.connectedComponents(skel_no_junc, connectivity=8)

        self.status_var.set("セグメントを拡張中...")
        self.root.update()

        # Expand skeleton labels to full line width
        expanded = skel_labels.copy()
        remaining = (self.source_bin == 255) & (expanded == 0)
        k3 = np.ones((3, 3), np.uint8)
        for _ in range(15):
            if not np.any(remaining):
                break
            dilated = cv2.dilate(expanded.astype(np.float64), k3, iterations=1).astype(np.int32)
            assign = remaining & (dilated > 0)
            expanded[assign] = dilated[assign]
            remaining = (self.source_bin == 255) & (expanded == 0)

        self.segment_labels = expanded
        self.num_segments = n_seg

        # Junction pixels: ink pixels at segment boundaries
        self.junction_mask = (self.source_bin == 255) & (expanded == 0)
        # For each junction pixel, find max adjacent segment label
        # by dilating expanded labels into junction area
        junc_dilated = cv2.dilate(expanded.astype(np.float64),
                                  np.ones((3, 3), np.uint8), iterations=1).astype(np.int32)
        self.junction_seg = np.where(self.junction_mask, junc_dilated, 0)

        # Upscale segment_labels to hi-res
        self.segment_labels_hi = cv2.resize(
            expanded.astype(np.float64),
            (self.source_bin_hi.shape[1], self.source_bin_hi.shape[0]),
            interpolation=cv2.INTER_NEAREST
        ).astype(np.int32)

        self.seg_selected = np.zeros(n_seg, dtype=bool)
        self.work_img = np.zeros_like(self.source_bin_hi)

        # Build display base cache from hi-res
        h_hi, w_hi = self.source_bin_hi.shape
        self.disp_base = np.full((h_hi, w_hi, 3), 255, dtype=np.uint8)
        self.disp_base[self.source_bin_hi == 255] = [210, 210, 210]

        self.undo_stack.clear()
        self.page_var.set(f"{self.current_page + 1} / {self.total_pages}")
        self.status_var.set(
            f"読み込み完了 — {n_seg - 1} セグメント  "
            f"線をなぞって抽出してください"
        )
        self.display_dirty = True
        self.zoom_fit()

    def _rebuild_work_img(self):
        self.work_img = np.zeros_like(self.source_bin_hi)
        selected_mask = self.seg_selected[self.segment_labels_hi]
        self.work_img[selected_mask & (self.source_bin_hi == 255)] = 255
        self._fill_junctions()

    def prev_page(self):
        if self.pdf_doc and self.current_page > 0:
            self._load_page(self.current_page - 1)

    def next_page(self):
        if self.pdf_doc and self.current_page < self.total_pages - 1:
            self._load_page(self.current_page + 1)

    # ========== Display ==========

    def _schedule_display(self):
        """Schedule a display update, throttled to avoid redundant redraws."""
        if not self.update_pending:
            self.update_pending = True
            self.root.after(30, self._do_display)

    def _do_display(self):
        self.update_pending = False
        self._update_display()

    def _update_display(self):
        if self.disp_base is None:
            return
        h, w = self.source_bin_hi.shape

        # Compose display: base + selected overlay
        disp = self.disp_base.copy()
        disp[self.work_img == 255] = [0, 0, 0]

        new_w = max(1, int(w * self.zoom))
        new_h = max(1, int(h * self.zoom))
        if self.zoom < 1.0:
            resized = cv2.resize(disp, (new_w, new_h), interpolation=cv2.INTER_AREA)
        else:
            resized = cv2.resize(disp, (new_w, new_h), interpolation=cv2.INTER_LINEAR)

        resized_rgb = cv2.cvtColor(resized, cv2.COLOR_BGR2RGB)
        pil_img = Image.fromarray(resized_rgb)
        self.tk_img = ImageTk.PhotoImage(pil_img)

        self.canvas.delete("image")
        canvas_w = self.canvas.winfo_width()
        canvas_h = self.canvas.winfo_height()
        self.img_canvas_x = canvas_w // 2 + self.pan_x
        self.img_canvas_y = canvas_h // 2 + self.pan_y
        self.canvas.create_image(self.img_canvas_x, self.img_canvas_y,
                                 anchor=tk.CENTER, image=self.tk_img, tags="image")
        self.zoom_var.set(f"{int(self.zoom * 100)}%")

    def _canvas_to_img(self, cx, cy):
        """Returns coordinates in hi-res image space."""
        if self.source_bin_hi is None:
            return -1, -1
        h, w = self.source_bin_hi.shape
        disp_w = int(w * self.zoom)
        disp_h = int(h * self.zoom)
        img_left = self.img_canvas_x - disp_w // 2
        img_top = self.img_canvas_y - disp_h // 2
        ix = int((cx - img_left) / self.zoom)
        iy = int((cy - img_top) / self.zoom)
        if 0 <= ix < w and 0 <= iy < h:
            return ix, iy
        return -1, -1

    # ========== Mouse ==========

    def _on_left_press(self, event):
        self.painting = True
        self.erasing = (self.mode_var.get() == "erase")
        self.undo_saved = False
        self.last_seg = 0
        self.last_cx = event.x
        self.last_cy = event.y
        self._trace_at(event.x, event.y)

    def _on_left_drag(self, event):
        if self.painting:
            # Interpolate between last and current position
            dx = event.x - self.last_cx
            dy = event.y - self.last_cy
            dist = max(abs(dx), abs(dy))
            if dist > 1:
                steps = max(2, int(dist / 2))
                for i in range(1, steps + 1):
                    t = i / steps
                    mx = int(self.last_cx + dx * t)
                    my = int(self.last_cy + dy * t)
                    self._trace_at(mx, my)
            else:
                self._trace_at(event.x, event.y)
            self.last_cx = event.x
            self.last_cy = event.y

    def _on_left_release(self, event):
        self.painting = False
        self.erasing = False
        self.undo_saved = False
        self.last_seg = 0

    def _on_right_press(self, event):
        self.drag_start = (event.x, event.y)

    def _on_right_drag(self, event):
        if self.drag_start:
            dx = event.x - self.drag_start[0]
            dy = event.y - self.drag_start[1]
            self.pan_x += dx
            self.pan_y += dy
            self.drag_start = (event.x, event.y)
            self._schedule_display()

    def _on_right_release(self, event):
        self.drag_start = None

    def _on_mousewheel(self, event):
        if event.state & 0x0004:  # Ctrl = zoom
            if event.delta > 0:
                self.zoom_in()
            else:
                self.zoom_out()
        elif event.state & 0x0001:  # Shift = horizontal scroll
            scroll = int(event.delta / 120) * 30
            self.pan_x += scroll
            self._update_display()
        else:  # Vertical scroll
            scroll = int(event.delta / 120) * 30
            self.pan_y += scroll
            self._update_display()

    # ========== Trace (select segment at cursor) ==========

    def _seg_direction_score(self, seg, ix_lo, iy_lo, move_dx, move_dy):
        """Score how well a segment's local direction matches cursor movement.
        Uses low-res coordinates."""
        h, w = self.source_bin.shape
        r = 10
        y0 = max(0, iy_lo - r)
        y1 = min(h, iy_lo + r + 1)
        x0 = max(0, ix_lo - r)
        x1 = min(w, ix_lo + r + 1)
        region = self.segment_labels[y0:y1, x0:x1]
        ys, xs = np.where(region == seg)
        if len(xs) < 2:
            return 0.0
        xs = xs.astype(np.float64)
        ys = ys.astype(np.float64)
        cx_s = xs.mean()
        cy_s = ys.mean()
        xs -= cx_s
        ys -= cy_s
        cov_xx = np.sum(xs * xs)
        cov_xy = np.sum(xs * ys)
        cov_yy = np.sum(ys * ys)
        # Principal eigenvector direction
        # For 2x2 matrix, eigenvalues: 0.5*(a+d) +/- sqrt(0.25*(a-d)^2 + b^2)
        a, b, d = cov_xx, cov_xy, cov_yy
        disc = np.sqrt(0.25 * (a - d) ** 2 + b * b)
        lam = 0.5 * (a + d) + disc
        if lam < 1e-6:
            return 0.0
        seg_dx = lam - d
        seg_dy = b
        seg_len = np.sqrt(seg_dx ** 2 + seg_dy ** 2)
        if seg_len < 1e-6:
            seg_dx = b
            seg_dy = lam - a
            seg_len = np.sqrt(seg_dx ** 2 + seg_dy ** 2)
        if seg_len < 1e-6:
            return 0.0
        seg_dx /= seg_len
        seg_dy /= seg_len
        # Cursor movement direction (normalized)
        move_len = np.sqrt(move_dx ** 2 + move_dy ** 2)
        if move_len < 1e-6:
            return 0.5  # No movement info, neutral score
        move_dx /= move_len
        move_dy /= move_len
        # Absolute dot product (line direction is bidirectional)
        return abs(seg_dx * move_dx + seg_dy * move_dy)

    def _trace_at(self, cx, cy):
        ix_hi, iy_hi = self._canvas_to_img(cx, cy)
        if ix_hi < 0:
            return

        # Convert to low-res for segment lookup
        ix = int(ix_hi / self.scale)
        iy = int(iy_hi / self.scale)
        h, w = self.source_bin.shape
        ix = min(ix, w - 1)
        iy = min(iy, h - 1)

        sticky_r = max(12, int(12 / self.zoom))

        # Cursor movement direction (low-res)
        prev_ix_hi, prev_iy_hi = self._canvas_to_img(self.last_cx, self.last_cy)
        if prev_ix_hi >= 0:
            move_dx = float(ix_hi - prev_ix_hi) / self.scale
            move_dy = float(iy_hi - prev_iy_hi) / self.scale
        else:
            move_dx, move_dy = 0.0, 0.0

        seg = 0

        # Sticky behavior (low-res labels)
        if self.last_seg > 0:
            y0 = max(0, iy - sticky_r)
            y1 = min(h, iy + sticky_r + 1)
            x0 = max(0, ix - sticky_r)
            x1 = min(w, ix + sticky_r + 1)
            region = self.segment_labels[y0:y1, x0:x1]
            if np.any(region == self.last_seg):
                seg = self.last_seg

        # Find best segment (low-res)
        if seg == 0:
            seg = self.segment_labels[iy, ix]
            if seg == 0:
                r = max(10, int(10 / self.zoom))
                y0 = max(0, iy - r)
                y1 = min(h, iy + r + 1)
                x0 = max(0, ix - r)
                x1 = min(w, ix + r + 1)
                region = self.segment_labels[y0:y1, x0:x1]
                candidates = np.unique(region)
                candidates = candidates[candidates > 0]

                if len(candidates) == 1:
                    seg = candidates[0]
                elif len(candidates) > 1 and (move_dx != 0 or move_dy != 0):
                    best_score = -1
                    for c in candidates:
                        score = self._seg_direction_score(c, ix, iy, move_dx, move_dy)
                        if score > best_score:
                            best_score = score
                            seg = c
                elif len(candidates) > 1:
                    best_d = float('inf')
                    for c in candidates:
                        ys, xs = np.where(region == c)
                        for sy, sx in zip(ys, xs):
                            d = (sx + x0 - ix) ** 2 + (sy + y0 - iy) ** 2
                            if d < best_d:
                                best_d = d
                                seg = c
                                break

        if seg == 0:
            return

        self.last_seg = seg

        add = not self.erasing
        if self.seg_selected[seg] == add:
            return

        if not self.undo_saved:
            self._push_undo()
            self.undo_saved = True

        self.seg_selected[seg] = add
        # Update work_img at hi-res
        mask = self.segment_labels_hi == seg
        if add:
            self.work_img[mask & (self.source_bin_hi == 255)] = 255
        else:
            self.work_img[mask] = 0

        self._fill_junctions()
        self._schedule_display()

    # ========== Junction Fill ==========

    def _fill_junctions(self):
        """Fill junction pixels at hi-res."""
        # Upscaled junction: hi-res pixels not assigned to any segment but are ink
        junc_hi = (self.source_bin_hi == 255) & (self.segment_labels_hi == 0)
        # Check if any neighbor segment is selected by dilating selected mask
        sel_mask = self.seg_selected[self.segment_labels_hi] & (self.source_bin_hi == 255)
        sel_dilated = cv2.dilate(sel_mask.astype(np.uint8), np.ones((3, 3), np.uint8), iterations=1)
        fill = junc_hi & (sel_dilated > 0)
        self.work_img[junc_hi] = 0
        self.work_img[fill] = 255

    # ========== Clear / Undo ==========

    def clear_all(self):
        if self.seg_selected is None:
            return
        self._push_undo()
        self.seg_selected[:] = False
        self.work_img = np.zeros_like(self.source_bin_hi)
        self._update_display()
        self.status_var.set("クリアしました")

    def _push_undo(self):
        if len(self.undo_stack) >= self.max_undo:
            self.undo_stack.pop(0)
        self.undo_stack.append(self.seg_selected.copy())

    def undo(self):
        if not self.undo_stack:
            self.status_var.set("履歴がありません")
            return
        self.seg_selected = self.undo_stack.pop()
        self._rebuild_work_img()
        self._update_display()
        self.status_var.set("元に戻しました")

    # ========== Zoom ==========

    def zoom_in(self):
        self.zoom = min(self.zoom * 1.25, 10.0)
        self._update_display()

    def zoom_out(self):
        self.zoom = max(self.zoom / 1.25, 0.05)
        self._update_display()

    def zoom_fit(self):
        if self.source_bin_hi is None:
            return
        h, w = self.source_bin_hi.shape
        canvas_w = max(self.canvas.winfo_width(), 100)
        canvas_h = max(self.canvas.winfo_height(), 100)
        self.zoom = min(canvas_w / w, canvas_h / h) * 0.95
        self.pan_x = 0
        self.pan_y = 0
        self._update_display()

    # ========== Save ==========

    def save_current(self):
        if self.work_img is None:
            self.status_var.set("保存する画像がありません")
            return
        path = filedialog.asksaveasfilename(
            title="画像を保存",
            defaultextension=".jpg",
            filetypes=[("JPEG files", "*.jpg")],
            initialdir=r"C:\Users\sealake\Desktop\extracted_lines",
            initialfile=f"page_{self.current_page + 1:02d}.jpg"
        )
        if not path:
            return
        output = 255 - self.work_img
        success, buf = cv2.imencode('.jpg', output, [cv2.IMWRITE_JPEG_QUALITY, 95])
        if success:
            with open(path, 'wb') as f:
                f.write(buf)
            self.status_var.set(f"保存しました: {path}")


def main():
    root = tk.Tk()
    app = LineDrawer(root)
    root.mainloop()


if __name__ == "__main__":
    main()

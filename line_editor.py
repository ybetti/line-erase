# -*- coding: utf-8 -*-
"""
船舶図面 線抽出エディタ v5
- 骨格線を分岐点で分割し、各セグメントを独立した選択単位にする
- クリックでセグメント単位の除去/抽出
- 線は枝分かれしない前提で、分岐点＝他の線との交差点
"""

import tkinter as tk
from tkinter import filedialog, ttk
import cv2
import numpy as np
from PIL import Image, ImageTk
import pymupdf
import os
from skeleton import skeletonize


class LineEditor:
    def __init__(self, root):
        self.root = root
        self.root.title("図面線抽出エディタ")
        self.root.geometry("1400x900")

        # Image state
        self.original_img = None
        self.source_bin = None       # Cleaned binary (255=ink)
        self.segment_labels = None   # Per-pixel segment ID (0=background)
        self.num_segments = 0
        self.seg_selected = None     # Boolean per segment: True=selected
        self.work_img = None         # Display output

        # Navigation
        self.pdf_doc = None
        self.current_page = 0
        self.total_pages = 0
        self.pdf_path = None
        self.dpi = 100

        # View
        self.zoom = 1.0
        self.pan_x = 0
        self.pan_y = 0
        self.img_canvas_x = 0
        self.img_canvas_y = 0
        self.tk_img = None

        # Interaction
        self.mode = "remove"
        self.press_pos = None      # (cx, cy) at press for click vs drag detection
        self.dragging = False      # True if drag distance exceeded threshold
        self.rect_id = None
        self.drag_start = None     # For panning (right-click)
        self.drag_threshold = 4    # Pixels to distinguish click from drag

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
        tk.Label(toolbar, text="  モード:").pack(side=tk.LEFT)
        self.mode_var = tk.StringVar(value="remove")
        modes = [
            ("除去", "remove"),
            ("抽出", "add"),
        ]
        for text, val in modes:
            tk.Radiobutton(toolbar, text=text, variable=self.mode_var, value=val,
                           command=self._mode_changed).pack(side=tk.LEFT, padx=2)

        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

        tk.Button(toolbar, text="全選択", command=self.select_all, width=6).pack(side=tk.LEFT, padx=2)
        tk.Button(toolbar, text="全解除", command=self.deselect_all, width=6).pack(side=tk.LEFT, padx=2)
        tk.Button(toolbar, text="元に戻す", command=self.undo, width=8).pack(side=tk.LEFT, padx=2)

        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

        tk.Button(toolbar, text="保存", command=self.save_current, width=6).pack(side=tk.LEFT, padx=2)

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
        self.canvas.bind("<Motion>", self._on_mouse_move)
        self.canvas.bind("<Configure>", lambda e: self._update_display())
        self.root.bind("<Control-z>", lambda e: self.undo())
        self.root.bind("<Control-s>", lambda e: self.save_current())

    def _mode_changed(self):
        self.mode = self.mode_var.get()

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
            self.image_path = path
            self.undo_stack.clear()
            self._load_image(path)
        else:
            self.pdf_doc = pymupdf.open(path)
            self.image_path = None
            self.total_pages = len(self.pdf_doc)
            self.current_page = 0
            self.undo_stack.clear()
            self._load_page(0)
        self.root.title(f"図面線抽出エディタ - {os.path.basename(path)}")

    def _load_image(self, path):
        """Load an image file directly."""
        img = cv2.imdecode(np.fromfile(path, dtype=np.uint8), cv2.IMREAD_GRAYSCALE)
        if img is None:
            self.status_var.set("画像の読み込みに失敗しました")
            return
        self._process_gray(img)

    def _load_page(self, page_num):
        if not self.pdf_doc:
            return
        self.current_page = page_num
        self.dpi = self.dpi_var.get()
        self.status_var.set(f"ページ {page_num + 1} を読み込み中...")
        self.root.update()

        page = self.pdf_doc[page_num]
        mat = pymupdf.Matrix(self.dpi / 72, self.dpi / 72)
        pix = page.get_pixmap(matrix=mat)
        img_array = np.frombuffer(pix.samples, dtype=np.uint8).reshape(pix.h, pix.w, pix.n)
        if pix.n == 4:
            gray = cv2.cvtColor(img_array, cv2.COLOR_RGBA2GRAY)
        elif pix.n == 3:
            gray = cv2.cvtColor(img_array, cv2.COLOR_RGB2GRAY)
        else:
            gray = img_array
        self._process_gray(gray)

    def _process_gray(self, gray):
        self.original_img = gray.copy()
        _, self.source_bin = cv2.threshold(gray, 200, 255, cv2.THRESH_BINARY_INV)

        self.status_var.set("骨格線を計算中...")
        self.root.update()

        skel = skeletonize(self.source_bin > 0).astype(np.uint8)

        kernel = np.array([[1, 1, 1],
                           [1, 0, 1],
                           [1, 1, 1]], dtype=np.uint8)
        neighbor_count = cv2.filter2D(skel, cv2.CV_16S, kernel)
        junctions = (skel > 0) & (neighbor_count >= 5)

        skel_f = skel.astype(np.float32)
        corners = cv2.cornerHarris(skel_f, blockSize=5, ksize=3, k=0.04)
        corner_mask = (skel > 0) & (corners > 0.01 * corners.max())

        split_points = junctions | corner_mask
        split_dilated = split_points.astype(np.uint8)

        skel_no_junc = skel.copy()
        skel_no_junc[split_dilated > 0] = 0

        n_seg, skel_labels = cv2.connectedComponents(skel_no_junc, connectivity=8)

        self.status_var.set("セグメントを拡張中...")
        self.root.update()

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

        self.seg_selected = np.ones(n_seg, dtype=bool)
        self.seg_selected[0] = False
        self._rebuild_work_img()

        self.undo_stack.clear()
        self.page_var.set(f"{self.current_page + 1} / {self.total_pages}")
        self.status_var.set(
            f"読み込み完了 — {n_seg - 1} セグメント  "
            f"クリックで線セグメントを除去/抽出できます"
        )
        self.zoom_fit()

    def _rebuild_work_img(self):
        self.work_img = np.zeros_like(self.source_bin)
        selected_mask = self.seg_selected[self.segment_labels]
        self.work_img[selected_mask & (self.source_bin == 255)] = 255

    def prev_page(self):
        if self.pdf_doc and self.current_page > 0:
            self._load_page(self.current_page - 1)

    def next_page(self):
        if self.pdf_doc and self.current_page < self.total_pages - 1:
            self._load_page(self.current_page + 1)

    # ========== Display ==========

    def _update_display(self):
        if self.source_bin is None:
            return
        h, w = self.source_bin.shape

        disp = np.full((h, w, 3), 255, dtype=np.uint8)
        unselected_ink = (self.source_bin == 255) & (self.work_img == 0)
        disp[unselected_ink] = [255, 255, 255]
        disp[self.work_img == 255] = [0, 0, 0]

        new_w = max(1, int(w * self.zoom))
        new_h = max(1, int(h * self.zoom))
        if self.zoom < 1.0:
            resized = cv2.resize(disp, (new_w, new_h), interpolation=cv2.INTER_AREA)
        else:
            resized = cv2.resize(disp, (new_w, new_h), interpolation=cv2.INTER_LANCZOS4)

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
        if self.source_bin is None:
            return None, None
        h, w = self.source_bin.shape
        disp_w = int(w * self.zoom)
        disp_h = int(h * self.zoom)
        img_left = self.img_canvas_x - disp_w // 2
        img_top = self.img_canvas_y - disp_h // 2
        ix = int((cx - img_left) / self.zoom)
        iy = int((cy - img_top) / self.zoom)
        if 0 <= ix < w and 0 <= iy < h:
            return ix, iy
        return None, None

    # ========== Mouse ==========

    def _on_mouse_move(self, event):
        self.canvas.delete("cursor")

    def _on_left_press(self, event):
        self.press_pos = (event.x, event.y)
        self.dragging = False

    def _on_left_drag(self, event):
        if self.press_pos is None:
            return
        x0, y0 = self.press_pos
        dx = abs(event.x - x0)
        dy = abs(event.y - y0)
        if dx > self.drag_threshold or dy > self.drag_threshold:
            self.dragging = True
        if self.dragging:
            if self.rect_id:
                self.canvas.delete(self.rect_id)
            add = (self.mode_var.get() == "add")
            color = "blue" if add else "red"
            self.rect_id = self.canvas.create_rectangle(
                x0, y0, event.x, event.y, outline=color, width=2, dash=(4, 4)
            )

    def _on_left_release(self, event):
        if self.press_pos is None:
            return
        add = (self.mode_var.get() == "add")
        if self.dragging:
            # Rect action
            if self.rect_id:
                self.canvas.delete(self.rect_id)
                self.rect_id = None
            x0, y0 = self.press_pos
            self._rect_action(x0, y0, event.x, event.y, add=add)
        else:
            # Click action
            self._click_segment(event.x, event.y, add=add)
        self.press_pos = None
        self.dragging = False

    def _on_right_press(self, event):
        self.drag_start = (event.x, event.y)

    def _on_right_drag(self, event):
        if self.drag_start:
            dx = event.x - self.drag_start[0]
            dy = event.y - self.drag_start[1]
            self.pan_x += dx
            self.pan_y += dy
            self.drag_start = (event.x, event.y)
            self._update_display()

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

    # ========== Click Segment ==========

    def _find_segment_at(self, cx, cy):
        """Find the segment label at canvas position, searching nearby pixels."""
        ix, iy = self._canvas_to_img(cx, cy)
        if ix is None:
            return 0
        h, w = self.source_bin.shape
        search_r = max(10, int(10 / self.zoom))
        best_label = 0
        best_dist = float('inf')
        for dy in range(-search_r, search_r + 1):
            for dx in range(-search_r, search_r + 1):
                ny, nx = iy + dy, ix + dx
                if 0 <= ny < h and 0 <= nx < w:
                    lbl = self.segment_labels[ny, nx]
                    if lbl > 0:
                        d = dx * dx + dy * dy
                        if d < best_dist:
                            best_dist = d
                            best_label = lbl
        return best_label

    def _click_segment(self, cx, cy, add=True):
        seg = self._find_segment_at(cx, cy)
        if seg == 0:
            self.status_var.set("線がありません")
            return
        if self.seg_selected[seg] == add:
            state = "選択済み" if add else "未選択"
            self.status_var.set(f"セグメント {seg} は既に{state}です")
            return

        self._push_undo()
        self.seg_selected[seg] = add
        # Incremental update
        mask = self.segment_labels == seg
        if add:
            self.work_img[mask & (self.source_bin == 255)] = 255
        else:
            self.work_img[mask] = 0
        self._update_display()
        action = "抽出" if add else "除去"
        self.status_var.set(f"セグメント {seg} を{action}しました")

    # ========== Rect Action ==========

    def _rect_action(self, cx0, cy0, cx1, cy1, add=True):
        ix0, iy0 = self._canvas_to_img(min(cx0, cx1), min(cy0, cy1))
        ix1, iy1 = self._canvas_to_img(max(cx0, cx1), max(cy0, cy1))
        if ix0 is None or ix1 is None:
            return
        h, w = self.source_bin.shape
        ix0, iy0 = max(0, ix0), max(0, iy0)
        ix1, iy1 = min(w, ix1), min(h, iy1)
        if ix1 - ix0 < 3 or iy1 - iy0 < 3:
            return

        region = self.segment_labels[iy0:iy1, ix0:ix1]
        segs = np.unique(region)
        segs = segs[segs > 0]
        if len(segs) == 0:
            return

        self._push_undo()
        for seg in segs:
            self.seg_selected[seg] = add
        self._rebuild_work_img()
        self._update_display()
        action = "抽出" if add else "除去"
        self.status_var.set(f"矩形内の {len(segs)} セグメントを{action}しました")

    # ========== Select All / Deselect ==========

    def select_all(self):
        if self.seg_selected is None:
            return
        self._push_undo()
        self.seg_selected[1:] = True
        self._rebuild_work_img()
        self._update_display()
        self.status_var.set("全セグメントを選択しました")

    def deselect_all(self):
        if self.seg_selected is None:
            return
        self._push_undo()
        self.seg_selected[:] = False
        self._rebuild_work_img()
        self._update_display()
        self.status_var.set("全選択を解除しました")

    # ========== Undo ==========

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
        if self.source_bin is None:
            return
        h, w = self.source_bin.shape
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
    app = LineEditor(root)
    root.mainloop()


if __name__ == "__main__":
    main()

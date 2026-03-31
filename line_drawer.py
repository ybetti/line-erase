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
from skimage.morphology import skeletonize
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
        self.dpi = 150  # Lower default for speed

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
        self.dpi_var = tk.IntVar(value=150)
        tk.Spinbox(toolbar, from_=72, to=600, textvariable=self.dpi_var, width=4).pack(side=tk.LEFT, padx=2)

        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)
        tk.Label(toolbar, text="  左ドラッグ:抽出  Shift+左:消去  右ドラッグ:移動  ホイール:ズーム",
                 fg="gray40").pack(side=tk.LEFT, padx=5)

        # Status
        status_bar = tk.Frame(self.root, bd=1, relief=tk.SUNKEN)
        status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        self.status_var = tk.StringVar(value="PDFファイルを開いてください")
        tk.Label(status_bar, textvariable=self.status_var, anchor=tk.W).pack(fill=tk.X)

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
            title="PDFファイルを選択",
            filetypes=[("PDF files", "*.pdf"), ("All files", "*.*")],
            initialdir=r"C:\Users\sealake\Desktop\東部支店図面\図面_PDF"
        )
        if not path:
            return
        self.pdf_path = path
        self.pdf_doc = pymupdf.open(path)
        self.total_pages = len(self.pdf_doc)
        self.current_page = 0
        self.undo_stack.clear()
        self._load_page(0)
        self.root.title(f"Line-drawer - {os.path.basename(path)}")

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

        self.original_img = gray.copy()
        _, raw_bin = cv2.threshold(gray, 200, 255, cv2.THRESH_BINARY_INV)

        # Remove only text (compact shapes), keep all lines
        n_raw, lbl_raw, stats_raw, _ = cv2.connectedComponentsWithStats(raw_bin, connectivity=8)
        cleaned = np.zeros_like(raw_bin)
        for i in range(1, n_raw):
            area = stats_raw[i, cv2.CC_STAT_AREA]
            cw = stats_raw[i, cv2.CC_STAT_WIDTH]
            ch = stats_raw[i, cv2.CC_STAT_HEIGHT]
            aspect = max(cw, ch) / (min(cw, ch) + 1)
            # Remove only small compact shapes (text characters)
            # Keep elongated shapes (lines) regardless of size
            if area < 50:
                continue  # Noise dots
            if area < 200 and aspect < 3:
                continue  # Small text characters
            cleaned[lbl_raw == i] = 255
        self.source_bin = cleaned

        # Skeletonize and segment
        self.status_var.set(f"ページ {page_num + 1} 骨格線を計算中...")
        self.root.update()

        skel = skeletonize(cleaned > 0).astype(np.uint8)

        kernel = np.array([[1, 1, 1],
                           [1, 0, 1],
                           [1, 1, 1]], dtype=np.uint8)
        neighbor_count = cv2.filter2D(skel, cv2.CV_16S, kernel)
        junctions = (skel > 0) & (neighbor_count >= 3)
        junction_dilated = cv2.dilate(junctions.astype(np.uint8), np.ones((3, 3), np.uint8), iterations=1)

        skel_no_junc = skel.copy()
        skel_no_junc[junction_dilated > 0] = 0

        n_seg, skel_labels = cv2.connectedComponents(skel_no_junc, connectivity=8)

        self.status_var.set(f"ページ {page_num + 1} セグメントを拡張中...")
        self.root.update()

        # Expand skeleton labels to full line width
        expanded = skel_labels.copy()
        remaining = (cleaned == 255) & (expanded == 0)
        k3 = np.ones((3, 3), np.uint8)
        for _ in range(15):
            if not np.any(remaining):
                break
            dilated = cv2.dilate(expanded.astype(np.float64), k3, iterations=1).astype(np.int32)
            assign = remaining & (dilated > 0)
            expanded[assign] = dilated[assign]
            remaining = (cleaned == 255) & (expanded == 0)

        self.segment_labels = expanded
        self.num_segments = n_seg

        # Junction pixels: ink pixels at segment boundaries
        # These should appear when any adjacent segment is selected
        self.junction_mask = (cleaned == 255) & (expanded == 0)
        # Also find which segments are adjacent to each junction pixel
        # by dilating each junction pixel and checking neighbors
        # Pre-compute: for each junction pixel, store adjacent segment set
        # For efficiency, store as a neighbor lookup per junction pixel
        junc_ys, junc_xs = np.where(self.junction_mask)
        self.junction_adj = {}  # (y,x) -> set of adjacent segment labels
        for jy, jx in zip(junc_ys, junc_xs):
            adj = set()
            for dy in (-1, 0, 1):
                for dx in (-1, 0, 1):
                    ny, nx = jy + dy, jx + dx
                    if 0 <= ny < h and 0 <= nx < w:
                        lbl = expanded[ny, nx]
                        if lbl > 0:
                            adj.add(lbl)
            if adj:
                self.junction_adj[(jy, jx)] = adj

        self.seg_selected = np.zeros(n_seg, dtype=bool)
        self.work_img = np.zeros_like(self.source_bin)

        # Build display base cache (unselected ink as gray on white)
        self.disp_base = np.full((cleaned.shape[0], cleaned.shape[1], 3), 255, dtype=np.uint8)
        self.disp_base[cleaned == 255] = [210, 210, 210]

        self.undo_stack.clear()
        self.page_var.set(f"{page_num + 1} / {self.total_pages}")
        self.status_var.set(
            f"ページ {page_num + 1} 読み込み完了 — {n_seg - 1} セグメント  "
            f"線をなぞって抽出してください"
        )
        self.display_dirty = True
        self.zoom_fit()

    def _rebuild_work_img(self):
        self.work_img = np.zeros_like(self.source_bin)
        selected_mask = self.seg_selected[self.segment_labels]
        self.work_img[selected_mask & (self.source_bin == 255)] = 255
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
        h, w = self.source_bin.shape

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
        if self.source_bin is None:
            return -1, -1
        h, w = self.source_bin.shape
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
        self.erasing = bool(event.state & 0x0001)  # Shift
        self.undo_saved = False
        self._trace_at(event.x, event.y)

    def _on_left_drag(self, event):
        if self.painting:
            self._trace_at(event.x, event.y)

    def _on_left_release(self, event):
        self.painting = False
        self.erasing = False
        self.undo_saved = False

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
        if event.delta > 0:
            self.zoom_in()
        else:
            self.zoom_out()

    # ========== Trace (select segment at cursor) ==========

    def _trace_at(self, cx, cy):
        ix, iy = self._canvas_to_img(cx, cy)
        if ix < 0:
            return

        h, w = self.source_bin.shape

        # Direct pixel check first (fast path)
        seg = self.segment_labels[iy, ix]

        # If background, search small neighborhood
        if seg == 0:
            r = max(3, int(3 / self.zoom))
            best_d = float('inf')
            for dy in range(-r, r + 1):
                ny = iy + dy
                if ny < 0 or ny >= h:
                    continue
                for dx in range(-r, r + 1):
                    nx = ix + dx
                    if nx < 0 or nx >= w:
                        continue
                    lbl = self.segment_labels[ny, nx]
                    if lbl > 0:
                        d = dx * dx + dy * dy
                        if d < best_d:
                            best_d = d
                            seg = lbl

        if seg == 0:
            return

        add = not self.erasing
        if self.seg_selected[seg] == add:
            return  # Already in desired state

        if not self.undo_saved:
            self._push_undo()
            self.undo_saved = True

        self.seg_selected[seg] = add
        mask = self.segment_labels == seg
        if add:
            self.work_img[mask & (self.source_bin == 255)] = 255
        else:
            self.work_img[mask] = 0

        self._fill_junctions()
        self._schedule_display()

    # ========== Junction Fill ==========

    def _fill_junctions(self):
        """Fill junction pixels when adjacent segments are selected."""
        for (jy, jx), adj_segs in self.junction_adj.items():
            if any(self.seg_selected[s] for s in adj_segs):
                self.work_img[jy, jx] = 255
            else:
                self.work_img[jy, jx] = 0

    # ========== Clear / Undo ==========

    def clear_all(self):
        if self.seg_selected is None:
            return
        self._push_undo()
        self.seg_selected[:] = False
        self.work_img = np.zeros_like(self.source_bin)
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
            defaultextension=".png",
            filetypes=[("PNG files", "*.png")],
            initialdir=r"C:\Users\sealake\Desktop\extracted_lines",
            initialfile=f"page_{self.current_page + 1:02d}.png"
        )
        if not path:
            return
        output = 255 - self.work_img
        success, buf = cv2.imencode('.png', output)
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

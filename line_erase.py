# -*- coding: utf-8 -*-
"""
Line-erase: PDFを表示し、線の消去 + 図形スタンプ配置ツール
- ペン消去 / 範囲選択消去
- ×印・丸数字・矢印の配置と移動
- 原図切り替え表示（薄く表示）
"""

import tkinter as tk
from tkinter import filedialog, ttk
import cv2
import numpy as np
from PIL import Image, ImageTk
import pymupdf
import os
import math
import time


class LineEraser:
    def __init__(self, root):
        self.root = root
        self.root.title("Line-erase — 線消去ツール")
        self.root.geometry("1400x900")

        # Image state
        self.original_img = None
        self.source_bin = None
        self.erase_mask = None
        self.work_img = None

        # Navigation
        self.pdf_doc = None
        self.current_page = 0
        self.total_pages = 0
        self.pdf_path = None
        self.dpi = 200

        # View
        self.zoom = 1.0
        self.pan_x = 0
        self.pan_y = 0
        self.img_canvas_x = 0
        self.img_canvas_y = 0
        self.tk_img = None

        # Mode: "pen", "rect", "cross", "number", "arrow", "move"
        self.mode = "pen"

        # Pen
        self.pen_size = 20
        self.erasing = False
        self.cursor_rect_id = None

        # Rect selection
        self.rect_start = None
        self.rect_id = None

        # Stamps: list of dicts
        #   {"type": "cross",  "x": img_x, "y": img_y, "size": 12}
        #   {"type": "number", "x": img_x, "y": img_y, "size": 14, "number": 1}
        #   {"type": "arrow",  "x1": img_x, "y1": img_y, "x2": img_x2, "y2": img_y2}
        self.stamps = []
        self.stamp_size = 6   # Default stamp size (image pixels)

        # Arrow placement state
        self.arrow_start = None  # (img_x, img_y) of first click

        # Move / selection state
        self.moving_idx = None       # Index of stamp being moved
        self.move_offset = (0, 0)    # Offset from stamp center to grab point
        self.move_arrow_end = False  # Moving arrow endpoint vs startpoint
        self.selected_idx = -1       # Currently selected stamp index

        # Pan
        self.drag_start = None

        # Display cache for fast erasing
        self._disp_cache = None      # Pre-built BGR image (full size, no stamps)
        self._disp_cache_valid = False
        self._last_draw_time = 0     # For throttling display updates

        # Undo
        self.undo_stack = []
        self.max_undo = 30
        self.stroke_points = []

        self._build_ui()
        self._bind_events()

    def _build_ui(self):
        toolbar = tk.Frame(self.root, bd=1, relief=tk.RAISED)
        toolbar.pack(side=tk.TOP, fill=tk.X)

        # === Row 1: File, Page, Mode, Pen, Actions, View ===
        row1 = tk.Frame(toolbar)
        row1.pack(side=tk.TOP, fill=tk.X)

        tk.Button(row1, text="PDF開く", command=self.open_pdf, width=10).pack(side=tk.LEFT, padx=2, pady=2)

        tk.Label(row1, text="  ページ:").pack(side=tk.LEFT)
        self.page_var = tk.StringVar(value="0 / 0")
        tk.Label(row1, textvariable=self.page_var, width=10).pack(side=tk.LEFT)
        tk.Button(row1, text="◀", command=self.prev_page, width=3).pack(side=tk.LEFT)
        tk.Button(row1, text="▶", command=self.next_page, width=3).pack(side=tk.LEFT)

        ttk.Separator(row1, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

        # Mode selection
        tk.Label(row1, text="  モード:").pack(side=tk.LEFT)
        self.mode_var = tk.StringVar(value="pen")
        modes_before = [
            ("ペン消去", "pen"),
            ("範囲選択", "rect"),
            ("×印", "cross"),
        ]
        for text, val in modes_before:
            tk.Radiobutton(row1, text=text, variable=self.mode_var, value=val,
                           command=self._mode_changed).pack(side=tk.LEFT, padx=1)

        # Number mode + spinbox together
        tk.Radiobutton(row1, text="数字", variable=self.mode_var, value="number",
                       command=self._mode_changed).pack(side=tk.LEFT, padx=1)
        self.number_var = tk.IntVar(value=1)
        self.number_spin = tk.Spinbox(row1, from_=1, to=999, textvariable=self.number_var,
                                       width=3, font=("", 10, "bold"))
        self.number_spin.pack(side=tk.LEFT, padx=(0, 2))

        modes_after = [
            ("矢印", "arrow"),
            ("移動", "move"),
            ("図形削除", "delete_stamp"),
        ]
        for text, val in modes_after:
            tk.Radiobutton(row1, text=text, variable=self.mode_var, value=val,
                           command=self._mode_changed).pack(side=tk.LEFT, padx=1)

        ttk.Separator(row1, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

        # Pen size (for pen mode)
        tk.Label(row1, text=" ペン太さ:").pack(side=tk.LEFT)
        self.pen_size_var = tk.IntVar(value=20)
        self.pen_size_var.trace_add("write", self._on_pen_size_changed)
        tk.Spinbox(row1, from_=2, to=200, textvariable=self.pen_size_var, width=4).pack(side=tk.LEFT, padx=2)

        self.pen_slider = tk.Scale(row1, from_=2, to=200, orient=tk.HORIZONTAL,
                                   variable=self.pen_size_var, showvalue=False, length=100)
        self.pen_slider.pack(side=tk.LEFT, padx=2)

        ttk.Separator(row1, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

        # Actions
        tk.Button(row1, text="元に戻す", command=self.undo, width=8).pack(side=tk.LEFT, padx=2)
        tk.Button(row1, text="全復元", command=self.restore_all, width=6).pack(side=tk.LEFT, padx=2)

        ttk.Separator(row1, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

        self.show_bg_var = tk.BooleanVar(value=False)
        tk.Checkbutton(row1, text="原図表示", variable=self.show_bg_var,
                       command=self._on_bg_toggle).pack(side=tk.LEFT, padx=4)

        ttk.Separator(row1, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

        tk.Button(row1, text="保存", command=self.save_current, width=6).pack(side=tk.LEFT, padx=2)

        ttk.Separator(row1, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

        self.zoom_var = tk.StringVar(value="100%")
        tk.Label(row1, textvariable=self.zoom_var, width=5).pack(side=tk.LEFT)
        tk.Button(row1, text="−", command=self.zoom_out, width=2).pack(side=tk.LEFT)
        tk.Button(row1, text="+", command=self.zoom_in, width=2).pack(side=tk.LEFT)
        tk.Button(row1, text="全体", command=self.zoom_fit, width=4).pack(side=tk.LEFT)

        ttk.Separator(row1, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

        tk.Label(row1, text=" DPI:").pack(side=tk.LEFT)
        self.dpi_var = tk.IntVar(value=200)
        tk.Spinbox(row1, from_=72, to=600, textvariable=self.dpi_var, width=4).pack(side=tk.LEFT, padx=2)

        # === Row 2: Stamp settings ===
        row2 = tk.Frame(toolbar)
        row2.pack(side=tk.TOP, fill=tk.X)

        # Stamp size
        tk.Label(row2, text=" 図形サイズ:").pack(side=tk.LEFT)
        self.stamp_size_var = tk.IntVar(value=6)
        self.stamp_size_var.trace_add("write", self._on_stamp_size_changed)
        tk.Spinbox(row2, from_=6, to=100, textvariable=self.stamp_size_var, width=4).pack(side=tk.LEFT, padx=2)
        tk.Label(row2, text="px").pack(side=tk.LEFT)

        self.stamp_slider = tk.Scale(row2, from_=6, to=100, orient=tk.HORIZONTAL,
                                      variable=self.stamp_size_var, showvalue=False, length=100)
        self.stamp_slider.pack(side=tk.LEFT, padx=2)

        ttk.Separator(row2, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

        # Delete selected stamp
        tk.Button(row2, text="全図形削除", command=self.delete_all_stamps, width=8).pack(side=tk.LEFT, padx=2)

        ttk.Separator(row2, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

        # Arrow hint
        self.arrow_hint_var = tk.StringVar(value="")
        tk.Label(row2, textvariable=self.arrow_hint_var, fg="blue").pack(side=tk.LEFT, padx=4)

        # Pan direction buttons (cross layout, right-aligned, grid)
        pan_step = 80
        btn_w, btn_h = 3, 1
        pan_frame = tk.Frame(row2)
        pan_frame.pack(side=tk.RIGHT, padx=4)
        tk.Button(pan_frame, text="↑", width=btn_w, height=btn_h,
                  command=lambda: self._pan_by(0, pan_step)).grid(row=0, column=1)
        tk.Button(pan_frame, text="←", width=btn_w, height=btn_h,
                  command=lambda: self._pan_by(pan_step, 0)).grid(row=1, column=0)
        tk.Button(pan_frame, text="↓", width=btn_w, height=btn_h,
                  command=lambda: self._pan_by(0, -pan_step)).grid(row=1, column=1)
        tk.Button(pan_frame, text="→", width=btn_w, height=btn_h,
                  command=lambda: self._pan_by(-pan_step, 0)).grid(row=1, column=2)

        # Status bar
        status_bar = tk.Frame(self.root, bd=1, relief=tk.SUNKEN)
        status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        self.status_var = tk.StringVar(value="PDFファイルを開いてください")
        tk.Label(status_bar, textvariable=self.status_var, anchor=tk.W).pack(side=tk.LEFT, fill=tk.X, expand=True)
        tk.Label(status_bar, text="右ドラッグ:パン  Ctrl+ホイール:ズーム  Shift+ホイール:横スクロール",
                 fg="gray50", anchor=tk.E).pack(side=tk.RIGHT)

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
        self.canvas.bind("<Leave>", self._on_mouse_leave)
        self.canvas.bind("<Configure>", lambda e: self._update_display())
        self.root.bind("<Control-z>", lambda e: self.undo())
        self.root.bind("<Control-s>", lambda e: self.save_current())
        self.root.bind("<Delete>", lambda e: self.delete_selected_stamp())

    def _on_bg_toggle(self):
        self._disp_cache_valid = False
        self._update_display()

    def _mode_changed(self):
        self.mode = self.mode_var.get()
        # Reset arrow placement state when switching away
        if self.mode != "arrow":
            self.arrow_start = None
            self.arrow_hint_var.set("")
        else:
            self.arrow_hint_var.set("← 始点をクリック")
        # Reset move state
        if self.mode != "move":
            self.moving_idx = None

    def _on_pen_size_changed(self, *args):
        try:
            self.pen_size = self.pen_size_var.get()
        except tk.TclError:
            pass

    def _on_stamp_size_changed(self, *args):
        try:
            self.stamp_size = self.stamp_size_var.get()
        except tk.TclError:
            pass

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
        self.root.title(f"Line-erase — {os.path.basename(path)}")

    def _load_image(self, path):
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
        self.erase_mask = np.zeros(self.source_bin.shape, dtype=bool)
        self.stamps = []
        self._rebuild_work_img()

        self.undo_stack.clear()
        self.page_var.set(f"{self.current_page + 1} / {self.total_pages}")

        ink_pixels = int(np.sum(self.source_bin == 255))
        self.status_var.set(
            f"読み込み完了 — {self.source_bin.shape[1]}x{self.source_bin.shape[0]}  "
            f"線ピクセル: {ink_pixels:,}"
        )
        self.zoom_fit()

    def _rebuild_work_img(self):
        self.work_img = self.source_bin.copy()
        self.work_img[self.erase_mask] = 0
        self._disp_cache_valid = False

    # ========== Page Navigation ==========

    def prev_page(self):
        if self.pdf_doc and self.current_page > 0:
            self._load_page(self.current_page - 1)

    def next_page(self):
        if self.pdf_doc and self.current_page < self.total_pages - 1:
            self._load_page(self.current_page + 1)

    # ========== Display ==========

    def _img_to_canvas(self, ix, iy):
        """Convert image coordinates to canvas coordinates."""
        if self.source_bin is None:
            return 0, 0
        h, w = self.source_bin.shape
        disp_w = int(w * self.zoom)
        disp_h = int(h * self.zoom)
        img_left = self.img_canvas_x - disp_w // 2
        img_top = self.img_canvas_y - disp_h // 2
        cx = img_left + ix * self.zoom
        cy = img_top + iy * self.zoom
        return cx, cy

    def _build_disp_base(self):
        """Build the base display image (cached)."""
        h, w = self.source_bin.shape
        if self.show_bg_var.get() and self.original_img is not None:
            bg = np.clip(self.original_img.astype(np.int16) + 100, 0, 255).astype(np.uint8)
            bg = np.maximum(bg, 200)
            disp = cv2.cvtColor(bg, cv2.COLOR_GRAY2BGR)
        else:
            disp = np.full((h, w, 3), 255, dtype=np.uint8)
        disp[self.work_img == 255] = [0, 0, 0]
        self._disp_cache = disp
        self._disp_cache_valid = True

    def _update_display(self, fast=False):
        if self.source_bin is None:
            return
        h, w = self.source_bin.shape

        if not self._disp_cache_valid or self._disp_cache is None:
            self._build_disp_base()

        disp = self._disp_cache.copy()

        # Draw stamps onto the image
        self._draw_stamps_on_img(disp)

        new_w = max(1, int(w * self.zoom))
        new_h = max(1, int(h * self.zoom))
        resized = cv2.resize(disp, (new_w, new_h), interpolation=cv2.INTER_NEAREST)

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

        # Draw arrow preview if placing
        self._draw_arrow_preview()

    def _update_erase_region(self, ix, iy, r):
        """Incrementally update the display cache in the erased region."""
        if self._disp_cache is None or not self._disp_cache_valid:
            return
        h, w = self.source_bin.shape
        y0 = max(0, iy - r)
        y1 = min(h, iy + r + 1)
        x0 = max(0, ix - r)
        x1 = min(w, ix + r + 1)
        # Update cache: erased pixels become white (background)
        if self.show_bg_var.get() and self.original_img is not None:
            bg_region = self.original_img[y0:y1, x0:x1].astype(np.int16)
            bg_region = np.clip(bg_region + 100, 0, 255).astype(np.uint8)
            bg_region = np.maximum(bg_region, 200)
            erased = self.erase_mask[y0:y1, x0:x1] & (self.source_bin[y0:y1, x0:x1] == 255)
            for c in range(3):
                ch = self._disp_cache[y0:y1, x0:x1, c]
                ch[erased] = bg_region[erased]
        else:
            erased = self.erase_mask[y0:y1, x0:x1] & (self.source_bin[y0:y1, x0:x1] == 255)
            self._disp_cache[y0:y1, x0:x1][erased] = [255, 255, 255]

    def _draw_stamps_on_img(self, disp):
        """Render all stamps onto the BGR display image."""
        for i, st in enumerate(self.stamps):
            # Selected stamp is highlighted in red
            if i == self.selected_idx:
                color = (0, 0, 255)  # BGR: red
            else:
                color = (0, 0, 0)  # BGR: black
            lw = max(1, int(self.stamp_size * 0.15))

            if st["type"] == "cross":
                cx, cy = int(st["x"]), int(st["y"])
                s = int(st["size"])
                cross_lw = max(2, int(st["size"] * 0.35))
                cv2.line(disp, (cx - s, cy - s), (cx + s, cy + s), color, cross_lw, cv2.LINE_AA)
                cv2.line(disp, (cx + s, cy - s), (cx - s, cy + s), color, cross_lw, cv2.LINE_AA)

            elif st["type"] == "number":
                cx, cy = int(st["x"]), int(st["y"])
                radius = int(st["size"])
                num = st["number"]
                cv2.circle(disp, (cx, cy), radius, color, lw, cv2.LINE_AA)
                text = str(num)
                font_scale = radius / 16.0
                thickness = max(1, lw)
                (tw, th), baseline = cv2.getTextSize(text, cv2.FONT_HERSHEY_SIMPLEX,
                                                      font_scale, thickness)
                tx = cx - tw // 2
                ty = cy + th // 2
                cv2.putText(disp, text, (tx, ty), cv2.FONT_HERSHEY_SIMPLEX,
                           font_scale, color, thickness, cv2.LINE_AA)

            elif st["type"] == "arrow":
                x1, y1 = int(st["x1"]), int(st["y1"])
                x2, y2 = int(st["x2"]), int(st["y2"])
                dx, dy = x2 - x1, y2 - y1
                length = math.sqrt(dx * dx + dy * dy)
                tip = min(0.3, 15.0 / length) if length > 1 else 0.3
                cv2.arrowedLine(disp, (x1, y1), (x2, y2), color, lw, cv2.LINE_AA, tipLength=tip)

    def _draw_arrow_preview(self):
        """Draw a temporary line from arrow start to current mouse position."""
        self.canvas.delete("arrow_preview")
        # Arrow start marker
        if self.mode == "arrow" and self.arrow_start is not None:
            ix, iy = self.arrow_start
            cx, cy = self._img_to_canvas(ix, iy)
            r = 4
            self.canvas.create_oval(cx - r, cy - r, cx + r, cy + r,
                                    fill="red", outline="red", tags="arrow_preview")

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

    # ========== Cursor Visualization ==========

    def _draw_cursor_rect(self, cx, cy):
        self.canvas.delete("cursor")
        half = self.pen_size * self.zoom / 2
        self.cursor_rect_id = self.canvas.create_rectangle(
            cx - half, cy - half, cx + half, cy + half,
            outline="red", width=1, dash=(3, 3), tags="cursor"
        )

    def _on_mouse_move(self, event):
        if self.mode == "pen":
            self._draw_cursor_rect(event.x, event.y)
        else:
            self.canvas.delete("cursor")
        # Arrow live preview line
        if self.mode == "arrow" and self.arrow_start is not None:
            self.canvas.delete("arrow_live")
            ix, iy = self.arrow_start
            cx, cy = self._img_to_canvas(ix, iy)
            self.canvas.create_line(cx, cy, event.x, event.y,
                                    fill="red", width=1, dash=(4, 4), tags="arrow_live")

    def _on_mouse_leave(self, event):
        self.canvas.delete("cursor")
        self.canvas.delete("arrow_live")

    # ========== Erase Operations ==========

    def _erase_at(self, cx, cy):
        ix, iy = self._canvas_to_img(cx, cy)
        if ix is None:
            return
        h, w = self.source_bin.shape
        r = self.pen_size // 2
        y0 = max(0, iy - r)
        y1 = min(h, iy + r + 1)
        x0 = max(0, ix - r)
        x1 = min(w, ix + r + 1)
        region_ink = self.source_bin[y0:y1, x0:x1] == 255
        self.erase_mask[y0:y1, x0:x1] |= region_ink
        self.work_img[y0:y1, x0:x1][region_ink & self.erase_mask[y0:y1, x0:x1]] = 0
        # Incrementally update display cache
        self._update_erase_region(ix, iy, r)

    def _erase_line(self, cx0, cy0, cx1, cy1):
        dist = max(abs(cx1 - cx0), abs(cy1 - cy0))
        steps = max(1, int(dist / (self.pen_size * self.zoom * 0.3)))
        for i in range(steps + 1):
            t = i / max(steps, 1)
            cx = cx0 + (cx1 - cx0) * t
            cy = cy0 + (cy1 - cy0) * t
            self._erase_at(cx, cy)

    def _rect_erase_outside(self, cx0, cy0, cx1, cy1):
        ix0, iy0 = self._canvas_to_img(min(cx0, cx1), min(cy0, cy1))
        ix1, iy1 = self._canvas_to_img(max(cx0, cx1), max(cy0, cy1))
        if ix0 is None or ix1 is None:
            self.status_var.set("範囲が画像外です")
            return
        h, w = self.source_bin.shape
        ix0, iy0 = max(0, ix0), max(0, iy0)
        ix1, iy1 = min(w, ix1), min(h, iy1)
        if ix1 - ix0 < 3 or iy1 - iy0 < 3:
            self.status_var.set("範囲が小さすぎます")
            return
        self._push_undo()
        outside = np.ones((h, w), dtype=bool)
        outside[iy0:iy1, ix0:ix1] = False
        ink_outside = (self.source_bin == 255) & outside
        self.erase_mask |= ink_outside
        self._rebuild_work_img()
        self._update_display()
        erased = int(np.sum(self.erase_mask))
        total_ink = int(np.sum(self.source_bin == 255))
        self.status_var.set(f"範囲外を消去 — 消去済み: {erased:,} / {total_ink:,} ピクセル")

    # ========== Stamp Operations ==========

    def _find_stamp_at(self, ix, iy):
        """Find the nearest stamp within grab distance. Returns index or -1."""
        best_idx = -1
        best_dist = float('inf')
        grab_r = max(20, self.stamp_size * 1.5)

        for i, st in enumerate(self.stamps):
            if st["type"] in ("cross", "number"):
                dx = ix - st["x"]
                dy = iy - st["y"]
                d = math.sqrt(dx * dx + dy * dy)
                if d < grab_r and d < best_dist:
                    best_dist = d
                    best_idx = i
            elif st["type"] == "arrow":
                # Check distance to start and end
                for px, py in [(st["x1"], st["y1"]), (st["x2"], st["y2"])]:
                    dx = ix - px
                    dy = iy - py
                    d = math.sqrt(dx * dx + dy * dy)
                    if d < grab_r and d < best_dist:
                        best_dist = d
                        best_idx = i
                # Check distance to midpoint
                mx = (st["x1"] + st["x2"]) / 2
                my = (st["y1"] + st["y2"]) / 2
                dx = ix - mx
                dy = iy - my
                d = math.sqrt(dx * dx + dy * dy)
                if d < grab_r and d < best_dist:
                    best_dist = d
                    best_idx = i
        return best_idx

    def _place_cross(self, cx, cy):
        ix, iy = self._canvas_to_img(cx, cy)
        if ix is None:
            return
        self._push_undo()
        self.stamps.append({"type": "cross", "x": ix, "y": iy, "size": self.stamp_size})
        self._update_display()
        self.status_var.set(f"×印を配置しました ({ix}, {iy})")

    def _place_number(self, cx, cy):
        ix, iy = self._canvas_to_img(cx, cy)
        if ix is None:
            return
        num = self.number_var.get()
        self._push_undo()
        number_size = max(12, self.stamp_size)
        self.stamps.append({"type": "number", "x": ix, "y": iy,
                            "size": number_size, "number": num})
        self._update_display()
        self.status_var.set(f"⓪{num} を配置しました ({ix}, {iy})")
        # Auto-increment number
        self.number_var.set(num + 1)

    def _place_arrow_click(self, cx, cy):
        ix, iy = self._canvas_to_img(cx, cy)
        if ix is None:
            return
        if self.arrow_start is None:
            # First click: set start
            self.arrow_start = (ix, iy)
            self.arrow_hint_var.set("← 終点をクリック")
            self._update_display()
            self.status_var.set("矢印の始点を設定しました。終点をクリックしてください")
        else:
            # Second click: place arrow
            x1, y1 = self.arrow_start
            self._push_undo()
            self.stamps.append({"type": "arrow", "x1": x1, "y1": y1, "x2": ix, "y2": iy})
            self.arrow_start = None
            self.arrow_hint_var.set("← 始点をクリック")
            self.canvas.delete("arrow_live")
            self._update_display()
            self.status_var.set(f"矢印を配置しました ({x1},{y1})→({ix},{iy})")

    def delete_selected_stamp(self):
        """Delete the selected stamp, or the last one if none selected."""
        if not self.stamps:
            self.status_var.set("図形がありません")
            return
        self._push_undo()
        if 0 <= self.selected_idx < len(self.stamps):
            removed = self.stamps.pop(self.selected_idx)
            self.selected_idx = -1
        else:
            removed = self.stamps.pop()
        self._disp_cache_valid = False
        self._update_display()
        self.status_var.set(f"{removed['type']}図形を削除しました")

    def delete_all_stamps(self):
        if not self.stamps:
            self.status_var.set("図形がありません")
            return
        self._push_undo()
        self.stamps.clear()
        self._update_display()
        self.status_var.set("全ての図形を削除しました")

    # ========== Mouse Handlers ==========

    def _on_left_press(self, event):
        if self.source_bin is None:
            return

        if self.mode == "pen":
            self.erasing = True
            self._push_undo()
            self.stroke_points = [(event.x, event.y)]
            # Ensure cache is ready before starting stroke
            if not self._disp_cache_valid or self._disp_cache is None:
                self._build_disp_base()
            self._erase_at(event.x, event.y)
            self._update_display(fast=True)
            self._draw_cursor_rect(event.x, event.y)

        elif self.mode == "rect":
            self.rect_start = (event.x, event.y)

        elif self.mode == "cross":
            self._place_cross(event.x, event.y)

        elif self.mode == "number":
            self._place_number(event.x, event.y)

        elif self.mode == "arrow":
            self._place_arrow_click(event.x, event.y)

        elif self.mode == "delete_stamp":
            ix, iy = self._canvas_to_img(event.x, event.y)
            if ix is None:
                return
            idx = self._find_stamp_at(ix, iy)
            if idx >= 0:
                self._push_undo()
                removed = self.stamps.pop(idx)
                self.selected_idx = -1
                self._disp_cache_valid = False
                self._update_display()
                self.status_var.set(f"{removed['type']}図形を削除しました")
            else:
                self.status_var.set("近くに図形がありません")

        elif self.mode == "move":
            ix, iy = self._canvas_to_img(event.x, event.y)
            if ix is None:
                return
            idx = self._find_stamp_at(ix, iy)
            if idx >= 0:
                self._push_undo()
                self.moving_idx = idx
                self.selected_idx = idx
                st = self.stamps[idx]
                if st["type"] in ("cross", "number"):
                    self.move_offset = (ix - st["x"], iy - st["y"])
                elif st["type"] == "arrow":
                    # Determine which end is closer to grab
                    d1 = math.hypot(ix - st["x1"], iy - st["y1"])
                    d2 = math.hypot(ix - st["x2"], iy - st["y2"])
                    mx = (st["x1"] + st["x2"]) / 2
                    my = (st["y1"] + st["y2"]) / 2
                    dm = math.hypot(ix - mx, iy - my)
                    if dm < d1 and dm < d2:
                        # Grab midpoint → move whole arrow
                        self.move_arrow_end = "both"
                        self.move_offset = (ix - mx, iy - my)
                    elif d1 < d2:
                        self.move_arrow_end = "start"
                        self.move_offset = (0, 0)
                    else:
                        self.move_arrow_end = "end"
                        self.move_offset = (0, 0)
                self.status_var.set(f"図形を移動中...")
            else:
                self.moving_idx = None
                self.selected_idx = -1
                self.status_var.set("近くに図形がありません")

    def _on_left_drag(self, event):
        if self.source_bin is None:
            return

        if self.mode == "pen":
            if not self.erasing:
                return
            if self.stroke_points:
                px, py = self.stroke_points[-1]
                self._erase_line(px, py, event.x, event.y)
            else:
                self._erase_at(event.x, event.y)
            self.stroke_points.append((event.x, event.y))
            # Throttle: skip display if too frequent
            now = time.time()
            if now - self._last_draw_time > 0.03:  # ~30fps max
                self._update_display(fast=True)
                self._draw_cursor_rect(event.x, event.y)
                self._last_draw_time = now

        elif self.mode == "rect":
            if self.rect_start is None:
                return
            if self.rect_id:
                self.canvas.delete(self.rect_id)
            x0, y0 = self.rect_start
            self.rect_id = self.canvas.create_rectangle(
                x0, y0, event.x, event.y,
                outline="blue", width=2, dash=(4, 4)
            )

        elif self.mode == "move":
            if self.moving_idx is None or self.moving_idx >= len(self.stamps):
                return
            ix, iy = self._canvas_to_img(event.x, event.y)
            if ix is None:
                return
            st = self.stamps[self.moving_idx]
            ox, oy = self.move_offset
            if st["type"] in ("cross", "number"):
                st["x"] = ix - ox
                st["y"] = iy - oy
            elif st["type"] == "arrow":
                if self.move_arrow_end == "start":
                    st["x1"] = ix
                    st["y1"] = iy
                elif self.move_arrow_end == "end":
                    st["x2"] = ix
                    st["y2"] = iy
                else:  # both
                    mx_new = ix - ox
                    my_new = iy - oy
                    mx_old = (st["x1"] + st["x2"]) / 2
                    my_old = (st["y1"] + st["y2"]) / 2
                    dx = mx_new - mx_old
                    dy = my_new - my_old
                    st["x1"] += dx
                    st["y1"] += dy
                    st["x2"] += dx
                    st["y2"] += dy
            self._update_display()

    def _on_left_release(self, event):
        if self.source_bin is None:
            return

        if self.mode == "pen":
            if self.erasing and self.stroke_points:
                px, py = self.stroke_points[-1]
                self._erase_line(px, py, event.x, event.y)
            self.erasing = False
            self.stroke_points = []
            # Final high-quality redraw
            self._update_display(fast=False)
            erased = int(np.sum(self.erase_mask))
            total_ink = int(np.sum(self.source_bin == 255))
            self.status_var.set(f"消去済み: {erased:,} / {total_ink:,} ピクセル")

        elif self.mode == "rect":
            if self.rect_id:
                self.canvas.delete(self.rect_id)
                self.rect_id = None
            if self.rect_start is None:
                return
            self._rect_erase_outside(self.rect_start[0], self.rect_start[1], event.x, event.y)
            self.rect_start = None

        elif self.mode == "move":
            if self.moving_idx is not None:
                self.status_var.set("図形を移動しました")
            self.moving_idx = None

    # ========== Pan (Right Click) ==========

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

    # ========== Scroll / Zoom ==========

    def _on_mousewheel(self, event):
        if event.state & 0x0004:
            if event.delta > 0:
                self.zoom_in()
            else:
                self.zoom_out()
        elif event.state & 0x0001:
            scroll = int(event.delta / 120) * 30
            self.pan_x += scroll
            self._update_display()
        else:
            scroll = int(event.delta / 120) * 30
            self.pan_y += scroll
            self._update_display()

    def _pan_by(self, dx, dy):
        self.pan_x += dx
        self.pan_y += dy
        self._update_display()

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

    # ========== Undo ==========

    def _push_undo(self):
        if len(self.undo_stack) >= self.max_undo:
            self.undo_stack.pop(0)
        import copy
        self.undo_stack.append({
            "erase_mask": self.erase_mask.copy(),
            "stamps": copy.deepcopy(self.stamps),
        })

    def undo(self):
        if not self.undo_stack:
            self.status_var.set("履歴がありません")
            return
        state = self.undo_stack.pop()
        self.erase_mask = state["erase_mask"]
        self.stamps = state["stamps"]
        self._rebuild_work_img()
        self._update_display()
        self.status_var.set("元に戻しました")

    def restore_all(self):
        if self.erase_mask is None:
            return
        self._push_undo()
        self.erase_mask[:] = False
        self._rebuild_work_img()
        self._update_display()
        self.status_var.set("全ての消去を復元しました")

    # ========== Save ==========

    def save_current(self):
        if self.work_img is None:
            self.status_var.set("保存する画像がありません")
            return
        path = filedialog.asksaveasfilename(
            title="画像を保存",
            defaultextension=".jpg",
            filetypes=[("JPEG files", "*.jpg"), ("PNG files", "*.png")],
            initialdir=r"C:\Users\sealake\Desktop\extracted_lines",
            initialfile=f"page_{self.current_page + 1:02d}.jpg"
        )
        if not path:
            return

        # Build output image
        h, w = self.work_img.shape
        output = np.full((h, w, 3), 255, dtype=np.uint8)
        output[self.work_img == 255] = [0, 0, 0]

        # Render stamps
        self._draw_stamps_on_img(output)

        # Convert BGR to single channel for save if no stamps, else save as color
        ext = os.path.splitext(path)[1].lower()
        if ext == '.png':
            success, buf = cv2.imencode('.png', output)
        else:
            success, buf = cv2.imencode('.jpg', output, [cv2.IMWRITE_JPEG_QUALITY, 95])
        if success:
            with open(path, 'wb') as f:
                f.write(buf)
            self.status_var.set(f"保存しました: {path}")


def main():
    root = tk.Tk()
    app = LineEraser(root)
    root.mainloop()


if __name__ == "__main__":
    main()

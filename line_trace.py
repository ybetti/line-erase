# -*- coding: utf-8 -*-
"""
Line-trace: PDF背景上にタッチペンで線を描き図形化するツール
- 部分描画: 1本ずつ描画
- 連続描画: 終点が次の始点になり連続して描き進める
- ドラッグで直線、フリーハンドで曲線
- 図形スタンプ: ×印、矢印、丸数字
"""

import tkinter as tk
from tkinter import filedialog, ttk, colorchooser
import cv2
import numpy as np
from PIL import Image, ImageTk
import pymupdf
import os
import math
import json


class LineTrace:
    def __init__(self, root):
        self.root = root
        self.root.title("Line-trace")
        self.root.geometry("1400x900")

        # PDF / background
        self.pdf_doc = None
        self.current_page = 0
        self.total_pages = 0
        self.pdf_path = None
        self.bg_gray = None
        self.bg_photo = None

        # View
        self.zoom = 1.0
        self.pan_x = 0
        self.pan_y = 0
        self.img_canvas_x = 0
        self.img_canvas_y = 0

        # Drawing state
        self.lines = []          # All items: lines, curves, stamps
        self.drawing = False
        self.start_img = None
        self.start_canvas = None
        self.preview_id = None
        self.continuous_start = None

        # Curve mode state
        self.curve_points = []
        self.curve_preview_ids = []
        self.curve_dot_ids = []

        # Endpoint move state
        self.move_line_idx = -1
        self.move_pt_idx = -1
        self.move_preview_id = None

        # Copy mode state
        self.copy_line_idx = -1
        self.copy_start = None

        # Item move state
        self.item_move_idx = -1
        self.item_move_last = None

        # Stamp state
        self.stamp_number = 1

        # Style
        self.line_color = "#000000"
        self.line_width = 3

        # Pan
        self.drag_start = None

        # Undo
        self.undo_stack = []
        self.max_undo = 30

        self._build_ui()
        self._bind_events()

    def _build_ui(self):
        toolbar_container = tk.Frame(self.root, bd=1, relief=tk.RAISED)
        toolbar_container.pack(side=tk.TOP, fill=tk.X)

        # === Row 1: File, Page, Line drawing modes, Confirm ===
        row1 = tk.Frame(toolbar_container)
        row1.pack(side=tk.TOP, fill=tk.X)

        tk.Button(row1, text="PDF開く", command=self.open_pdf, width=10).pack(side=tk.LEFT, padx=2, pady=2)

        tk.Label(row1, text="  ページ:").pack(side=tk.LEFT)
        self.page_var = tk.StringVar(value="0 / 0")
        tk.Label(row1, textvariable=self.page_var, width=10).pack(side=tk.LEFT)
        tk.Button(row1, text="◀", command=self.prev_page, width=3).pack(side=tk.LEFT)
        tk.Button(row1, text="▶", command=self.next_page, width=3).pack(side=tk.LEFT)

        ttk.Separator(row1, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

        tk.Label(row1, text="  線:").pack(side=tk.LEFT)
        self.mode_var = tk.StringVar(value="single")
        tk.Radiobutton(row1, text="部分描画", variable=self.mode_var, value="single",
                        command=self._mode_changed).pack(side=tk.LEFT, padx=2)
        tk.Radiobutton(row1, text="連続描画", variable=self.mode_var, value="continuous",
                        command=self._mode_changed).pack(side=tk.LEFT, padx=2)
        tk.Radiobutton(row1, text="曲線", variable=self.mode_var, value="curve",
                        command=self._mode_changed).pack(side=tk.LEFT, padx=2)

        ttk.Separator(row1, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

        confirm_frame = tk.Frame(row1, bd=1, relief=tk.SOLID)
        confirm_frame.pack(side=tk.LEFT, padx=4)
        tk.Button(confirm_frame, text="確定(Enter)", command=self._curve_finish, width=10).pack(padx=1, pady=1)

        # === Row 2: Stamps, Edit modes, Number selector ===
        row2 = tk.Frame(toolbar_container)
        row2.pack(side=tk.TOP, fill=tk.X)

        tk.Label(row2, text="  図形:").pack(side=tk.LEFT)
        tk.Radiobutton(row2, text="×印", variable=self.mode_var, value="cross",
                        command=self._mode_changed).pack(side=tk.LEFT, padx=2)
        tk.Radiobutton(row2, text="矢印", variable=self.mode_var, value="arrow",
                        command=self._mode_changed).pack(side=tk.LEFT, padx=2)
        tk.Radiobutton(row2, text="番号", variable=self.mode_var, value="number",
                        command=self._mode_changed).pack(side=tk.LEFT, padx=2)

        # Number selector (番号ボタンの隣)
        tk.Button(row2, text="▼", command=self._number_down, width=2).pack(side=tk.LEFT)
        self.number_var = tk.StringVar(value="1")
        tk.Label(row2, textvariable=self.number_var, width=3,
                 relief=tk.SUNKEN, anchor=tk.CENTER, font=("", 11, "bold")).pack(side=tk.LEFT, padx=2)
        tk.Button(row2, text="▲", command=self._number_up, width=2).pack(side=tk.LEFT)

        ttk.Separator(row2, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

        tk.Label(row2, text="  編集:").pack(side=tk.LEFT)
        tk.Radiobutton(row2, text="端点移動", variable=self.mode_var, value="move_endpoint",
                        command=self._mode_changed).pack(side=tk.LEFT, padx=2)
        tk.Radiobutton(row2, text="図形移動", variable=self.mode_var, value="move_item",
                        command=self._mode_changed).pack(side=tk.LEFT, padx=2)
        tk.Radiobutton(row2, text="コピー", variable=self.mode_var, value="copy",
                        command=self._mode_changed).pack(side=tk.LEFT, padx=2)
        tk.Radiobutton(row2, text="削除", variable=self.mode_var, value="delete",
                        command=self._mode_changed).pack(side=tk.LEFT, padx=2)

        # === Row 3: Constraints, Style, Actions, Zoom ===
        row3 = tk.Frame(toolbar_container)
        row3.pack(side=tk.TOP, fill=tk.X)

        # Constraint checkboxes
        tk.Label(row3, text="  制約:").pack(side=tk.LEFT)
        self.horizontal_var = tk.BooleanVar(value=False)
        self.vertical_var = tk.BooleanVar(value=False)
        tk.Checkbutton(row3, text="水平(0°)", variable=self.horizontal_var,
                        command=self._on_horizontal_changed).pack(side=tk.LEFT, padx=2)
        tk.Checkbutton(row3, text="垂直(90°)", variable=self.vertical_var,
                        command=self._on_vertical_changed).pack(side=tk.LEFT, padx=2)

        ttk.Separator(row3, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

        # Line width
        tk.Label(row3, text="  太さ:").pack(side=tk.LEFT)
        self.width_var = tk.IntVar(value=3)
        tk.Scale(row3, from_=1, to=5, orient=tk.HORIZONTAL, variable=self.width_var,
                 length=80, showvalue=True).pack(side=tk.LEFT, padx=2)

        # Color
        tk.Button(row3, text="色", command=self._pick_color, width=3).pack(side=tk.LEFT, padx=2)
        self.color_label = tk.Label(row3, text="  ■", fg="#000000", font=("", 14))
        self.color_label.pack(side=tk.LEFT)

        ttk.Separator(row3, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

        # Actions
        tk.Button(row3, text="一つ戻す", command=self.undo, width=8).pack(side=tk.LEFT, padx=2)
        tk.Button(row3, text="全消去", command=self.clear_all, width=6).pack(side=tk.LEFT, padx=2)
        tk.Button(row3, text="データ保存", command=self.save_data, width=8).pack(side=tk.LEFT, padx=2)
        tk.Button(row3, text="データ読込", command=self.load_data, width=8).pack(side=tk.LEFT, padx=2)
        tk.Button(row3, text="画像保存", command=self.save_current, width=8).pack(side=tk.LEFT, padx=2)

        ttk.Separator(row3, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

        # Zoom
        self.zoom_var = tk.StringVar(value="100%")
        tk.Label(row3, textvariable=self.zoom_var, width=5).pack(side=tk.LEFT)
        tk.Button(row3, text="−", command=self.zoom_out, width=2).pack(side=tk.LEFT)
        tk.Button(row3, text="+", command=self.zoom_in, width=2).pack(side=tk.LEFT)
        tk.Button(row3, text="全体", command=self.zoom_fit, width=4).pack(side=tk.LEFT, padx=2)

        # Pan direction buttons (cross layout, right-aligned, grid)
        pan_step = 80
        btn_w, btn_h = 3, 1
        pan_frame = tk.Frame(row3)
        pan_frame.pack(side=tk.RIGHT, padx=4)
        tk.Button(pan_frame, text="↑", width=btn_w, height=btn_h,
                  command=lambda: self._pan_by(0, pan_step)).grid(row=0, column=1)
        tk.Button(pan_frame, text="←", width=btn_w, height=btn_h,
                  command=lambda: self._pan_by(pan_step, 0)).grid(row=1, column=0)
        tk.Button(pan_frame, text="↓", width=btn_w, height=btn_h,
                  command=lambda: self._pan_by(0, -pan_step)).grid(row=1, column=1)
        tk.Button(pan_frame, text="→", width=btn_w, height=btn_h,
                  command=lambda: self._pan_by(-pan_step, 0)).grid(row=1, column=2)

        # Status
        status_bar = tk.Frame(self.root, bd=1, relief=tk.SUNKEN)
        status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        self.status_var = tk.StringVar(value="PDFファイルを開いてください")
        tk.Label(status_bar, textvariable=self.status_var, anchor=tk.W).pack(side=tk.LEFT, fill=tk.X, expand=True)
        tk.Label(status_bar, text="ホイール:上下  Shift+ホイール:左右  Ctrl+ホイール:ズーム  右クリック:一つ戻す",
                 fg="gray50", anchor=tk.E).pack(side=tk.RIGHT)

        # Canvas
        self.canvas = tk.Canvas(self.root, bg="#888888", cursor="crosshair")
        self.canvas.pack(fill=tk.BOTH, expand=True)

    def _bind_events(self):
        self.canvas.bind("<ButtonPress-1>", self._on_left_press)
        self.canvas.bind("<B1-Motion>", self._on_left_drag)
        self.canvas.bind("<ButtonRelease-1>", self._on_left_release)
        self.canvas.bind("<ButtonPress-3>", self._on_right_click)
        self.canvas.bind("<ButtonPress-2>", self._on_middle_press)
        self.canvas.bind("<B2-Motion>", self._on_middle_drag)
        self.canvas.bind("<ButtonRelease-2>", self._on_middle_release)
        self.canvas.bind("<MouseWheel>", self._on_mousewheel)
        self.canvas.bind("<Configure>", lambda e: self._update_display())
        self.root.bind("<Control-z>", lambda e: self.undo())
        self.root.bind("<Control-s>", lambda e: self.save_current())
        self.root.bind("<Escape>", lambda e: self._cancel_drawing())
        self.root.bind("<Return>", lambda e: self._curve_finish())
        self.root.bind("<Up>", lambda e: self._number_up())
        self.root.bind("<Down>", lambda e: self._number_down())

    def _mode_changed(self):
        self._cancel_drawing()
        mode = self.mode_var.get()
        if mode == "delete":
            self.canvas.config(cursor="X_cursor")
        elif mode in ("move_endpoint", "move_item"):
            self.canvas.config(cursor="fleur")
        elif mode == "copy":
            self.canvas.config(cursor="plus")
        elif mode in ("cross", "number"):
            self.canvas.config(cursor="tcross")
        else:
            self.canvas.config(cursor="crosshair")

    # ========== Number Controls ==========

    def _number_up(self):
        self.stamp_number = min(self.stamp_number + 1, 99)
        self.number_var.set(str(self.stamp_number))

    def _number_down(self):
        self.stamp_number = max(self.stamp_number - 1, 1)
        self.number_var.set(str(self.stamp_number))

    # ========== Constraint Controls ==========

    def _on_horizontal_changed(self):
        if self.horizontal_var.get():
            self.vertical_var.set(False)

    def _on_vertical_changed(self):
        if self.vertical_var.get():
            self.horizontal_var.set(False)

    def _constrain_point(self, ix0, iy0, ix_end, iy_end):
        """Constrain endpoint to horizontal (0 deg) or vertical (90 deg)."""
        if self.horizontal_var.get():
            return ix_end, iy0
        if self.vertical_var.get():
            return ix0, iy_end
        return ix_end, iy_end

    def _pick_color(self):
        color = colorchooser.askcolor(initialcolor=self.line_color, title="線の色")
        if color[1]:
            self.line_color = color[1]
            self.color_label.config(fg=self.line_color)

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
            self._load_image(path)
        else:
            self.pdf_doc = pymupdf.open(path)
            self.total_pages = len(self.pdf_doc)
            self.current_page = 0
            self._load_page(0)
        self.root.title(f"Line-trace - {os.path.basename(path)}")

    def _load_image(self, path):
        img = cv2.imdecode(np.fromfile(path, dtype=np.uint8), cv2.IMREAD_GRAYSCALE)
        if img is None:
            self.status_var.set("画像の読み込みに失敗しました")
            return
        self._setup_background(img)

    def _load_page(self, page_num):
        if not self.pdf_doc:
            return
        self.current_page = page_num
        page = self.pdf_doc[page_num]

        mat = pymupdf.Matrix(200 / 72, 200 / 72)
        pix = page.get_pixmap(matrix=mat)
        img_array = np.frombuffer(pix.samples, dtype=np.uint8).reshape(pix.h, pix.w, pix.n)
        if pix.n == 4:
            gray = cv2.cvtColor(img_array, cv2.COLOR_RGBA2GRAY)
        elif pix.n == 3:
            gray = cv2.cvtColor(img_array, cv2.COLOR_RGB2GRAY)
        else:
            gray = img_array
        self._setup_background(gray)

    def _setup_background(self, gray):
        self.bg_gray = np.clip(gray.astype(np.int16) + 80, 0, 255).astype(np.uint8)
        self.bg_gray = np.maximum(self.bg_gray, 180)

        self.lines.clear()
        self.undo_stack.clear()
        self._cancel_drawing()
        self.page_var.set(f"{self.current_page + 1} / {self.total_pages}")
        self.status_var.set("読み込み完了")
        self.zoom_fit()

    def _confirm_page_change(self):
        if not self.lines:
            return True
        from tkinter import messagebox
        return messagebox.askokcancel(
            "ページ移動",
            "描画した線が消えますが、よろしいですか？"
        )

    def prev_page(self):
        if self.pdf_doc and self.current_page > 0:
            if self._confirm_page_change():
                self._load_page(self.current_page - 1)

    def next_page(self):
        if self.pdf_doc and self.current_page < self.total_pages - 1:
            if self._confirm_page_change():
                self._load_page(self.current_page + 1)

    # ========== Display ==========

    def _update_display(self):
        if self.bg_gray is None:
            return
        h, w = self.bg_gray.shape

        new_w = max(1, int(w * self.zoom))
        new_h = max(1, int(h * self.zoom))

        if self.zoom < 1.0:
            resized = cv2.resize(self.bg_gray, (new_w, new_h), interpolation=cv2.INTER_AREA)
        else:
            resized = cv2.resize(self.bg_gray, (new_w, new_h), interpolation=cv2.INTER_LINEAR)

        pil_img = Image.fromarray(resized)
        self.bg_photo = ImageTk.PhotoImage(pil_img)

        self.canvas.delete("all")
        canvas_w = self.canvas.winfo_width()
        canvas_h = self.canvas.winfo_height()
        self.img_canvas_x = canvas_w // 2 + self.pan_x
        self.img_canvas_y = canvas_h // 2 + self.pan_y
        self.canvas.create_image(self.img_canvas_x, self.img_canvas_y,
                                 anchor=tk.CENTER, image=self.bg_photo, tags="bg")
        self.zoom_var.set(f"{int(self.zoom * 100)}%")

        for item in self.lines:
            self._draw_item_on_canvas(item)

        if self.continuous_start is not None:
            self._draw_start_marker()

    def _img_to_canvas(self, ix, iy):
        h, w = self.bg_gray.shape
        disp_w = int(w * self.zoom)
        disp_h = int(h * self.zoom)
        cx = self.img_canvas_x - disp_w // 2 + ix * self.zoom
        cy = self.img_canvas_y - disp_h // 2 + iy * self.zoom
        return cx, cy

    def _canvas_to_img(self, cx, cy):
        if self.bg_gray is None:
            return -1, -1
        h, w = self.bg_gray.shape
        disp_w = int(w * self.zoom)
        disp_h = int(h * self.zoom)
        img_left = self.img_canvas_x - disp_w // 2
        img_top = self.img_canvas_y - disp_h // 2
        ix = (cx - img_left) / self.zoom
        iy = (cy - img_top) / self.zoom
        if 0 <= ix < w and 0 <= iy < h:
            return ix, iy
        return -1, -1

    def _draw_start_marker(self):
        if self.continuous_start is None:
            return
        cx, cy = self._img_to_canvas(self.continuous_start[0], self.continuous_start[1])
        r = 5
        self.canvas.create_oval(
            cx - r, cy - r, cx + r, cy + r,
            fill="red", outline="red", tags="marker"
        )

    # ========== Draw items on canvas ==========

    def _draw_item_on_canvas(self, item):
        item_type = item["type"]
        if item_type == "cross":
            self._draw_cross_on_canvas(item)
        elif item_type == "arrow":
            self._draw_arrow_on_canvas(item)
        elif item_type == "number":
            self._draw_number_on_canvas(item)
        else:
            self._draw_line_on_canvas(item)

    def _draw_line_on_canvas(self, item):
        pts = item["points"]
        color = item.get("color", "#000000")
        width = item.get("width", 2)

        canvas_pts = []
        for p in pts:
            cx, cy = self._img_to_canvas(p[0], p[1])
            canvas_pts.extend([cx, cy])

        if len(canvas_pts) < 4:
            return

        cid = self.canvas.create_line(
            *canvas_pts, fill=color, width=width,
            capstyle=tk.ROUND, joinstyle=tk.ROUND, tags="drawn"
        )
        item["canvas_ids"] = [cid]

    def _draw_cross_on_canvas(self, item):
        cx, cy = item["points"][0]
        size = item.get("size", 12)
        color = item.get("color", "#000000")
        width = item.get("width", 2)

        ccx, ccy = self._img_to_canvas(cx, cy)
        s = size * self.zoom

        ids = []
        ids.append(self.canvas.create_line(
            ccx - s, ccy - s, ccx + s, ccy + s,
            fill=color, width=width, tags="drawn"
        ))
        ids.append(self.canvas.create_line(
            ccx + s, ccy - s, ccx - s, ccy + s,
            fill=color, width=width, tags="drawn"
        ))
        item["canvas_ids"] = ids

    def _draw_arrow_on_canvas(self, item):
        pts = item["points"]
        color = item.get("color", "#000000")
        width = item.get("width", 2)

        if len(pts) < 2:
            return

        cx1, cy1 = self._img_to_canvas(pts[0][0], pts[0][1])
        cx2, cy2 = self._img_to_canvas(pts[1][0], pts[1][1])

        cid = self.canvas.create_line(
            cx1, cy1, cx2, cy2,
            fill=color, width=width,
            arrow=tk.LAST, arrowshape=(12, 15, 5),
            tags="drawn"
        )
        item["canvas_ids"] = [cid]

    def _draw_number_on_canvas(self, item):
        cx, cy = item["points"][0]
        num = item.get("number", 1)
        size = item.get("size", 15)
        color = item.get("color", "#000000")
        width = item.get("width", 2)

        ccx, ccy = self._img_to_canvas(cx, cy)
        r = size * self.zoom

        ids = []
        ids.append(self.canvas.create_oval(
            ccx - r, ccy - r, ccx + r, ccy + r,
            outline=color, width=width, tags="drawn"
        ))
        font_size = max(8, int(r * 1.2))
        ids.append(self.canvas.create_text(
            ccx, ccy, text=str(num), fill=color,
            font=("Arial", font_size, "bold"), tags="drawn"
        ))
        item["canvas_ids"] = ids

    # ========== Endpoint Snapping ==========

    def _find_nearest_endpoint(self, ix, iy, snap_radius=10.0, exclude_line_idx=-1):
        best_dist = snap_radius
        best_pt = None
        for i, item in enumerate(self.lines):
            if i == exclude_line_idx:
                continue
            if item["type"] in ("cross", "number"):
                continue
            pts = item["points"]
            for ep in [pts[0], pts[-1]]:
                d = math.sqrt((ix - ep[0]) ** 2 + (iy - ep[1]) ** 2)
                if d < best_dist:
                    best_dist = d
                    best_pt = ep
        return best_pt

    # ========== Find Nearest Item (for move/delete) ==========

    def _find_nearest_item(self, ix, iy, radius=20.0):
        best_dist = radius
        best_idx = -1
        for i, item in enumerate(self.lines):
            if item["type"] in ("cross", "number"):
                px, py = item["points"][0]
                d = math.sqrt((ix - px) ** 2 + (iy - py) ** 2)
            else:
                pts = item["points"]
                d = float('inf')
                for j in range(len(pts) - 1):
                    d = min(d, self._point_to_segment_dist(ix, iy, pts[j], pts[j + 1]))
            if d < best_dist:
                best_dist = d
                best_idx = i
        return best_idx

    # ========== Mouse Handlers ==========

    def _on_left_press(self, event):
        mode = self.mode_var.get()

        if mode == "delete":
            self._delete_at(event.x, event.y)
            return

        if mode == "curve":
            self._curve_add_point(event.x, event.y)
            return

        if mode == "move_endpoint":
            self._move_start(event.x, event.y)
            return

        if mode == "copy":
            self._copy_start(event.x, event.y)
            return

        if mode == "move_item":
            self._item_move_start(event.x, event.y)
            return

        if mode == "cross":
            self._place_cross(event.x, event.y)
            return

        if mode == "number":
            self._place_number(event.x, event.y)
            return

        # Arrow mode: drag to draw
        if mode == "arrow":
            self.drawing = True
            ix, iy = self._canvas_to_img(event.x, event.y)
            if ix < 0:
                self.drawing = False
                return
            snap = self._find_nearest_endpoint(ix, iy)
            if snap:
                ix, iy = snap[0], snap[1]
            self.start_img = (ix, iy)
            self.start_canvas = self._img_to_canvas(ix, iy)
            return

        # Start drawing (single / continuous)
        self.drawing = True

        if mode == "continuous" and self.continuous_start is not None:
            self.start_img = self.continuous_start
            self.start_canvas = self._img_to_canvas(self.start_img[0], self.start_img[1])
            self.start_canvas = (self.start_canvas[0], self.start_canvas[1])
        else:
            ix, iy = self._canvas_to_img(event.x, event.y)
            if ix < 0:
                self.drawing = False
                return
            snap = self._find_nearest_endpoint(ix, iy)
            if snap:
                ix, iy = snap[0], snap[1]
            self.start_img = (ix, iy)
            self.start_canvas = self._img_to_canvas(ix, iy)

    def _on_left_drag(self, event):
        mode = self.mode_var.get()
        if mode == "move_endpoint" and self.move_line_idx >= 0:
            self._move_drag(event.x, event.y)
            return
        if mode == "copy" and self.copy_line_idx >= 0:
            self._copy_drag(event.x, event.y)
            return
        if mode == "move_item" and self.item_move_idx >= 0:
            self._item_move_drag(event.x, event.y)
            return
        if not self.drawing:
            return
        if self.preview_id:
            self.canvas.delete(self.preview_id)

        if mode == "arrow":
            self.preview_id = self.canvas.create_line(
                self.start_canvas[0], self.start_canvas[1],
                event.x, event.y,
                fill=self.line_color, width=self.width_var.get(),
                arrow=tk.LAST, arrowshape=(12, 15, 5),
                dash=(4, 4), tags="preview"
            )
            return

        # Apply parallel/perpendicular constraint to preview
        end_cx, end_cy = event.x, event.y
        if self.horizontal_var.get() or self.vertical_var.get():
            ix_end, iy_end = self._canvas_to_img(event.x, event.y)
            if ix_end >= 0 and self.start_img is not None:
                ix0, iy0 = self.start_img
                cix, ciy = self._constrain_point(ix0, iy0, ix_end, iy_end)
                end_cx, end_cy = self._img_to_canvas(cix, ciy)

        self.preview_id = self.canvas.create_line(
            self.start_canvas[0], self.start_canvas[1],
            end_cx, end_cy,
            fill=self.line_color, width=self.width_var.get(),
            dash=(4, 4), tags="preview"
        )

    def _on_left_release(self, event):
        mode = self.mode_var.get()
        if mode == "copy" and self.copy_line_idx >= 0:
            self._copy_end(event.x, event.y)
            return
        if mode == "move_endpoint" and self.move_line_idx >= 0:
            self._move_end(event.x, event.y)
            return
        if mode == "move_item" and self.item_move_idx >= 0:
            self._item_move_end(event.x, event.y)
            return
        if not self.drawing:
            return
        self.drawing = False

        if self.preview_id:
            self.canvas.delete(self.preview_id)
            self.preview_id = None

        ix_end, iy_end = self._canvas_to_img(event.x, event.y)
        if ix_end < 0:
            return

        ix0, iy0 = self.start_img

        if mode == "arrow":
            dist = math.sqrt((ix_end - ix0) ** 2 + (iy_end - iy0) ** 2)
            if dist < 2:
                return
            self._push_undo()
            item = {
                "type": "arrow",
                "points": [(ix0, iy0), (ix_end, iy_end)],
                "color": self.line_color,
                "width": self.width_var.get(),
                "canvas_ids": []
            }
            self.lines.append(item)
            self._draw_item_on_canvas(item)
            self.status_var.set(f"矢印を追加 ({len(self.lines)}個)")
            return

        # Apply parallel/perpendicular constraint before snap
        if self.horizontal_var.get() or self.vertical_var.get():
            ix_end, iy_end = self._constrain_point(ix0, iy0, ix_end, iy_end)

        # Snap end point to nearest endpoint
        snap = self._find_nearest_endpoint(ix_end, iy_end)
        if snap:
            ix_end, iy_end = snap[0], snap[1]

        dist = math.sqrt((ix_end - ix0) ** 2 + (iy_end - iy0) ** 2)
        if dist < 2:
            return

        self._push_undo()
        line = {
            "type": "straight",
            "points": [(ix0, iy0), (ix_end, iy_end)],
            "color": self.line_color,
            "width": self.width_var.get(),
            "canvas_ids": []
        }
        self.lines.append(line)
        self._draw_item_on_canvas(line)
        end_pt = (ix_end, iy_end)
        self.status_var.set(f"直線を追加 ({len(self.lines)}個)")

        if mode == "continuous":
            self.continuous_start = end_pt
            self.canvas.delete("marker")
            self._draw_start_marker()
        else:
            self.continuous_start = None

    # ========== Stamp Placement ==========

    def _place_cross(self, cx, cy):
        ix, iy = self._canvas_to_img(cx, cy)
        if ix < 0:
            return
        self._push_undo()
        item = {
            "type": "cross",
            "points": [(ix, iy)],
            "size": 12,
            "color": self.line_color,
            "width": self.width_var.get(),
            "canvas_ids": []
        }
        self.lines.append(item)
        self._draw_item_on_canvas(item)
        self.status_var.set(f"×印を配置 ({len(self.lines)}個)")

    def _place_number(self, cx, cy):
        ix, iy = self._canvas_to_img(cx, cy)
        if ix < 0:
            return
        self._push_undo()
        item = {
            "type": "number",
            "points": [(ix, iy)],
            "number": self.stamp_number,
            "size": 15,
            "color": self.line_color,
            "width": self.width_var.get(),
            "canvas_ids": []
        }
        self.lines.append(item)
        self._draw_item_on_canvas(item)
        self.status_var.set(f"番号 {self.stamp_number} を配置 ({len(self.lines)}個)")

    # ========== Endpoint Move ==========

    def _find_nearest_endpoint_with_info(self, ix, iy, radius=15.0):
        best_dist = radius
        best_line = -1
        best_pt = -1
        for i, item in enumerate(self.lines):
            if item["type"] in ("cross", "number"):
                continue
            pts = item["points"]
            d = math.sqrt((ix - pts[0][0]) ** 2 + (iy - pts[0][1]) ** 2)
            if d < best_dist:
                best_dist = d
                best_line = i
                best_pt = 0
            d = math.sqrt((ix - pts[-1][0]) ** 2 + (iy - pts[-1][1]) ** 2)
            if d < best_dist:
                best_dist = d
                best_line = i
                best_pt = len(pts) - 1
        return best_line, best_pt, best_dist

    def _move_start(self, cx, cy):
        ix, iy = self._canvas_to_img(cx, cy)
        if ix < 0:
            return
        line_idx, pt_idx, dist = self._find_nearest_endpoint_with_info(ix, iy)
        if line_idx < 0:
            self.status_var.set("近くに端点がありません")
            return
        self._push_undo()
        self.move_line_idx = line_idx
        self.move_pt_idx = pt_idx

    def _move_drag(self, cx, cy):
        ix, iy = self._canvas_to_img(cx, cy)
        if ix < 0:
            return
        item = self.lines[self.move_line_idx]
        pts = list(item["points"])
        pts[self.move_pt_idx] = (ix, iy)
        item["points"] = pts
        for cid in item.get("canvas_ids", []):
            self.canvas.delete(cid)
        self._draw_item_on_canvas(item)

    def _move_end(self, cx, cy):
        ix, iy = self._canvas_to_img(cx, cy)
        if ix >= 0:
            snap = self._find_nearest_endpoint(ix, iy, exclude_line_idx=self.move_line_idx)
            if snap:
                ix, iy = snap[0], snap[1]
            item = self.lines[self.move_line_idx]
            pts = list(item["points"])
            pts[self.move_pt_idx] = (ix, iy)
            item["points"] = pts
            for cid in item.get("canvas_ids", []):
                self.canvas.delete(cid)
            self._draw_item_on_canvas(item)
        self.move_line_idx = -1
        self.move_pt_idx = -1
        self.status_var.set("端点を移動しました")

    # ========== Item Move (whole object) ==========

    def _item_move_start(self, cx, cy):
        ix, iy = self._canvas_to_img(cx, cy)
        if ix < 0:
            return
        idx = self._find_nearest_item(ix, iy)
        if idx < 0:
            self.status_var.set("近くに図形がありません")
            return
        self._push_undo()
        self.item_move_idx = idx
        self.item_move_last = (ix, iy)

    def _item_move_drag(self, cx, cy):
        ix, iy = self._canvas_to_img(cx, cy)
        if ix < 0 or self.item_move_last is None:
            return
        dx = ix - self.item_move_last[0]
        dy = iy - self.item_move_last[1]
        self.item_move_last = (ix, iy)

        item = self.lines[self.item_move_idx]
        item["points"] = [(p[0] + dx, p[1] + dy) for p in item["points"]]
        for cid in item.get("canvas_ids", []):
            self.canvas.delete(cid)
        self._draw_item_on_canvas(item)

    def _item_move_end(self, cx, cy):
        if self.item_move_idx >= 0:
            ix, iy = self._canvas_to_img(cx, cy)
            if ix >= 0 and self.item_move_last is not None:
                dx = ix - self.item_move_last[0]
                dy = iy - self.item_move_last[1]
                item = self.lines[self.item_move_idx]
                item["points"] = [(p[0] + dx, p[1] + dy) for p in item["points"]]
                for cid in item.get("canvas_ids", []):
                    self.canvas.delete(cid)
                self._draw_item_on_canvas(item)
        self.item_move_idx = -1
        self.item_move_last = None
        self.status_var.set("図形を移動しました")

    # ========== Copy Mode ==========

    def _find_nearest_line(self, ix, iy, radius=15.0):
        return self._find_nearest_item(ix, iy, radius)

    def _copy_start(self, cx, cy):
        ix, iy = self._canvas_to_img(cx, cy)
        if ix < 0:
            return
        idx = self._find_nearest_item(ix, iy)
        if idx < 0:
            self.status_var.set("近くに図形がありません")
            return
        self.copy_line_idx = idx
        self.copy_start_pos = (cx, cy)
        self.status_var.set("ドラッグでオフセット方向を指定してください")

    def _copy_drag(self, cx, cy):
        if self.preview_id:
            self.canvas.delete(self.preview_id)
            self.preview_id = None
        self.canvas.delete("copy_preview")

        dx_canvas = cx - self.copy_start_pos[0]
        dy_canvas = cy - self.copy_start_pos[1]
        dx_img = dx_canvas / self.zoom
        dy_img = dy_canvas / self.zoom

        item = self.lines[self.copy_line_idx]
        pts = item["points"]
        item_type = item["type"]

        if item_type in ("cross", "number"):
            px, py = pts[0]
            ccx, ccy = self._img_to_canvas(px + dx_img, py + dy_img)
            s = item.get("size", 12) * self.zoom
            color = item.get("color", "#000000")
            width = item.get("width", 2)
            if item_type == "cross":
                self.canvas.create_line(
                    ccx - s, ccy - s, ccx + s, ccy + s,
                    fill=color, width=width, dash=(4, 4), tags="copy_preview"
                )
                self.canvas.create_line(
                    ccx + s, ccy - s, ccx - s, ccy + s,
                    fill=color, width=width, dash=(4, 4), tags="copy_preview"
                )
            else:
                r = s
                self.canvas.create_oval(
                    ccx - r, ccy - r, ccx + r, ccy + r,
                    outline=color, width=width, dash=(4, 4), tags="copy_preview"
                )
                font_size = max(8, int(r * 1.2))
                self.canvas.create_text(
                    ccx, ccy, text=str(item.get("number", 1)), fill=color,
                    font=("Arial", font_size, "bold"), tags="copy_preview"
                )
        else:
            canvas_pts = []
            for p in pts:
                pcx, pcy = self._img_to_canvas(p[0] + dx_img, p[1] + dy_img)
                canvas_pts.extend([pcx, pcy])
            if len(canvas_pts) >= 4:
                is_curve = item_type == "curve"
                arrow_opt = tk.LAST if item_type == "arrow" else tk.NONE
                self.canvas.create_line(
                    *canvas_pts, fill=item.get("color", "#000000"),
                    width=item.get("width", 3), dash=(4, 4),
                    smooth=is_curve, splinesteps=36 if is_curve else 0,
                    arrow=arrow_opt,
                    arrowshape=(12, 15, 5) if item_type == "arrow" else (),
                    tags="copy_preview"
                )

    def _copy_end(self, cx, cy):
        self.canvas.delete("copy_preview")

        dx_canvas = cx - self.copy_start_pos[0]
        dy_canvas = cy - self.copy_start_pos[1]
        dx_img = dx_canvas / self.zoom
        dy_img = dy_canvas / self.zoom

        if abs(dx_img) < 1 and abs(dy_img) < 1:
            self.copy_line_idx = -1
            return

        self._push_undo()
        src = self.lines[self.copy_line_idx]
        new_pts = [(p[0] + dx_img, p[1] + dy_img) for p in src["points"]]
        new_item = {
            "type": src["type"],
            "points": new_pts,
            "color": src["color"],
            "width": src["width"],
            "canvas_ids": []
        }
        if "size" in src:
            new_item["size"] = src["size"]
        if "number" in src:
            new_item["number"] = src["number"]
        self.lines.append(new_item)
        self._draw_item_on_canvas(new_item)
        self.copy_line_idx = -1
        self.status_var.set(f"コピーしました ({len(self.lines)}個)")

    # ========== Right click = undo ==========

    def _on_right_click(self, event):
        self.undo()

    # ========== Middle click = pan ==========

    def _on_middle_press(self, event):
        self.drag_start = (event.x, event.y)

    def _on_middle_drag(self, event):
        if self.drag_start:
            dx = event.x - self.drag_start[0]
            dy = event.y - self.drag_start[1]
            self.pan_x += dx
            self.pan_y += dy
            self.drag_start = (event.x, event.y)
            self._update_display()

    def _on_middle_release(self, event):
        self.drag_start = None

    def _pan_by(self, dx, dy):
        self.pan_x += dx
        self.pan_y += dy
        self._update_display()

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

    def _cancel_drawing(self):
        self.drawing = False
        if self.preview_id:
            self.canvas.delete(self.preview_id)
            self.preview_id = None
        self.continuous_start = None
        self.canvas.delete("marker")
        self.item_move_idx = -1
        self.item_move_last = None
        for cid in self.curve_preview_ids:
            self.canvas.delete(cid)
        for cid in self.curve_dot_ids:
            self.canvas.delete(cid)
        self.curve_preview_ids = []
        self.curve_dot_ids = []
        self.curve_points = []

    # ========== Curve Mode ==========

    def _curve_add_point(self, cx, cy):
        ix, iy = self._canvas_to_img(cx, cy)
        if ix < 0:
            return

        snap = self._find_nearest_endpoint(ix, iy)
        if snap:
            ix, iy = snap[0], snap[1]

        self.curve_points.append((ix, iy))

        ccx, ccy = self._img_to_canvas(ix, iy)
        r = 4
        dot = self.canvas.create_oval(ccx - r, ccy - r, ccx + r, ccy + r,
                                       fill="blue", outline="blue", tags="curve_edit")
        self.curve_dot_ids.append(dot)

        self._update_curve_preview()

        if len(self.curve_points) == 1:
            self.status_var.set("曲線: 制御点をクリックで追加、Enterで確定")

    def _catmull_rom(self, points, num_per_seg=20):
        if len(points) < 2:
            return list(points)
        if len(points) == 2:
            return list(points)

        pts = [points[0]] + list(points) + [points[-1]]
        result = []
        for i in range(1, len(pts) - 2):
            p0 = pts[i - 1]
            p1 = pts[i]
            p2 = pts[i + 1]
            p3 = pts[i + 2]
            for t_i in range(num_per_seg):
                t = t_i / num_per_seg
                t2 = t * t
                t3 = t2 * t
                x = 0.5 * ((2 * p1[0]) +
                            (-p0[0] + p2[0]) * t +
                            (2 * p0[0] - 5 * p1[0] + 4 * p2[0] - p3[0]) * t2 +
                            (-p0[0] + 3 * p1[0] - 3 * p2[0] + p3[0]) * t3)
                y = 0.5 * ((2 * p1[1]) +
                            (-p0[1] + p2[1]) * t +
                            (2 * p0[1] - 5 * p1[1] + 4 * p2[1] - p3[1]) * t2 +
                            (-p0[1] + 3 * p1[1] - 3 * p2[1] + p3[1]) * t3)
                result.append((x, y))
        result.append(points[-1])
        return result

    def _update_curve_preview(self):
        for cid in self.curve_preview_ids:
            self.canvas.delete(cid)
        self.curve_preview_ids = []

        if len(self.curve_points) < 2:
            return

        smooth_pts = self._catmull_rom(self.curve_points)
        canvas_pts = []
        for p in smooth_pts:
            cx, cy = self._img_to_canvas(p[0], p[1])
            canvas_pts.extend([cx, cy])

        if len(canvas_pts) < 4:
            return

        cid = self.canvas.create_line(
            *canvas_pts, fill=self.line_color, width=self.width_var.get(),
            dash=(6, 3), capstyle=tk.ROUND, tags="curve_edit"
        )
        self.curve_preview_ids.append(cid)

    def _curve_finish(self):
        if len(self.curve_points) < 2:
            self._cancel_drawing()
            return

        for cid in self.curve_preview_ids:
            self.canvas.delete(cid)
        for cid in self.curve_dot_ids:
            self.canvas.delete(cid)
        self.curve_preview_ids = []
        self.curve_dot_ids = []

        smooth_pts = self._catmull_rom(self.curve_points)

        self._push_undo()
        item = {
            "type": "curve",
            "points": smooth_pts,
            "color": self.line_color,
            "width": self.width_var.get(),
            "canvas_ids": []
        }
        self.lines.append(item)
        self._draw_item_on_canvas(item)
        self.status_var.set(f"曲線を追加 ({len(self.lines)}個)")
        self.curve_points = []

    # ========== Delete ==========

    def _delete_at(self, cx, cy):
        ix, iy = self._canvas_to_img(cx, cy)
        if ix < 0:
            return

        best_idx = self._find_nearest_item(ix, iy)

        if best_idx >= 0:
            self._push_undo()
            item = self.lines.pop(best_idx)
            for cid in item.get("canvas_ids", []):
                self.canvas.delete(cid)
            self.status_var.set(f"削除しました ({len(self.lines)}個)")

    def _point_to_segment_dist(self, px, py, p1, p2):
        x1, y1 = p1
        x2, y2 = p2
        dx = x2 - x1
        dy = y2 - y1
        length_sq = dx * dx + dy * dy
        if length_sq < 1e-6:
            return math.sqrt((px - x1) ** 2 + (py - y1) ** 2)
        t = max(0, min(1, ((px - x1) * dx + (py - y1) * dy) / length_sq))
        proj_x = x1 + t * dx
        proj_y = y1 + t * dy
        return math.sqrt((px - proj_x) ** 2 + (py - proj_y) ** 2)

    # ========== Undo ==========

    def _push_undo(self):
        if len(self.undo_stack) >= self.max_undo:
            self.undo_stack.pop(0)
        saved = []
        for item in self.lines:
            entry = {
                "type": item["type"],
                "points": list(item["points"]),
                "color": item["color"],
                "width": item["width"],
                "canvas_ids": []
            }
            if "size" in item:
                entry["size"] = item["size"]
            if "number" in item:
                entry["number"] = item["number"]
            saved.append(entry)
        self.undo_stack.append(saved)

    def undo(self):
        if not self.undo_stack:
            self.status_var.set("履歴がありません")
            return
        for item in self.lines:
            for cid in item.get("canvas_ids", []):
                self.canvas.delete(cid)
        self.lines = self.undo_stack.pop()
        for item in self.lines:
            self._draw_item_on_canvas(item)
        self.status_var.set("元に戻しました")

    def clear_all(self):
        if not self.lines:
            return
        self._push_undo()
        for item in self.lines:
            for cid in item.get("canvas_ids", []):
                self.canvas.delete(cid)
        self.lines.clear()
        self._cancel_drawing()
        self.status_var.set("全消去しました")

    # ========== Zoom ==========

    def zoom_in(self):
        self.zoom = min(self.zoom * 1.25, 10.0)
        self._update_display()

    def zoom_out(self):
        self.zoom = max(self.zoom / 1.25, 0.05)
        self._update_display()

    def zoom_fit(self):
        if self.bg_gray is None:
            return
        h, w = self.bg_gray.shape
        canvas_w = max(self.canvas.winfo_width(), 100)
        canvas_h = max(self.canvas.winfo_height(), 100)
        self.zoom = min(canvas_w / w, canvas_h / h) * 0.95
        self.pan_x = 0
        self.pan_y = 0
        self._update_display()

    # ========== Save Image ==========

    def save_current(self):
        if self.bg_gray is None:
            self.status_var.set("保存する画像がありません")
            return
        path = filedialog.asksaveasfilename(
            title="画像を保存",
            defaultextension=".jpg",
            filetypes=[("JPEG files", "*.jpg"), ("PNG files", "*.png")],
            initialdir=r"C:\Users\sealake\Desktop\extracted_lines",
            initialfile=f"trace_{self.current_page + 1:02d}.jpg"
        )
        if not path:
            return

        h, w = self.bg_gray.shape
        output = np.full((h, w, 3), 255, dtype=np.uint8)

        for item in self.lines:
            hex_color = item.get("color", "#000000").lstrip("#")
            cr, cg, cb = int(hex_color[0:2], 16), int(hex_color[2:4], 16), int(hex_color[4:6], 16)
            bgr = (cb, cg, cr)
            lw = item.get("width", 2)
            item_type = item["type"]

            if item_type in ("straight", "curve"):
                int_pts = [(int(round(p[0])), int(round(p[1]))) for p in item["points"]]
                for j in range(len(int_pts) - 1):
                    cv2.line(output, int_pts[j], int_pts[j + 1], bgr, lw, cv2.LINE_AA)

            elif item_type == "arrow":
                pts = item["points"]
                pt1 = (int(round(pts[0][0])), int(round(pts[0][1])))
                pt2 = (int(round(pts[1][0])), int(round(pts[1][1])))
                dx = pts[1][0] - pts[0][0]
                dy = pts[1][1] - pts[0][1]
                length = math.sqrt(dx * dx + dy * dy)
                tip = min(0.3, 15.0 / length) if length > 0 else 0.3
                cv2.arrowedLine(output, pt1, pt2, bgr, lw, cv2.LINE_AA, tipLength=tip)

            elif item_type == "cross":
                cx, cy = item["points"][0]
                size = item.get("size", 12)
                icx, icy = int(round(cx)), int(round(cy))
                s = int(round(size))
                cv2.line(output, (icx - s, icy - s), (icx + s, icy + s), bgr, lw, cv2.LINE_AA)
                cv2.line(output, (icx + s, icy - s), (icx - s, icy + s), bgr, lw, cv2.LINE_AA)

            elif item_type == "number":
                cx, cy = item["points"][0]
                num = item.get("number", 1)
                size = item.get("size", 15)
                icx, icy = int(round(cx)), int(round(cy))
                radius = int(round(size))
                cv2.circle(output, (icx, icy), radius, bgr, lw, cv2.LINE_AA)
                text = str(num)
                font_scale = size / 20.0
                thickness = max(1, lw)
                (tw, th), _ = cv2.getTextSize(text, cv2.FONT_HERSHEY_SIMPLEX, font_scale, thickness)
                tx = icx - tw // 2
                ty = icy + th // 2
                cv2.putText(output, text, (tx, ty), cv2.FONT_HERSHEY_SIMPLEX,
                            font_scale, bgr, thickness, cv2.LINE_AA)

        ext = os.path.splitext(path)[1].lower()
        if ext == ".png":
            success, buf = cv2.imencode('.png', output)
        else:
            success, buf = cv2.imencode('.jpg', output, [cv2.IMWRITE_JPEG_QUALITY, 95])
        if success:
            with open(path, 'wb') as f:
                f.write(buf)
            self.status_var.set(f"保存しました: {path}")

    # ========== Data Save/Load ==========

    def save_data(self):
        if not self.lines:
            self.status_var.set("保存するデータがありません")
            return
        path = filedialog.asksaveasfilename(
            title="描画データを保存",
            defaultextension=".json",
            filetypes=[("JSON files", "*.json")],
            initialdir=r"C:\Users\sealake\Desktop\extracted_lines",
            initialfile=f"trace_{self.current_page + 1:02d}.json"
        )
        if not path:
            return
        data = {
            "pdf_path": self.pdf_path,
            "page": self.current_page,
            "lines": []
        }
        for item in self.lines:
            entry = {
                "type": item["type"],
                "points": [[p[0], p[1]] for p in item["points"]],
                "color": item.get("color", "#000000"),
                "width": item.get("width", 3)
            }
            if "size" in item:
                entry["size"] = item["size"]
            if "number" in item:
                entry["number"] = item["number"]
            data["lines"].append(entry)
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        self.status_var.set(f"データを保存しました: {path}")

    def load_data(self):
        path = filedialog.askopenfilename(
            title="描画データを読み込み",
            filetypes=[("JSON files", "*.json")],
            initialdir=r"C:\Users\sealake\Desktop\extracted_lines"
        )
        if not path:
            return
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)

        self._push_undo()
        loaded = []
        for ld in data.get("lines", []):
            item = {
                "type": ld["type"],
                "points": [(p[0], p[1]) for p in ld["points"]],
                "color": ld.get("color", "#000000"),
                "width": ld.get("width", 3),
                "canvas_ids": []
            }
            if "size" in ld:
                item["size"] = ld["size"]
            if "number" in ld:
                item["number"] = ld["number"]
            loaded.append(item)

        self.lines.extend(loaded)
        for item in loaded:
            self._draw_item_on_canvas(item)
        self.status_var.set(f"{len(loaded)}個の要素を読み込みました")


def main():
    root = tk.Tk()
    app = LineTrace(root)
    root.mainloop()


if __name__ == "__main__":
    main()

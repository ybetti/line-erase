# -*- coding: utf-8 -*-
"""
OpenCV morphological skeleton (超高速版)
"""
import cv2
import numpy as np


def skeletonize(binary):
    """
    Fast morphological skeleton using OpenCV.
    May produce 2px wide lines in places, but very fast.
    Input: binary image (uint8, 255 or bool = foreground)
    Output: skeleton (uint8, 0 or 1)
    """
    img = (binary > 0).astype(np.uint8) * 255
    skel = np.zeros_like(img)
    element = cv2.getStructuringElement(cv2.MORPH_CROSS, (3, 3))
    while True:
        opened = cv2.morphologyEx(img, cv2.MORPH_OPEN, element)
        temp = cv2.subtract(img, opened)
        skel = cv2.bitwise_or(skel, temp)
        img = cv2.erode(img, element)
        if cv2.countNonZero(img) == 0:
            break
    return (skel > 0).astype(np.uint8)

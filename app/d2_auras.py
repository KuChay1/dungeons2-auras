"""Dungeons II Auras - WeakAuras-style cooldown tracker for Minecraft Dungeons II.

Reads cooldowns straight off the game's hotbar (screen pixels only, nothing is
injected into the game) and draws WoW-style icon auras: clock swipe, big
countdown numbers, desaturated icon while on cooldown, golden proc glow when
an ability comes back.

Hotkeys (global, polled):
  F8               lock / unlock (unlocked = drag the auras with the mouse)
  Ctrl+Shift+F8    quit
"""
import ctypes
import ctypes.wintypes as wt
import json
import math
import os
import sys
import time

import numpy as np
import random
import threading

try:
    import d2_mem  # read-only game memory: exact buff and cooldown timers
except Exception:  # pragma: no cover
    d2_mem = None
from PIL import Image, ImageChops, ImageDraw, ImageFilter, ImageFont, ImageGrab, ImageOps

HERE = os.path.dirname(os.path.abspath(__file__))
CONFIG_PATH = os.path.join(HERE, "config.json")
GAME_EXE = "dungeons-win64-shipping.exe"
DEBUG = "--debug" in sys.argv

# --------------------------------------------------------------------------
# Hotbar geometry, measured at 2560x1440. UI is anchored bottom-centre and
# scales with screen height, so these are remapped for other resolutions.
# Each slot: inner rect (x0, y0, x1, y1) the cooldown line sweeps through,
# detect span (dx0, dx1) that avoids the keybind badge, icon crop rect.
# --------------------------------------------------------------------------
REF_W, REF_H = 2560, 1440
OX, OY = 720, 1142  # origin of the hotbar crop the numbers were measured in
SLOTS = [
    {"key": "potion", "label": "E", "rect": (22, 158, 86, 244), "detect": (24, 84), "icon": (22, 170, 86, 234)},
    {"key": "slot1", "label": "1", "rect": (381, 87, 474, 179), "detect": (385, 458), "icon": (394, 88, 458, 152)},
    {"key": "slot2", "label": "2", "rect": (517, 87, 610, 179), "detect": (521, 594), "icon": (530, 88, 594, 152)},
    {"key": "slot3", "label": "3", "rect": (653, 87, 746, 179), "detect": (657, 730), "icon": (666, 88, 730, 152)},
]
# HUD Size "Small" doesn't shrink everything by the same factor (text stays bigger), so a
# few rects differ there. Keyed by slot; merged over SLOTS when the detected scale is small.
SMALL_HUD = 0.85
SLOTS_SMALL = {
    "potion": {"rect": (40, 155, 110, 240), "detect": (42, 108), "icon": (50, 168, 106, 224)},
    "slot1": {"icon": (408, 92, 460, 144)},
    "slot2": {"icon": (544, 92, 596, 144)},
    "slot3": {"icon": (680, 92, 732, 144)},
}


def slot_specs(hud):
    specs = {s["key"]: dict(s) for s in SLOTS}
    if hud < SMALL_HUD:
        for k, over in SLOTS_SMALL.items():
            specs[k].update(over)
    return specs


# White keybind badges ("1","2","3"); if they're missing the hotbar is hidden
# (inventory, menus, loading) and auras are hidden too.
BADGES = [(470, 178, 488, 202), (606, 178, 624, 202), (742, 178, 760, 202)]

DEFAULTS = {
    "x": None,             # aura group centre x (None = screen centre)
    "y": None,             # aura group top y   (None = 62% of screen height)
    "icon_size": 64,
    "spacing": 8,
    "slots": ["potion", "slot1", "slot2", "slot3"],
    "round_slots": [],          # e.g. ["slot1"] to draw a slot as a circle with a ring instead
    "max_buffs": 6,  # drawn as circles with a cooldown ring
    "hide_when_ready": False,   # True = only show auras while on cooldown
    "ready_glow_seconds": 1.4,
    "sound_on_ready": False,
    "only_when_game_focused": True,
    "show_buffs": True,         # big glowing copies of the buff/debuff icons above the hotbar
    "buff_icon_size": 72,
    "show_health_bar": True,
    "show_soul_bar": True,
    "bar_width": 0,             # 0 = same width as the cooldown row
    "bar_height": 24,
    "low_health_alert": 0.3,    # health bar pulses red at/below this fraction
    "hud_scale": None,          # auto-detected from the hotbar (in-game HUD Size)
    "learned_durations": {},
    "buff_durations": None,     # measured real buff lengths on this character (only ever lengthen the wiki value)
    "hide_game_buffs": False,   # blur-cover over the game's buff row (looks bad; a real in-game mod is the proper fix)
    "artifact_buffs": {},       # learned: which buff each artifact gives (shown on its square)
    "panels": None,             # per panel {"x", "y", "dir": "x"|"y", "show"}; F8 to move / right-click to flip
    "buff_order": [],           # buff priority (F8: drag buffs to reorder)
    "buff_group": {},           # buff -> panel overrides (F8: drag a buff onto another panel)
}

# --------------------------------------------------------------------------
# Win32 plumbing
# --------------------------------------------------------------------------
user32 = ctypes.windll.user32
gdi32 = ctypes.windll.gdi32
kernel32 = ctypes.windll.kernel32
try:
    ctypes.windll.shcore.SetProcessDpiAwareness(2)
except Exception:
    user32.SetProcessDPIAware()

WS_POPUP = 0x80000000
WS_EX_LAYERED, WS_EX_TRANSPARENT = 0x80000, 0x20
WS_EX_TOPMOST, WS_EX_TOOLWINDOW, WS_EX_NOACTIVATE = 0x8, 0x80, 0x08000000
GWL_EXSTYLE = -20
WM_NCHITTEST, WM_DESTROY, WM_EXITSIZEMOVE = 0x84, 0x2, 0x232
HTCAPTION = 2
SW_SHOWNOACTIVATE, SW_HIDE = 4, 0
HWND_TOPMOST = -1
SWP_NOMOVE, SWP_NOSIZE, SWP_NOACTIVATE = 0x2, 0x1, 0x10
VK_F8, VK_CONTROL, VK_SHIFT = 0x77, 0x11, 0x10

LRESULT = ctypes.c_ssize_t
WNDPROC = ctypes.WINFUNCTYPE(LRESULT, wt.HWND, wt.UINT, wt.WPARAM, wt.LPARAM)
user32.DefWindowProcW.restype = LRESULT
user32.DefWindowProcW.argtypes = [wt.HWND, wt.UINT, wt.WPARAM, wt.LPARAM]
user32.GetWindowLongPtrW.restype = ctypes.c_ssize_t
user32.GetWindowLongPtrW.argtypes = [wt.HWND, ctypes.c_int]
user32.SetWindowLongPtrW.restype = ctypes.c_ssize_t
user32.SetWindowLongPtrW.argtypes = [wt.HWND, ctypes.c_int, ctypes.c_ssize_t]
user32.CreateWindowExW.restype = wt.HWND
user32.CreateWindowExW.argtypes = [wt.DWORD, wt.LPCWSTR, wt.LPCWSTR, wt.DWORD, ctypes.c_int, ctypes.c_int,
                                   ctypes.c_int, ctypes.c_int, wt.HWND, wt.HMENU, wt.HINSTANCE, wt.LPVOID]
gdi32.CreateDIBSection.restype = wt.HBITMAP
gdi32.CreateDIBSection.argtypes = [wt.HDC, ctypes.c_void_p, wt.UINT, ctypes.POINTER(ctypes.c_void_p), wt.HANDLE, wt.DWORD]
gdi32.SelectObject.restype = wt.HGDIOBJ
gdi32.SelectObject.argtypes = [wt.HDC, wt.HGDIOBJ]
gdi32.DeleteObject.argtypes = [wt.HGDIOBJ]
gdi32.CreateCompatibleDC.restype = wt.HDC
gdi32.CreateCompatibleDC.argtypes = [wt.HDC]
gdi32.DeleteDC.argtypes = [wt.HDC]
user32.UpdateLayeredWindow.argtypes = [wt.HWND, wt.HDC, ctypes.c_void_p, ctypes.c_void_p, wt.HDC, ctypes.c_void_p,
                                       wt.DWORD, ctypes.c_void_p, wt.DWORD]
user32.ShowWindow.argtypes = [wt.HWND, ctypes.c_int]
user32.SetWindowPos.argtypes = [wt.HWND, wt.HWND, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int, wt.UINT]
user32.GetWindowRect.argtypes = [wt.HWND, ctypes.POINTER(wt.RECT)]
user32.GetForegroundWindow.restype = wt.HWND
user32.GetWindowThreadProcessId.argtypes = [wt.HWND, ctypes.POINTER(wt.DWORD)]
user32.LoadCursorW.restype = wt.HANDLE
user32.LoadCursorW.argtypes = [wt.HINSTANCE, ctypes.c_void_p]
kernel32.GetModuleHandleW.restype = wt.HMODULE
kernel32.OpenProcess.restype = wt.HANDLE
kernel32.CloseHandle.argtypes = [wt.HANDLE]
kernel32.QueryFullProcessImageNameW.argtypes = [wt.HANDLE, wt.DWORD, wt.LPWSTR, ctypes.POINTER(wt.DWORD)]
user32.GetDC.restype = wt.HDC
user32.ReleaseDC.argtypes = [wt.HWND, wt.HDC]


class WNDCLASSEXW(ctypes.Structure):
    _fields_ = [("cbSize", wt.UINT), ("style", wt.UINT), ("lpfnWndProc", WNDPROC), ("cbClsExtra", ctypes.c_int),
                ("cbWndExtra", ctypes.c_int), ("hInstance", wt.HINSTANCE), ("hIcon", wt.HICON),
                ("hCursor", wt.HANDLE), ("hbrBackground", wt.HBRUSH), ("lpszMenuName", wt.LPCWSTR),
                ("lpszClassName", wt.LPCWSTR), ("hIconSm", wt.HICON)]


class BLENDFUNCTION(ctypes.Structure):
    _fields_ = [("BlendOp", ctypes.c_ubyte), ("BlendFlags", ctypes.c_ubyte),
                ("SourceConstantAlpha", ctypes.c_ubyte), ("AlphaFormat", ctypes.c_ubyte)]


class BITMAPINFOHEADER(ctypes.Structure):
    _fields_ = [("biSize", wt.DWORD), ("biWidth", wt.LONG), ("biHeight", wt.LONG), ("biPlanes", wt.WORD),
                ("biBitCount", wt.WORD), ("biCompression", wt.DWORD), ("biSizeImage", wt.DWORD),
                ("biXPelsPerMeter", wt.LONG), ("biYPelsPerMeter", wt.LONG), ("biClrUsed", wt.DWORD),
                ("biClrImportant", wt.DWORD)]


def foreground_exe():
    hwnd = user32.GetForegroundWindow()
    pid = wt.DWORD()
    user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
    h = kernel32.OpenProcess(0x1000, False, pid.value)  # QUERY_LIMITED_INFORMATION
    if not h:
        return ""
    buf = ctypes.create_unicode_buffer(520)
    n = wt.DWORD(520)
    kernel32.QueryFullProcessImageNameW(h, 0, buf, ctypes.byref(n))
    kernel32.CloseHandle(h)
    return os.path.basename(buf.value).lower()


def key_down(vk):
    return bool(user32.GetAsyncKeyState(vk) & 0x8000)


class LayeredWindow:
    """Per-pixel-alpha, topmost, click-through window fed with PIL images."""

    def __init__(self, on_moved, native_drag=True):
        self.on_moved = on_moved
        self.native_drag = native_drag
        self.locked = True
        self._proc = WNDPROC(self._wndproc)
        hinst = kernel32.GetModuleHandleW(None)
        wc = WNDCLASSEXW()
        wc.cbSize = ctypes.sizeof(WNDCLASSEXW)
        wc.lpfnWndProc = self._proc
        wc.hInstance = hinst
        wc.hCursor = user32.LoadCursorW(None, ctypes.c_void_p(32646))  # size-all
        wc.lpszClassName = "D2AurasOverlay"
        user32.RegisterClassExW(ctypes.byref(wc))
        ex = WS_EX_LAYERED | WS_EX_TRANSPARENT | WS_EX_TOPMOST | WS_EX_TOOLWINDOW | WS_EX_NOACTIVATE
        self.hwnd = user32.CreateWindowExW(ex, "D2AurasOverlay", "Dungeons II Auras", WS_POPUP,
                                           0, 0, 10, 10, None, None, hinst, None)
        self.visible = False
        self.pos = (0, 0)

    def _wndproc(self, hwnd, msg, wp, lp):
        if msg == WM_NCHITTEST and not self.locked and self.native_drag:
            return HTCAPTION
        if msg == WM_EXITSIZEMOVE:
            r = wt.RECT()
            user32.GetWindowRect(hwnd, ctypes.byref(r))
            self.on_moved(r.left - self.pos[0], r.top - self.pos[1])
            return 0
        return user32.DefWindowProcW(hwnd, msg, wp, lp)

    def set_locked(self, locked):
        self.locked = locked
        ex = user32.GetWindowLongPtrW(self.hwnd, GWL_EXSTYLE)
        ex = (ex | WS_EX_TRANSPARENT) if locked else (ex & ~WS_EX_TRANSPARENT)
        user32.SetWindowLongPtrW(self.hwnd, GWL_EXSTYLE, ex)

    def show(self, on):
        if on != self.visible:
            user32.ShowWindow(self.hwnd, SW_SHOWNOACTIVATE if on else SW_HIDE)
            self.visible = on
        if on:  # games love to steal topmost
            user32.SetWindowPos(self.hwnd, HWND_TOPMOST, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE)

    def update(self, img, x, y):
        self.pos = (x, y)
        w, h = img.size
        a = np.asarray(img, dtype=np.uint16)
        alpha = a[..., 3:4]
        bgra = np.empty((h, w, 4), np.uint8)
        bgra[..., :3] = (a[..., 2::-1] * alpha // 255).astype(np.uint8)  # premultiplied BGR
        bgra[..., 3] = a[..., 3]
        bmi = BITMAPINFOHEADER(ctypes.sizeof(BITMAPINFOHEADER), w, -h, 1, 32, 0, 0, 0, 0, 0, 0)
        screen = user32.GetDC(None)
        mem = gdi32.CreateCompatibleDC(screen)
        bits = ctypes.c_void_p()
        hbmp = gdi32.CreateDIBSection(mem, ctypes.byref(bmi), 0, ctypes.byref(bits), None, 0)
        ctypes.memmove(bits, bgra.ctypes.data, bgra.nbytes)
        old = gdi32.SelectObject(mem, hbmp)
        blend = BLENDFUNCTION(0, 0, 255, 1)
        user32.UpdateLayeredWindow(self.hwnd, screen, ctypes.byref(wt.POINT(x, y)), ctypes.byref(wt.SIZE(w, h)),
                                   mem, ctypes.byref(wt.POINT(0, 0)), 0, ctypes.byref(blend), 2)
        gdi32.SelectObject(mem, old)
        gdi32.DeleteObject(hbmp)
        gdi32.DeleteDC(mem)
        user32.ReleaseDC(None, screen)

    def pump(self):
        msg = wt.MSG()
        while user32.PeekMessageW(ctypes.byref(msg), None, 0, 0, 1):
            user32.TranslateMessage(ctypes.byref(msg))
            user32.DispatchMessageW(ctypes.byref(msg))


# --------------------------------------------------------------------------
# Cooldown reading
# --------------------------------------------------------------------------
class SlotTracker:
    def __init__(self, spec, learned):
        self.spec = spec
        self.learned = learned          # dict shared with config
        self.on_cd = False
        self.samples = []               # (t, line_y) for the current cooldown
        self.miss = 0
        self.icon = None
        self.icon_t = 0
        self.ready_at = -99.0
        self.remaining = 0.0
        self.frac = 0.0
        self.active = False             # slot is red: the artifact's effect is running (a buff)
        self.active_since = -99.0
        self._red = 0
        self.art = None                 # official artifact name if recognised
        self.started_at = -99.0         # when the current cooldown began (= artifact used)
        self.hud = 1.0
        self.end_t = None               # predicted end of the current cooldown (smoothed)
        self.total = None               # estimated full cooldown length, for the ring
        self.last_line_t = 0.0

    def feed(self, crop, t):
        """crop: RGB uint8 array of the hotbar in reference (crop) coordinates."""
        x0, y0, x1, y1 = self.spec["rect"]
        dx0, dx1 = self.spec["detect"]
        region = crop[y0:y1, dx0:dx1].astype(np.int16)
        R, G, B = region[..., 0], region[..., 1], region[..., 2]
        # artifacts only: the potion bottle itself is red
        red = self.spec["key"] != "potion" and ((R > 150) & (R > G + 80) & (R > B + 60)).mean() > 0.3
        self._red = min(4, self._red + 1) if red else max(0, self._red - 1)
        if self._red >= 2 and not self.active:
            self.active, self.active_since = True, t
        elif self._red == 0:
            self.active = False
        lo = region.min(axis=2)
        frac = ((lo > 185) & (region.max(axis=2) - lo < 40)).mean(axis=1)
        rows = np.nonzero(frac > 0.5)[0]
        line = None
        if 0 < len(rows) <= 30:  # a thin white line; a fully white slot is the "ready" flash
            runs = np.split(rows, np.nonzero(np.diff(rows) > 1)[0] + 1)
            if all(len(r) <= 16 for r in runs):  # a long white band = ready flash, not a line  # the line fades out near the end, so take the strongest band
                best = max(runs, key=lambda r: frac[r].mean() + 0.01 * len(r))
                line = y0 + float(best.mean())
        ex = getattr(self, "exact", None)
        if ex is not None and t - ex[2] < 1.0:
            # the game's own timer drives this slot: a white glint in the slot art must not start a
            # fake cooldown (it fought the exact timer every frame and kept the "ready" flash on)
            line = None
        elif line is not None:
            self.miss = 0
            if not self.on_cd or (self.samples and line < self.samples[-1][1] - 6):
                # new cooldown (or re-used right after ready)
                self.on_cd, self.samples, self.end_t, self.total = True, [], None, None
                self.started_at = t
            self.samples.append((t, line))
            self.samples = self.samples[-120:]
            self.last_line_t = t
            old = [q for q in self.samples if t - q[0] > 2.0]
            if old and abs(line - old[-1][1]) < 2:  # a "line" that never moves is part of the art
                self._finish(t, learn=False)
                self.ready_at = -99.0
                return
            self._estimate(t, line)
            if self.remaining >= 0:
                new_end = t + self.remaining
                if self.end_t is None or abs(new_end - self.end_t) > 1.5:
                    self.end_t = new_end
                else:  # smooth so the number counts down steadily instead of jittering
                    self.end_t = self.end_t * 0.85 + new_end * 0.15
                if self.frac > 0.05:
                    self.total = self.remaining / self.frac
        elif self.on_cd:
            # the line can be hidden for a moment (flash, effects): keep counting, only stop when
            # the slot is clearly back to normal or the predicted end has passed
            self.miss += 1
            rem = None if self.end_t is None else self.end_t - t
            dark = np.median(region.max(axis=2)) < 80
            young = t - self.started_at < 1.0
            gone = t - self.last_line_t
            if young or (rem is None and gone < 1.0):
                pass  # just used / no estimate yet: a hidden line means the flash, not "ready"
            elif self.miss >= 3 and (rem is None or rem < 0.5 or (gone > 0.3 and dark)):
                self._finish(t)
            elif rem is not None and rem < -0.3:
                self._finish(t)
        if not self.on_cd and not self.active and self._red == 0 and len(rows) == 0 and t - self.icon_t > 1.0 and t - self.ready_at > 0.6:
            ix0, iy0, ix1, iy1 = self.spec["rect"] if self.spec["key"] != "potion" else self.spec["icon"]
            sub = crop[iy0:iy1, ix0:ix1]
            ring = np.concatenate([sub[2:6].reshape(-1, 3), sub[-6:-2].reshape(-1, 3),
                                   sub[:, 2:6].reshape(-1, 3), sub[:, -6:-2].reshape(-1, 3)])
            normal = np.median(ring.max(axis=1)) < 70  # dark slot = normal state (not greyed / flashing)
            if normal:
                cut = cut_item(sub)
                if self.spec["key"] == "potion":
                    # no potion icon exists online: keep the game's own sprite, cleanly cut out
                    if cut is not None and self.icon is None:
                        self.icon = cut
                else:
                    if getattr(self, "art_from_game", False):
                        if self.art is None and cut is not None:
                            self.icon = cut  # artifact without a wiki icon: use the game's own sprite
                    else:
                        name = recognise_artifact(cut)
                        if name:
                            self.art = name
                        elif cut is not None:
                            self.art, self.icon = None, cut
            self.icon_t = t

    def set_exact(self, rem, dur, t):
        self.exact = (rem, dur, t)

    def tick(self, t):
        """Advance the countdown every frame, even when the hotbar couldn't be read."""
        ex = getattr(self, "exact", None)
        if ex is not None and t - ex[2] < 1.0:  # exact cooldown from game memory
            rem = max(0.0, ex[0] - (t - ex[2]))
            if rem > 0.03:
                if not self.on_cd:
                    self.started_at = t
                self.on_cd, self.remaining = True, rem
                self.frac = min(1.0, rem / ex[1]) if ex[1] > 0 else 0.0
                self.end_t, self.total = t + rem, ex[1]
            elif self.on_cd:
                self.on_cd, self.remaining, self.frac = False, 0.0, 0.0
                self.end_t = self.total = None
                self.ready_at = t
            return
        if self.on_cd and self.end_t is not None:
            self.remaining = max(0.0, self.end_t - t)
            if self.total and t - self.last_line_t > 0.05:
                self.frac = min(1.0, self.remaining / self.total)
            if t - self.last_line_t > 3.0 and self.remaining <= 0:  # never got the end: give up
                self._finish(t)

    def _lkey(self):
        return self.spec["key"]

    def _speed(self):
        if len(self.samples) < 4 or self.samples[-1][0] - self.samples[0][0] < 0.35:
            return None
        ts = np.array([s[0] for s in self.samples])
        ys = np.array([s[1] for s in self.samples])
        slope = np.polyfit(ts - ts[0], ys, 1)[0]
        return slope if slope > 0.2 else None

    def _estimate(self, t, line):
        x0, y0, x1, y1 = self.spec["rect"]
        span = y1 - y0
        self.frac = min(1.0, max(0.0, (y1 - line) / span))
        speed = self._speed()
        known = self.learned.get(self._lkey())
        settled = self.samples[-1][0] - self.samples[0][0] > 0.8
        if speed and (settled or not known):
            self.remaining = (y1 - line) / speed
        elif known:
            self.remaining = self.frac * known
        else:
            self.remaining = -1  # unknown yet: swipe only, no number

    def _finish(self, t, learn=True):
        x0, y0, x1, y1 = self.spec["rect"]
        speed = self._speed()
        if learn and speed and len(self.samples) > 10:
            total = (y1 - y0) / speed
            old = self.learned.get(self._lkey())
            self.learned[self._lkey()] = round(total if old is None else old * 0.5 + total * 0.5, 2)
        self.on_cd, self.samples, self.miss = False, [], 0
        self.remaining, self.frac = 0.0, 0.0
        self.end_t = self.total = None
        self.ready_at = t


def hotbar_visible(crop):
    # 2 of the 3 keybind badges is enough: effects and damage numbers often cover one
    return sum((crop[y0:y1, x0:x1].min(axis=2) > 190).mean() > 0.35 for x0, y0, x1, y1 in BADGES) >= 2


def _surface(filled):
    """filled: bool per row (top->bottom). Fraction of the column that is filled from the bottom."""
    n = len(filled)
    if n == 0:
        return 0.0
    below = np.cumsum(filled[::-1])[::-1]  # filled rows from i to the bottom
    for i in range(n):
        if filled[i] and below[i] >= 0.85 * (n - i):
            return 1 - i / n
    return 0.0


class VitalsReader:
    """Health from the heart's red fill, souls from the hexagon (number via OCR, fill for the bar)."""
    HEART = (215, 110, 275, 238)          # x0, y0, x1, y1 in hotbar crop coords
    HEX_CX, HEX_TOP, HEX_FLAT0, HEX_FLAT1, HEX_BOTTOM, HEX_HW = 850, 80, 110, 173, 212, 58
    DIGITS = (790, 140, 912, 226)  # search area around the soul number

    def __init__(self):
        self.health = None
        self.souls = None
        self.soul_frac = None
        self._hp_hist = []
        try:
            self.templates = np.load(os.path.join(HERE, "digits.npy"))
        except OSError:
            self.templates = None

    def feed(self, crop, t):
        x0, y0, x1, y1 = self.HEART
        r = crop[y0:y1, x0:x1].astype(np.int16)
        red = (r[..., 0] > 45) & (r[..., 0] > r[..., 1] * 1.6)  # also matches the dim low-HP pulse
        white = r.min(axis=2) > 200
        filled = int(((red | white).mean(axis=1) > 0.6).sum())
        self._hp_full = max(getattr(self, "_hp_full", 0) * 0.9995, filled)  # full heart = most rows ever filled
        hp = filled / self._hp_full if self._hp_full >= 20 else 1.0
        self._hp_hist = [(tt, v) for tt, v in self._hp_hist if t - tt < 0.25] + [(t, hp)]
        self.health = float(np.median([v for _, v in self._hp_hist]))  # damage-number flicker filter

        rows = []
        for y in range(self.HEX_TOP + 4, self.HEX_BOTTOM - 4):
            if y < self.HEX_FLAT0:
                hw = self.HEX_HW * (y - self.HEX_TOP) / (self.HEX_FLAT0 - self.HEX_TOP)
            elif y > self.HEX_FLAT1:
                hw = self.HEX_HW * (self.HEX_BOTTOM - y) / (self.HEX_BOTTOM - self.HEX_FLAT1)
            else:
                hw = self.HEX_HW
            xs = [x for x in range(self.HEX_CX - int(hw) + 6, self.HEX_CX + int(hw) - 6) if abs(x - self.HEX_CX) > 22]
            if len(xs) < 4:
                continue
            px = crop[y, xs].astype(np.int16)
            rows.append((px.max(axis=1) > 70).mean() > 0.6)
        if rows:
            self.soul_frac = _surface(np.array(rows))
        if t - getattr(self, "_ocr_t", 0) > 0.15:
            self._ocr_t = t
            n = self.read_souls(crop)
            if n is not None and n == getattr(self, "_last_read", None):
                self.souls = n
            self._last_read = n

    def read_souls(self, crop):
        """OCR the soul count: digits are the bright blobs sitting on the lowest common baseline
        (the ghost icon above them can touch the number at small HUD sizes)."""
        if self.templates is None:
            return None
        x0, y0, x1, y1 = self.DIGITS
        r = crop[y0:y1, x0:x1].astype(np.int16)
        m = (r[..., 0] > 125) & (r[..., 1] > 190) & (r[..., 2] > 190)
        lab, comps = _components(m)
        cand = [c for c in comps if 12 <= c[1] - c[0] + 1 <= 45 and 2 <= c[3] - c[2] + 1 <= 35]
        if not cand:
            return None
        base = max(c[1] for c in cand)
        hmax = max(c[1] - c[0] + 1 for c in cand if c[1] >= base - 4)
        digits = sorted((c for c in cand if c[1] >= base - 4 and c[1] - c[0] + 1 >= 0.75 * hmax), key=lambda c: c[2])
        if not 0 < len(digits) <= 4:
            return None
        text = ""
        for top, bot, left, right, n in digits:
            g = lab[top:bot + 1, left:right + 1] == n
            g = np.asarray(Image.fromarray((g * 255).astype(np.uint8)).resize((12, 16), Image.BILINEAR)) / 255.0
            d = ((self.templates[:, :13] - g[:13]) ** 2).mean(axis=(1, 2))  # ignore the bottom: fonts differ there
            if d.min() > 0.05:
                return None  # something is in the way (damage numbers, effects)
            text += str(int(d.argmin()))
        return int(text)


def _components(m):
    """4-connected blobs of a small bool mask -> (label image, [(top, bottom, left, right, label)])."""
    lab = np.zeros(m.shape, np.int32)
    h, w = m.shape
    out, n = [], 0
    for y0, x0 in zip(*np.nonzero(m)):
        if lab[y0, x0]:
            continue
        n += 1
        lab[y0, x0] = n
        stack, ys, xs = [(y0, x0)], [], []
        while stack:
            y, x = stack.pop()
            ys.append(y)
            xs.append(x)
            for yy, xx in ((y + 1, x), (y - 1, x), (y, x + 1), (y, x - 1)):
                if 0 <= yy < h and 0 <= xx < w and m[yy, xx] and not lab[yy, xx]:
                    lab[yy, xx] = n
                    stack.append((yy, xx))
        out.append((min(ys), max(ys), min(xs), max(xs), n))
    return lab, out


# --------------------------------------------------------------------------
# Icon cut-outs: no slot background, no cost text, no game world behind buffs
# --------------------------------------------------------------------------
def cut_item(arr):
    """Hotbar item -> RGBA with the dark slot background, cyan soul-cost text and specks removed."""
    a = arr.astype(np.int16)
    R, G, B = a[..., 0], a[..., 1], a[..., 2]
    mx, mn = a.max(axis=2), a.min(axis=2)
    edge = np.concatenate([a[0], a[-1], a[:, 0], a[:, -1]])
    ref = np.median(edge, axis=0)  # slot / panel colour
    bg = ((mx < 75) & (mx - mn < 35)) | (np.abs(a - ref).sum(axis=2) < 45)
    text = (B > 170) & (G > 160) & (R < 190) & (B > R + 20)
    text = np.asarray(Image.fromarray((text * 255).astype(np.uint8)).filter(ImageFilter.MaxFilter(7))) > 0
    keep = ~bg & ~text
    keep[:, :4] = False
    keep[:, -4:] = False
    keep[:4] = False
    keep[-4:] = False
    lab, comps = _components(keep)
    if not comps:
        return None
    sizes = {c[4]: int((lab == c[4]).sum()) for c in comps}
    biggest = max(sizes.values())
    keep = np.isin(lab, [n for n, sz in sizes.items() if sz >= max(15, biggest * 0.25)])
    ys, xs = np.nonzero(keep)
    if len(ys) < 40:
        return None
    rgba = np.dstack([arr, (keep * 255).astype(np.uint8)])[ys.min():ys.max() + 1, xs.min():xs.max() + 1]
    return Image.fromarray(np.ascontiguousarray(rgba), "RGBA")


def _side_rows(big, xc):
    a = big[0:110, xc - 2:xc + 3].astype(np.int16)
    s = (a.max(axis=2) < 60).any(axis=1) | (np.abs(np.diff(a.mean(axis=2), axis=1)) > 40).any(axis=1)
    best, i = (0, 0), 0
    while i < len(s):
        if s[i]:
            j = i
            while j < len(s) and s[j]:
                j += 1
            if j - i > best[1] - best[0]:
                best = (i, j)
            i = j
        i += 1
    return best


def cut_buff(big, x, w=52):
    """Buff icon -> RGBA cut along its house (buff) or shield (debuff) outline."""
    p = big[35:66].astype(np.int16)
    grad = np.pad(np.abs(np.diff(p.mean(axis=2), axis=1)) > 40, ((0, 0), (1, 0)))
    colf = ((p.max(axis=2) < 50) | grad).mean(axis=0)
    l = max(range(max(3, x - 4), x + 5), key=lambda c: colf[c])
    r = max(range(min(x + w - 8, big.shape[1] - 4), min(x + w + 8, big.shape[1] - 3)), key=lambda c: colf[c])
    t0, b0 = _side_rows(big, l)
    t1, b1 = _side_rows(big, r)
    top, bot = max(t0, t1), min(b0, b1)
    if bot - top < 20:
        top, bot = 35, 70
    width = r - l
    cx = (l + r) / 2
    roof, vee = int(round(0.33 * width)), int(round(0.43 * width))

    def darkline(segs):
        hit = n = 0
        for (xa, ya), (xb, yb) in segs:
            for s in np.linspace(0, 1, 20):
                xx, yy = int(round(xa + (xb - xa) * s)), int(round(ya + (yb - ya) * s))
                if 1 <= yy < big.shape[0] - 1:
                    n += 1
                    hit += bool((big[yy - 1:yy + 2, xx - 1:xx + 2].max(axis=2) < 60).any())
        return hit / max(1, n)

    house = darkline([((l, top), (cx, top - roof)), ((r, top), (cx, top - roof))])
    shield = darkline([((l, bot), (cx, bot + vee)), ((r, bot), (cx, bot + vee))])
    if abs(house - shield) < 0.25:  # unclear outline: whichever tip looks like the icon body
        body = big[top + 6:bot - 6, l + 8:r - 8].reshape(-1, 3).mean(axis=0)
        ry = max(2, top - roof // 2)
        vy = min(big.shape[0] - 3, bot + vee // 2)
        rp = big[ry - 2:ry + 3, int(cx) - 2:int(cx) + 3].reshape(-1, 3).mean(axis=0)
        vp = big[vy - 2:vy + 3, int(cx) - 2:int(cx) + 3].reshape(-1, 3).mean(axis=0)
        house, shield = -np.abs(rp - body).sum(), -np.abs(vp - body).sum()
    if house >= shield:
        poly = [(l, top), (cx, top - roof), (r, top), (r, bot), (l, bot)]
    else:
        poly = [(l, top), (r, top), (r, bot), (cx, bot + vee), (l, bot)]
    y0 = max(0, int(min(pt[1] for pt in poly)))
    y1 = min(big.shape[0] - 1, int(max(pt[1] for pt in poly)))
    crop = big[y0:y1 + 1, l:r + 1]
    mask = Image.new("L", (crop.shape[1], crop.shape[0]), 0)
    ImageDraw.Draw(mask).polygon([(px - l, py - y0) for px, py in poly], fill=255)
    m = np.asarray(mask).copy()
    xs = np.arange(l, r + 1)
    over = (xs >= 495) & (xs <= 625)  # the arrow counter sits under this part of the buff row
    if over.any():
        m[max(0, 62 - y0):, over] = 0
    img = Image.fromarray(np.ascontiguousarray(crop)).convert("RGBA")
    img.putalpha(Image.fromarray(m))
    return img


# --------------------------------------------------------------------------
# Official game icons (datamined set from th.gl, see icons/game/index.json) and wiki data
# --------------------------------------------------------------------------
# durations: metabot.gg status list (build 1.1.1.0), artifact ones checked against the game data
# (Tempo Truffle 8 s, Warding Chimes 5 s); only a fallback - real timers come from game memory;
# real lengths on this character are
# measured in play and can only lengthen these (gear extends buffs)
STATUS_DUR = {
    "Artificing": 6, "Blaze Bangle": 8, "Blight Bangle": 8, "Blizzard Bangle": 8, "Electric Bangle": 8,
    "Critical Precision": 4, "Critical Strength": 4, "Deathcap Mushroom": 6, "Deflection": 8, "Flurrying": 4,
    "Fortifying": 5, "Grindstone": 6, "Hurrying": 8, "Invulnerable": 5, "Powershaker": 6, "Regenerating": 4.5,
    "Shadowcloaking": 8, "Stampeding": 4, "Strengthened": 4,
    "Burned": 4, "Chained": 5, "Frozen": 15, "Honeyed": 6, "Poisoned": 15, "Sealed": 8, "Slowed": 6,
    "Soulsick": 5, "Vined": 8, "Weakened": 5, "Webbed": 3, "Zapped": 8,
}
NEGATIVE = {"Burned", "Chained", "Frozen", "Honeyed", "Poisoned", "Sealed", "Slowed", "Soulsick", "Vined",
            "Weakened", "Webbed", "Zapped"}
# which panel each buff goes in by default (F8 lets you drag any buff to another panel)
ATTACK_BUFFS = {"Strengthened", "Critical Precision", "Critical Strength", "Flurrying", "Artificing", "Powershaker",
                "Grindstone", "Blaze Bangle", "Blight Bangle", "Blizzard Bangle", "Electric Bangle",
                "Deathcap Mushroom", "Stampeding"}
BUFF_PANELS = ("attack", "defense", "debuffs")


def default_group(name):
    if name in NEGATIVE:
        return "debuffs"
    return "attack" if name in ATTACK_BUFFS else "defense"


# the game's internal item IDs -> display names (icons are keyed by display name)
ARTIFACT_IDS = {
    "WarBanner": "Battle Banner", "FireBracelet": "Blaze Bangle", "PoisonBracelet": "Blight Bangle",
    "FrostBracelet": "Blizzard Bangle", "FlameScepter": "Cinder Scepter", "FlameSceptre": "Cinder Scepter",
    "LightningQuiver": "Conductive Quiver", "CorruptedBeacon": "Corrupted Beacon", "CorruptedSeeds": "Corrupted Seeds",
    "CreeperCandle": "Creeper Candle", "DeathcapMushroom": "Death Cap Mushroom", "CarapaceOcarina": "Echo Ocarina",
    "ConductiveBracelet": "Electric Bangle", "SmokeBomb": "Ender Fog", "FightersFife": "Fighter's Flute",
    "MaimingMushroom": "Fighting Fungus", "Mushroom.Maiming": "Fighting Fungus", "FireworkQuiver": "Firework Arrow",
    "FlameQuiver": "Flaming Quiver", "FrostQuiver": "Freezing Quiver", "Grindstone": "Grindstone",
    "Honeypot": "Honey Dipper", "RallyingHorn": "Humbling Horn", "LightningRod": "Lightning Rod",
    "PicnicBlanket": "Picnic Basket", "Satchel.Fire": "Pouch of Ember", "Satchel.Freezing": "Pouch of Frost",
    "Satchel.Poison": "Pouch of Poison", "Satchel.Conductive": "Pouch of Thunder", "Powershaker": "Powershaker",
    "RedstoneMines": "Redstone Mine Launcher", "SoulHarvester": "Soul Harvester", "HasteMushroom": "Tempo Truffle",
    "Mushroom.Haste": "Tempo Truffle", "TotemOfCasting": "Totem of Casting", "TotemOfRegeneration": "Totem of Regeneration",
    "TotemOfShielding": "Totem of Shielding", "IronHideLute": "Turtle Master's Mandolin", "PoisonQuiver": "Venomous Quiver",
    "WardingChimes": "Warding Chimes", "WarDrums": "Warrior Drums", "WarriorsDrums": "Warrior Drums",
    "BlizzardStaff": "Winter Staff", "WitchesBrew": "Witch Brew",
}


def artifact_name(item_tag):
    if not item_tag or not item_tag.startswith("SW.Item.Artifact."):
        return None
    core = item_tag[len("SW.Item.Artifact."):]
    for key in (core, core.split("_")[0]):
        if key in ARTIFACT_IDS:
            return ARTIFACT_IDS[key]
    return None


# artifact -> the buff it gives you: using it starts/refreshes that buff instantly
ARTIFACT_BUFF = {
    "Fighting Fungus": "Flurrying", "Tempo Truffle": "Hurrying", "Death Cap Mushroom": "Deathcap Mushroom",
    "Echo Ocarina": "Deflection", "Warding Chimes": "Invulnerable", "Ender Fog": "Shadowcloaking",
    "Powershaker": "Powershaker", "Grindstone": "Grindstone", "Blaze Bangle": "Blaze Bangle",
    "Blight Bangle": "Blight Bangle", "Blizzard Bangle": "Blizzard Bangle", "Electric Bangle": "Electric Bangle",
    "Fighter's Flute": "Critical Precision", "Warrior Drums": "Critical Strength",
    # from the game's own artifact data (2026-10-12 audit): area artifacts apply these to you
    "Turtle Master's Mandolin": "Fortifying", "Battle Banner": "Strengthened",
    "Totem of Regeneration": "Regenerating", "Totem of Casting": "Artificing",
}
# no buff on you (damage, summons, projectiles, or debuffs on enemies): Humbling Horn (slows
# enemies), Totem of Shielding (blocks projectiles), satchels, quivers, staffs, mines, seeds...


def _load_icons():
    """Official icons: the wiki's images (extracted from the game, higher resolution) first,
    the datamined th.gl set as a fallback. Keyed by the game's display names."""
    import re
    norm = lambda n: re.sub(r"[^a-z0-9]", "", n.lower())
    status, artifacts = {}, {}
    try:
        index = json.load(open(os.path.join(HERE, "icons", "game", "index.json"), encoding="utf-8"))
    except OSError:
        index = {}
    wiki = {}
    for folder in ("status", "artifacts"):
        d = os.path.join(HERE, "icons", folder)
        if os.path.isdir(d):
            wiki[folder] = {norm(f[:-4]): os.path.join(d, f) for f in os.listdir(d) if f.endswith(".png")}
    for v in index.values():
        cat = v["cat"]
        if cat not in ("status_effects", "gear_artifacts"):
            continue
        folder = "status" if cat == "status_effects" else "artifacts"
        path = wiki.get(folder, {}).get(norm(v["name"])) or os.path.join(HERE, "icons", "game", v["file"])
        try:
            im = Image.open(path).convert("RGBA")
        except OSError:
            continue
        (status if cat == "status_effects" else artifacts)[v["name"]] = im
    return status, artifacts


STATUS_ICONS, ARTIFACT_ICONS = _load_icons()
try:  # the game's potion sprite (no potion icon is published online), cut out once from the hotbar
    POTION_ICON = Image.open(os.path.join(HERE, "icons", "game", "potion.png")).convert("RGBA")
except OSError:
    POTION_ICON = None


def _alpha_sig(rgba, n=10):
    im = rgba.crop(rgba.getbbox()).resize((n, n), Image.BILINEAR)
    a = np.asarray(im).astype(np.float32)
    return a[..., :3] * (a[..., 3:] / 255.0)


_ART_SIGS = {name: _alpha_sig(im) for name, im in ARTIFACT_ICONS.items()}


def recognise_artifact(cut):
    """Clean cut-out of a hotbar slot -> official artifact name (or None if unsure)."""
    if cut is None or not _ART_SIGS:
        return None
    sig = _alpha_sig(cut)
    ranked = sorted((float(np.abs(sig - v).mean()), n) for n, v in _ART_SIGS.items())
    if ranked[0][0] <= 35 and ranked[1][0] - ranked[0][0] >= 5:
        return ranked[0][1]
    return None


class StatusMatcher:
    """Identifies an on-screen buff icon by comparing its centre with every official status icon."""
    P = 22

    def __init__(self):
        self.names = list(STATUS_ICONS)
        self._refs = {}
        self.cache = []  # (cheap sig, name, t) so a buff isn't re-identified every frame

    def refs(self, w):
        if w not in self._refs:
            c, h = w // 2, self.P // 2
            stack = []
            for n in self.names:
                im = STATUS_ICONS[n]
                a = np.asarray(im.crop(im.getbbox()).convert("RGB").resize((w, w), Image.BILINEAR)).astype(np.float32)
                stack.append(a[c - h:c + h, c - h:c + h])
            self._refs[w] = np.stack(stack)
        return self._refs[w]

    def geom(self, big, x, w=52):
        p = big[35:66].astype(np.int16)
        grad = np.pad(np.abs(np.diff(p.mean(axis=2), axis=1)) > 40, ((0, 0), (1, 0)))
        colf = ((p.max(axis=2) < 50) | grad).mean(axis=0)
        l = max(range(max(3, x - 4), x + 5), key=lambda c: colf[c])
        r = max(range(min(x + w - 8, big.shape[1] - 4), min(x + w + 8, big.shape[1] - 3)), key=lambda c: colf[c])
        t0, b0 = _side_rows(big, l)
        t1, b1 = _side_rows(big, r)
        return l, r, max(t0, t1), min(b0, b1)

    def identify(self, big, x, sig, t, expected=()):
        for cs, name, ct in self.cache:
            if t - ct < 3.0 and float(np.abs(cs - sig).mean()) < 12:
                return name
        if not self.names:
            return None
        l, r, top, bot = self.geom(big, x)
        cx, h = (l + r) // 2, self.P // 2
        best = np.full(len(self.names), 1e9, np.float32)
        for w in range(max(24, r - l - 14), r - l + 1, 2):
            R = self.refs(w)
            for cy in range(min(top, 40), max(bot, 50), 2):
                if cy + h > 64 and 495 <= cx <= 625:  # arrow counter underneath
                    continue
                for dx in (-2, 0, 2):
                    pt = big[cy - h:cy + h, cx + dx - h:cx + dx + h].astype(np.float32)
                    if pt.shape != (self.P, self.P, 3):
                        continue
                    best = np.minimum(best, np.abs(R - pt[None]).mean(axis=(1, 2, 3)))
        order = np.argsort(best)
        b0, b1 = float(best[order[0]]), float(best[order[1]])
        name = self.names[order[0]] if (b0 <= 42 and b1 - b0 >= 6) else None
        if name is None and self.names[order[0]] in expected and b0 <= 58:
            name = self.names[order[0]]
        if name:
            self.cache = [c for c in self.cache if t - c[2] < 3.0][-30:] + [(sig, name, t)]
        return name


# internal effect names (SW_Status_<X>_GE) -> status icon names
MEM_STATUS = {
    "Acceleration": "Flurrying", "Arcane": "Artificing", "Swiftness": "Hurrying", "Resistance": "Fortifying",
    "Strength": "Strengthened", "Regeneration": "Regenerating", "WobbleRegeneration": "Regenerating",
    "Critical_Chance_Increase": "Critical Precision", "Critical_Damage_Increase": "Critical Strength",
    "Deflection": "Deflection", "Invulnerable": "Invulnerable", "ShadowForm": "Shadowcloaking",
    "Unstoppable": "Stampeding",
    "Artifact_Buff_ConductiveBracelet": "Electric Bangle", "Artifact_Buff_DeathcapMushroom": "Deathcap Mushroom",
    "Artifact_Buff_FireBracelet": "Blaze Bangle", "Artifact_Buff_FrostBracelet": "Blizzard Bangle",
    "Artifact_Buff_Grindstone": "Grindstone", "Artifact_Buff_PoisonBracelet": "Blight Bangle",
    "Artifact_Buff_Powershaker": "Powershaker",
    "Burning": "Burned", "Chained": "Chained", "Conductive": "Zapped", "Freezing": "Frozen", "Honeyed": "Honeyed",
    "Poisoned": "Poisoned", "Slowed": "Slowed", "SoulSnared": "Soulsick", "Vined": "Vined", "Weakness": "Weakened",
    "Webbed": "Webbed",
}


def mem_status_name(defname):
    """'SW_Status_Slowed_Roar_GE' -> 'Slowed' (None if it isn't a status we have an icon for)."""
    if not defname or not defname.startswith("SW_Status_") or not defname.endswith("_GE"):
        return None
    core = defname[len("SW_Status_"):-len("_GE")]
    for suffix in ("_Infinite", "_Short", "_Lingering", "_Propagated"):
        if core.endswith(suffix):
            core = core[:-len(suffix)]
    if core in MEM_STATUS:
        return MEM_STATUS[core]
    base = core.split("_")[0]
    return MEM_STATUS.get(base)


class ExactSource:
    """Background thread reading the game's own buff and cooldown timers (read-only)."""

    def __init__(self):
        self.reader = None
        self.latest = None   # (time, buffs [(name, remaining, duration)], cooldowns {slot: (rem, dur)})
        self.attrs = {}      # Health, HealthMax, Souls, SoulsMax, HealthPotionCharges...
        self.equipped = {}   # equipment slot tag -> item tag
        self.ok = False
        self._stop = False
        threading.Thread(target=self._run, daemon=True).start()

    def _run(self):
        while not self._stop:
            if self.reader is None:
                try:
                    self.reader = d2_mem.BuffReader() if d2_mem else None
                except Exception:
                    self.reader = None
                if self.reader is None:
                    self.ok = False
                    time.sleep(3.0)
                    continue
            try:
                res = self.reader.poll(time.perf_counter())
            except Exception:
                try:
                    self.reader.g.close()
                except Exception:
                    pass
                self.reader = None
                self.ok = False
                time.sleep(0.5)
                continue
            if res is None:
                self.ok = False
                # game closed or relaunched: drop the old process and attach to the new one
                # (tasklist is slow to start: only ask about a new process every few seconds)
                now = time.perf_counter()
                relaunch = False
                if now - getattr(self, "_pid_check", 0.0) > 5.0:
                    self._pid_check = now
                    relaunch = d2_mem.find_pid() != self.reader.g.pid
                if not self.reader.alive() or relaunch:
                    try:
                        self.reader.g.close()
                    except Exception:
                        pass
                    self.reader = None
                time.sleep(0.5)
                continue
            buffs, cds, attrs, equipped = res
            self.equipped = equipped
            out = {}
            for defname, rem, dur, _st in buffs:
                name = mem_status_name(defname)
                if not name or name not in STATUS_ICONS:
                    continue
                # no fixed duration = lasts while something keeps it up (e.g. standing in a Totem of
                # Regeneration's area); the game shows these too, so show them without a countdown
                rem = min(rem, dur) if dur > 0 else -1.0
                if name not in out or rem > out[name][0] or (rem < 0 <= out[name][0]):
                    out[name] = (rem, dur)
            self.latest = (time.perf_counter(), [(n, r, d) for n, (r, d) in out.items()], cds)
            self.attrs = attrs
            self.ok = True
            time.sleep(1 / 15)

    def fresh(self, t):
        return self.ok and self.latest is not None and t - self.latest[0] < 1.0


class TestSource:
    """F8 menu 'Test buffs': random buffs and debuffs pop up, refresh and expire."""

    def __init__(self):
        self.active = {}
        self.next_t = 0.0

    def entries(self, t):
        if t >= self.next_t:
            self.next_t = t + random.uniform(0.6, 1.6)
            names = [n for n in STATUS_ICONS if n in STATUS_DUR]
            name = random.choice(names)
            dur = random.choice([3.0, 4.0, 6.0, 8.0, 12.0])
            self.active[name] = (t, dur)  # also refreshes one that's already up
        self.active = {n: (st, d) for n, (st, d) in self.active.items() if t - st < d}
        return [(n, d - (t - st), d) for n, (st, d) in self.active.items()]


class Buff:
    def __init__(self, name, t, order):
        self.name = name
        self.order = order       # display order: first come stays leftmost
        self.first = t           # this application's start (for learning its length)
        self.timer_start = t     # restarts when the buff is refreshed
        self.seen = t
        self.on_screen = False   # confirmed by the game's own icon (vs. only predicted from an artifact)
        self.ended = None
        self.refreshed = False
        self.gap = False
        self.remaining = -1.0
        self.frac = 1.0
        self.x = -999
        self.sig = None
        self.exact_rem = self.exact_dur = 0.0
        self.exact_t = None      # last time the game's own timer was read for this buff
        self.overran = False
        self.low = None          # lowest timer-border reading since the last (re)application
        self.top = 0

    @property
    def bad(self):
        return self.name in NEGATIVE


class BuffTracker:
    """Buffs from the row above the hotbar, identified against the official icons."""
    X0, STEP, W = 182, 85.4, 56
    Y0, Y1 = 15, 86
    MAX = 8

    def __init__(self, learned=None, links=None):
        self.learned = dict(learned) if isinstance(learned, dict) and "v" not in learned else {}
        self.links = dict(links or {})  # artifact -> buff, learned in play
        self.link_votes = {}
        self.uses = []
        self.dirty = False
        self.matcher = StatusMatcher()
        self.t0 = None
        self.t = 0.0
        self.active = {}         # name -> Buff
        self.votes = {}          # name -> (sightings, first sighting) for not-yet-shown buffs
        self.last_order = {}     # name -> (order, when it ended)
        self.ended = []
        self.counter = 0

    def export(self):
        return self.learned

    def duration(self, name):
        wiki = STATUS_DUR.get(name)
        real = self.learned.get(name)
        return max(real or 0, wiki or 0) or None

    @staticmethod
    def _sig(p):
        c = p[15:55, 8:48]
        return np.asarray(Image.fromarray(c).resize((6, 6), Image.BILINEAR), dtype=np.float32)

    @staticmethod
    def locate(big, x0=120):
        """Left x of each buff icon. Icons have straight vertical sides (black outline or a hard
        edge); pair sides one icon-width apart, then fill gaps one slot either side, since the row
        is evenly spaced. Rejects background texture and the arrow counter."""
        p = big[35:66, x0:].astype(np.int16)
        dark = (p.max(axis=2) < 50).mean(axis=0)
        g = np.zeros(p.shape[1])
        g[1:] = (np.abs(np.diff(p.mean(axis=2), axis=1)) > 40).mean(axis=0)
        side = (dark >= 0.75) | (g >= 0.8)
        weak = (dark >= 0.5) | (g >= 0.55)
        runs, i = [], 0
        while i < len(side):
            if side[i]:
                s0 = i
                while i < len(side) and side[i]:
                    i += 1
                if i - s0 <= 14:
                    runs.append((s0, i - 1))
            i += 1
        icons = []
        for ra in runs:
            for rb in runs:
                if 46 <= rb[1] - ra[0] <= 62:
                    if all(abs(ra[0] - o) > 60 for o in icons):
                        icons.append(ra[0])
                    break
        band = big[20:61, x0:].astype(np.int16).mean(axis=2)
        ed = np.zeros(band.shape[1])
        ed[1:] = (np.abs(np.diff(band, axis=1)) > 60).mean(axis=0)

        def score(x):
            if x < 3 or x + 59 >= len(ed):
                return -1.0
            if not (weak[x - 3:x + 4].any() or weak[x + 49:x + 59].any()):
                return -1.0
            return float(ed[x:x + 52].mean())

        changed = True
        while changed and len(icons) < 10:
            changed = False
            for x in list(icons):
                for sgn in (-1, 1):
                    sc, nx = max((score(x + sgn * st), x + sgn * st) for st in range(77, 91))
                    if sc >= 0.04 and all(abs(nx - o) > 60 for o in icons):
                        icons.append(nx)
                        changed = True
        return sorted(i + x0 for i in icons)

    @staticmethod
    def border_counts(big, x):
        """Lit pixels hugging the icon's black outline. The game draws the buff's remaining time
        as a coloured border that drains around the icon and snaps back when it's refreshed."""
        p = big[8:95, max(0, x - 6):x + 62].astype(np.int16)
        R, G, B = p[..., 0], p[..., 1], p[..., 2]
        dark = (p.max(axis=2) < 55)
        near = np.asarray(Image.fromarray((dark * 255).astype(np.uint8)).filter(ImageFilter.MaxFilter(7))) > 0
        green = (G > 100) & (G > R + 25) & (G > B + 5)
        orange = (R > 170) & (G > 70) & (G < 170) & (B < 90) & (R > G + 50)
        return int((green & near).sum()), int((orange & near).sum())

    def _get(self, name, t):
        b = self.active.get(name)
        if b is None:
            prev = self.last_order.get(name)
            if prev and t - prev[1] < 10:  # back within 10 s (e.g. a buff your weapon keeps applying): same spot
                order = prev[0]
            else:
                self.counter += 1
                order = self.counter
            b = Buff(name, t, order)
            self.active[name] = b
        return b

    def apply_exact(self, entries, t, learn=False):
        """Exact list from game memory (or test mode): [(name, remaining, duration)]."""
        self.t = t
        if self.t0 is None:
            self.t0 = t
        present = set()
        for name, rem, dur in entries:
            if learn and name not in self.active and name not in ARTIFACT_BUFF.values() and name not in self.links.values():
                ended_at = self.last_order.get(name, (0, -99))[1]
                for art, u in self.uses:
                    if t - u < 1.5 and not self.link_for(art) and u - ended_at > 3.0:
                        key = (art, name)
                        self.link_votes[key] = self.link_votes.get(key, 0) + 1
                        if self.link_votes[key] >= 2:
                            self.links[art] = name
                            self.dirty = True
                        break
            b = self._get(name, t)
            if b.exact_t is not None and rem > b.exact_rem + 0.25:
                b.first = t  # refreshed (the game reset its timer)
            b.exact_rem, b.exact_dur, b.exact_t = rem, dur, t
            b.seen = t
            b.on_screen = True
            present.add(name)
        for name, b in list(self.active.items()):
            if name not in present:
                left = b.exact_rem - (t - b.exact_t) if b.exact_t is not None else 0.0
                if left > 0.3 and t - b.seen < 0.2:
                    continue  # one missed read (list being updated) while time was left: don't end it yet
                b.ended = t  # the game removed it: fade out now
                self.last_order[name] = (b.order, t)
                del self.active[name]
                self.ended.append(b)

    def note_use(self, art, t):
        """An artifact was used. If we don't know which buff it gives, the first new buff that
        shows up right after is its buff (remembered in config)."""
        self.uses = [(a, u) for a, u in self.uses if t - u < 1.5] + [(art, t)]

    def link_for(self, art):
        return ARTIFACT_BUFF.get(art)

    def trigger(self, name, t):
        """An artifact that grants this buff was just used: show/refresh it right away."""
        b = self.active.get(name)
        if b is not None:
            b.timer_start, b.refreshed = t, True
        else:
            b = self._get(name, t)
        b.seen = t

    def feed(self, big, t):
        self.t = t
        if self.t0 is None:
            self.t0 = t
        for x in self.locate(big):
            if x < 2 or x + self.W + 2 > big.shape[1]:
                continue
            p = big[self.Y0:self.Y1, x - 2:x + self.W + 2]
            sig = self._sig(p)
            if float((sig.max(axis=2) - sig.min(axis=2)).mean()) < 60:
                continue  # washed-out fade in/out frame: colours aren't reliable yet
            name = None
            for b in self.active.values():  # same spot, same look as a moment ago: same buff
                if b.on_screen and abs(b.x - x) <= 14 and t - b.seen < 0.4 and b.sig is not None                         and float(np.abs(b.sig - sig).mean()) < 25:
                    name = b.name
                    break
            if name is None:
                expected = {n for n, b in self.active.items() if not b.on_screen or t - b.first < 2.0}
                name = self.matcher.identify(big, x, sig, t, expected)
            if name is None:
                continue  # not confidently an official status icon: don't show anything
            if name not in self.active:  # a new buff must be recognised twice before it shows
                n, t1 = self.votes.get(name, (0, t))
                if t - t1 > 0.6:
                    n, t1 = 0, t
                self.votes[name] = (n + 1, t1)
                if n + 1 < 2:
                    continue
            if name not in self.active and name not in ARTIFACT_BUFF.values() and name not in self.links.values():
                ended_at = self.last_order.get(name, (0, -99))[1]
                for art, u in self.uses:
                    # only a buff that wasn't up just before the use, seen after it twice, is that artifact's
                    if t - u < 1.5 and not self.link_for(art) and u - ended_at > 3.0:
                        key = (art, name)
                        self.link_votes[key] = self.link_votes.get(key, 0) + 1
                        if self.link_votes[key] >= 2:
                            self.links[art] = name
                            self.dirty = True
                        break
            b = self._get(name, t)
            if t - b.seen > 0.35:
                b.gap = True
            b.seen = t
            b.on_screen = True
            moved = abs(b.x - x) > 6
            b.x, b.sig = x, sig
            g, o = self.border_counts(big, x)
            lit = o if b.bad else g  # buffs have a green timer border, debuffs an orange one
            if b.low is None or moved:
                b.low, b.top = lit, lit  # (icon slid over: re-baseline)
            else:
                b.top = max(b.top, lit)
                if lit - b.low >= max(12, 0.06 * b.top) and t - b.timer_start > 0.3:
                    b.timer_start, b.refreshed = t, True  # border climbed back up: refreshed
                    b.low = lit
                else:
                    b.low = min(b.low, lit)

    def tick(self, t):
        self.t = t
        for name, b in list(self.active.items()):
            if b.exact_t is not None and t - b.exact_t < 1.5:
                if b.exact_rem < 0:
                    b.remaining, b.frac = -1.0, 1.0
                else:
                    b.remaining = max(0.0, b.exact_rem - (t - b.exact_t))
                    b.frac = b.remaining / b.exact_dur if b.exact_dur > 0 else 1.0
                continue
            dur = self.duration(name)
            since = t - b.seen
            if dur:
                if t - b.timer_start > dur + 0.15 and since < 0.15:
                    b.timer_start = t - 0.15  # still showing past its time: refreshed, or it simply lasts longer
                    b.overran = True
                b.remaining = max(0.0, dur - (t - b.timer_start))
                b.frac = b.remaining / dur
                over = since > 0.6 and (b.remaining <= 0.25 or since > 2.0)
            else:
                b.remaining, b.frac = -1.0, 1.0
                over = since > 0.6
            if over:
                self._learn(b)
                b.ended = t
                self.last_order[name] = (b.order, t)
                del self.active[name]
                self.ended.append(b)
        self.ended = [b for b in self.ended if t - b.ended < 0.35]

    def _learn(self, b):
        life = b.seen - b.first
        if b.refreshed or b.gap or not b.on_screen or b.first - self.t0 < 0.5:
            return
        wiki = STATUS_DUR.get(b.name)
        if wiki and not (0.8 * wiki <= life <= 3.0 * wiki):
            return
        if life > (self.learned.get(b.name) or 0) + 0.05:
            self.learned[b.name] = round(life, 2)
            self.dirty = True

    def visible(self):
        out = [(b, 1.0) for b in self.active.values()]
        out += [(b, max(0.0, 1 - (self.t - b.ended) / 0.35)) for b in self.ended]
        return sorted(out, key=lambda ba: ba[0].order)

    def cover_image(self, big):
        """Terrain-coloured patch that hides the game's own buff row (shown in a window our own
        screen capture can't see, so the icons stay readable). The arrow counter is left alone."""
        y0, y1, x0, x1 = 6, 98, 150, 1000
        a = big.astype(np.float32)
        top = a[y0 - 4:y0].mean(axis=0)
        bot = a[y1:y1 + 4].mean(axis=0)
        k = np.linspace(0, 1, y1 - y0, dtype=np.float32)[:, None, None]
        fill = top[None] * (1 - k) + bot[None] * k
        img = Image.fromarray(fill[:, x0:x1].astype(np.uint8)).filter(ImageFilter.GaussianBlur(6)).convert("RGBA")
        h, w = y1 - y0, x1 - x0
        m = np.ones((h, w), np.float32)
        ramp = np.linspace(0, 1, 10, dtype=np.float32)
        m[:10] *= ramp[:, None]
        m[-10:] *= ramp[::-1, None]
        m[:, :10] *= ramp[None]
        m[:, -10:] *= ramp[None, ::-1]
        cx0, cx1, cy0 = 498 - x0, 622 - x0, 62 - y0  # arrow counter box stays visible
        m[cy0:, max(0, cx0):cx1] = 0
        img.putalpha(Image.fromarray((m * 255).astype(np.uint8)))
        return img, x0, y0


class ScreenReader:
    """Grabs the hotbar plus the buff row above it.

    grab() returns (big, crop): big has its origin PAD px above the hotbar crop
    origin (OX, OY); crop = big[PAD:] is in the hotbar crop coordinates used by SLOTS.
    """
    PAD = 60
    WIDTH = 1000

    def __init__(self, hud=1.0):
        self.W = user32.GetSystemMetrics(0)
        self.H = user32.GetSystemMetrics(1)
        self.set_hud(hud)

    def set_hud(self, hud):
        """hud = in-game HUD Size relative to Medium (Small is ~0.74)."""
        self.hud = hud
        self.s = self.H / REF_H * hud
        self.bbox = (self.sx(OX), self.sy(OY - self.PAD), self.sx(OX + self.WIDTH), self.sy(OY + 250))

    def sx(self, x):
        return int(round(self.W / 2 + (x - REF_W / 2) * self.s))

    def sy(self, y):
        return int(round(self.H - (REF_H - y) * self.s))

    def grab(self):
        img = ImageGrab.grab(bbox=self.bbox)
        size = (self.WIDTH, 250 + self.PAD)
        if img.size != size:
            img = img.resize(size, Image.BILINEAR)
        big = np.asarray(img.convert("RGB"))
        return big, big[self.PAD:]

    def calibrate(self):
        """Find the HUD scale by looking for the white 1/2/3 keybind badges. Returns True if found."""
        base = self.H / REF_H
        left, top = int(self.W / 2 - 900 * base), int(self.H - 520 * base)
        shot = np.asarray(ImageGrab.grab(bbox=(left, top, int(self.W / 2 + 900 * base), self.H)).convert("RGB"))
        white = shot.min(axis=2) > 190
        best, best_score = None, 0.0
        for hud in np.arange(0.55, 1.6, 0.005):
            s = base * hud
            score = 0.0
            for x0, y0, x1, y1 in BADGES:
                sx0 = int(round(self.W / 2 + (OX + x0 - REF_W / 2) * s)) - left
                sx1 = int(round(self.W / 2 + (OX + x1 - REF_W / 2) * s)) - left
                sy0 = int(round(self.H - (REF_H - OY - y0) * s)) - top
                sy1 = int(round(self.H - (REF_H - OY - y1) * s)) - top
                if sx0 < 0 or sy0 < 0 or sx1 > white.shape[1] or sy1 > white.shape[0] or sx1 <= sx0 or sy1 <= sy0:
                    score = 0
                    break
                f = white[sy0:sy1, sx0:sx1].mean()
                if f < 0.35:
                    score = 0
                    break
                score += f
            if score > best_score:
                best, best_score = float(hud), score
        if best is None:
            return False
        self.set_hud(round(best, 3))
        return True

# --------------------------------------------------------------------------
# Drawing (WeakAuras look)
# --------------------------------------------------------------------------
def load_font(size):
    for name in ("seguibl.ttf", "segoeuib.ttf", "arialbd.ttf"):
        try:
            return ImageFont.truetype(os.path.join(os.environ.get("WINDIR", "C:/Windows"), "Fonts", name), size)
        except OSError:
            pass
    return ImageFont.load_default()


def _fmt_time(r):
    if r >= 60:
        return f"{int(r // 60) + 1}m"
    return f"{max(0.0, r):.1f}"  # tenths all the way down


def _glow_ring(size, margin, color, width, blur, radius=6):
    img = Image.new("RGBA", (size + 2 * margin, size + 2 * margin), (0, 0, 0, 0))
    m = margin
    ImageDraw.Draw(img).rounded_rectangle((m - 5, m - 5, m + size + 4, m + size + 4), radius,
                                          outline=color + (255,), width=width)
    return img.filter(ImageFilter.GaussianBlur(blur))


def _with_alpha(img, a):
    out = img.copy()
    out.putalpha(out.getchannel("A").point(lambda v: int(v * max(0.0, min(1.0, a)))))
    return out


GOLD, GREEN, RED, CYAN = (255, 200, 40), (70, 255, 110), (255, 60, 50), (70, 200, 255)


class Renderer:
    MARGIN = 18  # room for the glow
    GAP = 6      # vertical gap between rows

    def __init__(self, cfg):
        self.cfg = cfg
        self.size = cfg["icon_size"]
        self.bsize = cfg["buff_icon_size"]
        self.font_big = load_font(int(self.size * 0.46))
        self.font_mid = load_font(int(self.size * 0.36))
        self.font_key = load_font(int(self.size * 0.22))
        self.font_bbig = load_font(int(self.bsize * 0.42))
        self.font_bmid = load_font(int(self.bsize * 0.32))
        # countdowns use the biggest size that fits the square ("15.4" needs more room than "4.2")
        self.time_fonts = {"slot": [load_font(int(self.size * k)) for k in (0.46, 0.40, 0.34, 0.29, 0.25)],
                           "buff": [load_font(int(self.bsize * k)) for k in (0.42, 0.37, 0.32, 0.27, 0.23)]}
        self._tf_cache = {}
        self.font_bar = load_font(int(cfg["bar_height"] * 0.68))
        s, m = self.size, self.MARGIN
        self.glow_gold = _glow_ring(s, m, GOLD, 7, 5)
        self.glow_green = _glow_ring(s, m, GREEN, 8, 6)
        self.bglow = {"buff": _glow_ring(self.bsize, m, GREEN, 9, 6), "debuff": _glow_ring(self.bsize, m, RED, 9, 6)}
        self._placeholder = {}
        self._tiles = {}
        self._anim = {}
        self._panel_t = {}
        self._live_all = set()

    # ---------------------------------------------------------------- pieces
    def placeholder(self, label):
        return Image.new("RGBA", (1, 1), (0, 0, 0, 0))  # plain tile until the real icon is captured

    def icon_img(self, src, size, grey, fill=0.86):
        """Cut-out icon centred on a dark tile; pixel art scaled nearest-neighbour so it stays crisp."""
        tile = Image.new("RGBA", (size, size), (0, 0, 0, 255))
        tile.alpha_composite(self.tile_bg(size))
        src = src.convert("RGBA")
        k = fill * size / max(src.width, src.height)
        w, h = max(1, int(src.width * k)), max(1, int(src.height * k))
        if k >= 2:  # whole-number zoom keeps pixels square
            w, h = src.width * int(k), src.height * int(k)
        icon = src.resize((w, h), Image.NEAREST)
        if grey:
            g = ImageOps.grayscale(icon.convert("RGB")).convert("RGBA")
            g.putalpha(icon.getchannel("A"))
            icon = Image.blend(icon, g, 0.75)
        tile.alpha_composite(icon, ((size - w) // 2, (size - h) // 2))
        return tile

    def item_tile(self, tr, size, grey):
        src = None
        if tr.spec["key"] == "potion" and POTION_ICON is not None:
            src = POTION_ICON
        elif tr.art and tr.art in ARTIFACT_ICONS:
            src = ARTIFACT_ICONS[tr.art]
        elif tr.icon is not None:
            src = tr.icon
        if src is None:
            return self.icon_img(self.placeholder(""), size, grey)
        tile = Image.new("RGBA", (size, size), (0, 0, 0, 255))
        tile.alpha_composite(self.tile_bg(size))
        icon = src.crop(src.getbbox())
        k = 0.94 * size / max(icon.width, icon.height)
        icon = icon.resize((max(1, int(icon.width * k)), max(1, int(icon.height * k))), Image.LANCZOS)
        tile.alpha_composite(icon, ((size - icon.width) // 2, (size - icon.height) // 2))
        if grey:
            g = ImageOps.grayscale(tile.convert("RGB")).convert("RGBA")
            tile = Image.blend(tile, g, 0.7)
        return tile

    def tile_bg(self, size):
        if size not in self._tiles:
            a = np.asarray(Image.linear_gradient("L").resize((size, size)), dtype=np.float32)[..., None] / 255.0
            rgb = (np.array((52, 56, 66)) * (1 - a) + np.array((20, 22, 28)) * a).astype(np.uint8)
            self._tiles[size] = Image.fromarray(np.dstack([rgb, np.full((size, size), 255, np.uint8)]), "RGBA")
        return self._tiles[size]

    @staticmethod
    def swipe(size, frac, color=(0, 0, 0, 170)):
        """Clock swipe covering the remaining part, sweeping clockwise (WoW cooldown style)."""
        sw = Image.new("RGBA", (size, size), (0, 0, 0, 0))
        if frac > 0.001:
            sd = ImageDraw.Draw(sw)
            start = -90 + (1 - frac) * 360
            sd.pieslice((-size * 0.25, -size * 0.25, size * 1.25, size * 1.25), start, 270, fill=color)
            ang = math.radians(start)
            c = size / 2
            sd.line((c, c, c + math.cos(ang) * size, c + math.sin(ang) * size), fill=(255, 255, 255, 90), width=2)
        return sw

    def time_font(self, txt, kind):
        key = (len(txt), kind)  # same number of digits -> same font, so the size doesn't jitter
        if key not in self._tf_cache:
            box = (self.size if kind == "slot" else self.bsize) * 0.94
            fonts = self.time_fonts[kind]
            probe = "8" * (len(txt) - 1) + "." if "." in txt else "8" * len(txt)
            self._tf_cache[key] = next((f for f in fonts if f.getlength(probe) + 6 <= box), fonts[-1])
        return self._tf_cache[key]

    def text(self, img, xy, txt, font, col, stroke=3, anchor="mm"):
        ImageDraw.Draw(img).text(xy, txt, font=font, fill=col + (255,), anchor=anchor,
                                 stroke_width=stroke, stroke_fill=(0, 0, 0, 255))

    # ------------------------------------------------------------ cooldowns
    @staticmethod
    def ring_color(frac):
        """Remaining fraction -> green (full) through yellow to red (almost done)."""
        if frac > 0.5:
            k = (frac - 0.5) / 0.5
            a, b = (255, 210, 40), (60, 230, 90)
        else:
            k = frac / 0.5
            a, b = (235, 45, 35), (255, 210, 40)
        return tuple(int(a[i] + (b[i] - a[i]) * k) for i in range(3))

    def circle_aura(self, tr, t, since_ready, glow_t):
        """Round artifact icon; cooldown shown as a ring around the outside that runs down
        clockwise from full to nothing, shifting green -> yellow -> red."""
        s, m = self.size, self.MARGIN
        W = s + 2 * m
        SS = 4  # draw the ring and mask supersampled so the circles are smooth
        img = Image.new("RGBA", (W, W), (0, 0, 0, 0))
        c = W / 2
        r_icon = s / 2 - 3
        ring_w = 6
        r_ring = r_icon + 3 + ring_w / 2 + 1

        def circ(r):
            return (int((c - r) * SS), int((c - r) * SS), int((c + r) * SS), int((c + r) * SS))

        glow = None
        if tr.active:
            glow = (GREEN, 0.75 + 0.25 * math.sin((t - tr.active_since) * 9))
        elif not tr.on_cd and since_ready < glow_t:
            p = since_ready / glow_t
            glow = (GOLD, (0.65 + 0.35 * math.sin(since_ready * 14)) * (1 - p ** 3))
        if glow:
            g = Image.new("RGBA", (W, W), (0, 0, 0, 0))
            ImageDraw.Draw(g).ellipse((c - r_ring - 3, c - r_ring - 3, c + r_ring + 3, c + r_ring + 3),
                                      outline=glow[0] + (255,), width=8)
            img.alpha_composite(_with_alpha(g.filter(ImageFilter.GaussianBlur(5)), glow[1]))

        # icon, masked to a circle, with a dark rim
        hi = Image.new("RGBA", (W * SS, W * SS), (0, 0, 0, 0))
        hd = ImageDraw.Draw(hi)
        hd.ellipse(circ(r_icon + 3), fill=(GREEN if tr.active else (10, 10, 12)) + (255,))
        if tr.on_cd:  # track for the ring
            hd.ellipse(circ(r_ring + ring_w / 2), outline=(0, 0, 0, 150), width=int((ring_w + 2) * SS))
            if tr.frac > 0.002:
                col = GREEN if tr.active else self.ring_color(tr.frac)
                hd.arc(circ(r_ring), -90, -90 + 360 * tr.frac, fill=col + (255,), width=int(ring_w * SS))
        img.alpha_composite(hi.resize((W, W), Image.LANCZOS))

        d = int(2 * r_icon)
        tile = self.item_tile(tr, d, tr.on_cd and not tr.active)
        mask = Image.new("L", (d * SS, d * SS), 0)
        ImageDraw.Draw(mask).ellipse((0, 0, d * SS - 1, d * SS - 1), fill=255)
        tile.putalpha(mask.resize((d, d), Image.LANCZOS))
        img.alpha_composite(tile, (int(c - d / 2), int(c - d / 2)))
        if tr.on_cd:
            if tr.remaining >= 0:
                r = tr.remaining
                f = self.time_font(_fmt_time(r), "slot")
                col = GREEN if tr.active else ((255, 255, 255) if r > 5 else RED)
                self.text(img, (c, c), _fmt_time(r), f, col, max(2, s // 22))
        elif not tr.active and since_ready < 0.25:
            fl = Image.new("RGBA", (d, d), (255, 255, 255, int(170 * (1 - since_ready / 0.25))))
            fl.putalpha(ImageChops.multiply(fl.getchannel("A"), mask.resize((d, d), Image.LANCZOS)))
            img.alpha_composite(fl, (int(c - d / 2), int(c - d / 2)))
        return img

    def aura(self, tr, t, unlocked):
        s, m = self.size, self.MARGIN
        img = Image.new("RGBA", (s + 2 * m, s + 2 * m), (0, 0, 0, 0))
        since_ready = t - tr.ready_at
        glow_t = self.cfg["ready_glow_seconds"]
        if (not tr.on_cd and not tr.active and self.cfg["hide_when_ready"] and since_ready > glow_t
                and not unlocked):
            return None
        if tr.spec["key"] in self.cfg["round_slots"]:
            return self.circle_aura(tr, t, since_ready, glow_t)
        bt = getattr(self, "bufftr", None)
        buff = None
        if bt is not None and tr.art and not getattr(self, "test_mode", False):
            name = bt.link_for(tr.art)
            buff = bt.active.get(name) if name else None
            if buff is not None and buff.remaining < 0:
                buff = None
            # only this artifact's own buff: it must have started/refreshed after the artifact was
            # used (the axe's random Strength must not show up on the Battle Banner square)
            if buff is not None:
                applied = max(buff.first, buff.timer_start)
                if not (tr.started_at - 0.5 <= applied <= tr.started_at + 15.0):
                    buff = None
        if buff is not None:
            # one countdown only: while the artifact's buff runs the square counts the buff down;
            # its (shorter) cooldown shows as a dark sweep over the icon, not a second timer
            return self.buff_square(tr, buff, t)
        return self._cooldown_square(tr, t, since_ready, glow_t)

    def _cooldown_square(self, tr, t, since_ready, glow_t):
        s, m = self.size, self.MARGIN
        img = Image.new("RGBA", (s + 2 * m, s + 2 * m), (0, 0, 0, 0))
        if tr.active:
            # effect running: strong pulsing green glow, full-colour icon
            a = 0.75 + 0.25 * math.sin((t - tr.active_since) * 9)
            img.alpha_composite(_with_alpha(self.glow_green, a))
        d = ImageDraw.Draw(img)
        # while cooling down the whole square shifts green -> yellow -> red as it runs out
        cd_col = self.ring_color(tr.frac) if (tr.on_cd and not tr.active) else None
        border = GREEN if tr.active else (cd_col or (0, 0, 0))
        d.rectangle((m - 4, m - 4, m + s + 3, m + s + 3), fill=border + (255,))
        img.paste(self.item_tile(tr, s, tr.on_cd and not tr.active), (m, m))
        if tr.on_cd:
            if cd_col:
                img.alpha_composite(Image.new("RGBA", (s, s), cd_col + (95,)), (m, m))
            else:
                img.alpha_composite(self.swipe(s, tr.frac, (0, 60, 0, 120)), (m, m))
            if tr.remaining >= 0:
                r = tr.remaining
                f = self.time_font(_fmt_time(r), "slot")
                c = GREEN if tr.active else (255, 255, 255)
                self.text(img, (m + s / 2, m + s / 2), _fmt_time(r), f, c, max(2, s // 22))
        elif not tr.active and since_ready < glow_t:
            # proc glow: golden pulse + quick white "bling" flash
            p = since_ready / glow_t
            img.alpha_composite(_with_alpha(self.glow_gold, (0.65 + 0.35 * math.sin(since_ready * 14)) * (1 - p ** 3)))
            if since_ready < 0.25:
                img.alpha_composite(Image.new("RGBA", (s, s), (255, 255, 255, int(170 * (1 - since_ready / 0.25)))), (m, m))
        return img

    def buff_square(self, tr, b, t):
        """Artifact square while its buff is running: full-colour icon, glowing, whole square
        shifting green -> yellow -> red with the buff's time left."""
        s, m = self.size, self.MARGIN
        img = Image.new("RGBA", (s + 2 * m, s + 2 * m), (0, 0, 0, 0))
        col = self.ring_color(b.frac)
        g = _glow_ring(s, m, col, 8, 6)
        img.alpha_composite(_with_alpha(g, 0.75 + 0.25 * math.sin(t * 6)))
        ImageDraw.Draw(img).rectangle((m - 4, m - 4, m + s + 3, m + s + 3), fill=col + (255,))
        img.paste(self.item_tile(tr, s, False), (m, m))
        img.alpha_composite(Image.new("RGBA", (s, s), col + (70,)), (m, m))
        if tr.on_cd and tr.frac > 0.002:
            img.alpha_composite(self.swipe(s, tr.frac, (0, 0, 0, 120)), (m, m))
        r = b.remaining
        self.text(img, (m + s / 2, m + s / 2), _fmt_time(r), self.time_font(_fmt_time(r), "slot"),
                  (255, 255, 255), max(2, s // 22))
        return img

    # ---------------------------------------------------------------- buffs
    def buff_aura(self, b, t, alpha):
        icon = STATUS_ICONS.get(b.name)
        if icon is None:
            return None
        s, m = self.bsize, self.MARGIN
        img = Image.new("RGBA", (s + 2 * m, s + 2 * m), (0, 0, 0, 0))
        age = t - b.first
        col = RED if b.bad else GREEN
        a = 0.6 + 0.15 * math.sin(t * 5) if age > 0.5 else 1.0
        img.alpha_composite(_with_alpha(self.bglow["debuff" if b.bad else "buff"], a))
        d = ImageDraw.Draw(img)
        d.rectangle((m - 2, m - 2, m + s + 1, m + s + 1), fill=(10, 10, 12, 255))
        ic = icon.crop(icon.getbbox())
        rs = Image.NEAREST if s % ic.width == 0 else Image.LANCZOS
        img.alpha_composite(ic.resize((s, s), rs), (m, m))
        d = ImageDraw.Draw(img)
        d.rectangle((m - 2, m - 2, m + s + 1, m + s + 1), outline=col + (255,), width=2)
        if b.remaining >= 0:  # draining bar under the icon + countdown, green -> red
            bh = max(5, s // 12)
            c = self.ring_color(b.frac)
            by = m + s + 3
            d.rectangle((m - 1, by - 1, m + s, by + bh), fill=(0, 0, 0, 220))
            if b.frac > 0:
                d.rectangle((m, by, m + int((s - 1) * b.frac), by + bh - 1), fill=c + (255,))
            r = b.remaining
            self.text(img, (m + s / 2, m + s / 2), _fmt_time(r),
                      self.time_font(_fmt_time(r), "buff"),
                      (255, 255, 255) if r > 3 else RED, max(2, s // 20))
        if age < 0.35:  # quick pop on arrival
            p = age / 0.35
            ring = Image.new("RGBA", img.size, (0, 0, 0, 0))
            e = int(m * p)
            ImageDraw.Draw(ring).rectangle((m - e, m - e, m + s + e - 1, m + s + e - 1),
                                           outline=(255, 255, 255, int(220 * (1 - p))), width=3)
            img.alpha_composite(ring)
        if alpha < 0.999:
            img = _with_alpha(img, alpha)
        return img

    # ----------------------------------------------------------------- bars
    def bar(self, width, frac, color, label, value, t, alert=False):
        h, m = self.cfg["bar_height"], self.MARGIN
        img = Image.new("RGBA", (width + 2 * m, h + 2 * m), (0, 0, 0, 0))
        if alert:  # pulsing red glow around the bar
            g = Image.new("RGBA", img.size, (0, 0, 0, 0))
            ImageDraw.Draw(g).rectangle((m - 5, m - 5, m + width + 4, m + h + 4), outline=RED + (255,), width=7)
            img.alpha_composite(_with_alpha(g.filter(ImageFilter.GaussianBlur(5)), 0.6 + 0.4 * math.sin(t * 10)))
        d = ImageDraw.Draw(img)
        d.rectangle((m - 2, m - 2, m + width + 1, m + h + 1), fill=(0, 0, 0, 255))
        d.rectangle((m, m, m + width - 1, m + h - 1), fill=(25, 25, 30, 210))
        if frac is not None and frac > 0:
            fw = max(1, int(width * min(1.0, frac)))
            fill = Image.new("RGBA", (fw, h), color + (255,))
            shade = Image.linear_gradient("L").resize((fw, h)).point(lambda v: 255 - v // 3)  # top-lit sheen
            fill = Image.composite(fill, Image.new("RGBA", (fw, h), tuple(c // 2 for c in color) + (255,)), shade)
            img.alpha_composite(fill, (m, m))
        # no label text: colour says which bar it is
        self.text(img, (m + width - 6, m + h / 2), value, self.font_bar, (255, 255, 255), 2, "rm")
        return img

    def health_color(self, hp):
        if hp > 0.5:
            return (60, 210, 80)
        if hp > 0.3:
            return (230, 200, 40)
        return (230, 50, 40)

    # ---------------------------------------------------------------- panels
    PANEL_COLORS = {"attack": (230, 80, 60), "defense": (70, 150, 255), "debuffs": (190, 80, 230),
                    "cooldowns": (230, 200, 60), "health": (70, 210, 90), "souls": (70, 200, 255)}

    def _frame(self, img, name):
        """Edit mode: tinted box hugging the panel's content (not its glow margin)."""
        col = self.PANEL_COLORS.get(name, (200, 200, 200))
        m, pad = self.MARGIN, 9
        d = ImageDraw.Draw(img)
        d.rectangle((m - pad, m - pad, img.width - m + pad - 1, img.height - m + pad - 1),
                    fill=col + (45,), outline=col + (230,), width=2)

    def panel_buffs(self, name, buffs, t, edit, order):
        """One buff panel. Returns (image, cells) with cells = [(buff name, (x0, y0, x1, y1))]."""
        cfg, m, sp, bs = self.cfg, self.MARGIN, self.cfg["spacing"], self.bsize
        vertical = cfg["panels"][name]["dir"] == "y"
        rank = {n: i for i, n in enumerate(order)}
        items = sorted(buffs, key=lambda ba: (rank.get(ba[0].name, 999), ba[0].order))
        names_live = {b.name for b, _ in items}
        entries = [(b, a) for b, a in items]
        if edit:  # show every buff of this panel so any of them can be reordered or moved
            for n in order:
                if n not in names_live and n in STATUS_ICONS:
                    entries.append((n, 0.4))
            entries.sort(key=lambda e: rank.get(e[0].name if isinstance(e[0], Buff) else e[0], 999))
        n = max(1, len(entries) if edit else cfg["max_buffs"])
        cell = bs + sp + (bs // 8 if not vertical else bs // 6)
        W = (cell * n - sp if not vertical else bs) + 2 * m
        H = (bs + bs // 6 + 6 if not vertical else cell * n - sp) + 2 * m
        out = Image.new("RGBA", (W, H), (0, 0, 0, 0))
        if edit:
            self._frame(out, name)
        cells = []
        dt = min(0.1, t - self._panel_t.get(name, t))
        self._panel_t[name] = t
        live_ids = set()
        for i, (b, alpha) in enumerate(entries):
            tx, ty = (m + i * cell, m) if not vertical else (m, m + i * cell)
            if isinstance(b, Buff):
                key = id(b)
                live_ids.add(key)
                st = self._anim.setdefault(key, {"x": float(tx), "y": float(ty), "born": t})
                k = min(1.0, dt * 14)
                st["x"] += (tx - st["x"]) * k
                st["y"] += (ty - st["y"]) * k
                fade_in = min(1.0, (t - st["born"]) / 0.12)
                a = self.buff_aura(b, t, alpha * fade_in)
                if a is not None:
                    out.alpha_composite(a, (int(st["x"]) - m, int(st["y"]) - m))
                cells.append((b.name, (tx, ty, tx + bs, ty + bs)))
            else:  # edit-mode preview of a buff that isn't up right now
                ic = STATUS_ICONS[b]
                tile = ic.crop(ic.getbbox()).resize((bs, bs), Image.LANCZOS)
                out.alpha_composite(_with_alpha(tile, alpha), (tx, ty))
                cells.append((b, (tx, ty, tx + bs, ty + bs)))
        self._anim = {k: v for k, v in self._anim.items() if k in live_ids or not isinstance(k, int)
                      or k in self._live_all}
        return out, cells

    def panel_cooldowns(self, trackers, t, edit):
        m, s, sp = self.MARGIN, self.size, self.cfg["spacing"] + 4
        vertical = self.cfg["panels"]["cooldowns"]["dir"] == "y"
        n = len(trackers)
        W = ((s + sp) * n - sp if not vertical else s) + 2 * m
        H = (s if not vertical else (s + sp) * n - sp) + 2 * m
        out = Image.new("RGBA", (W, H), (0, 0, 0, 0))
        if edit:
            self._frame(out, "cooldowns")
        for i, tr in enumerate(trackers):
            a = self.aura(tr, t, edit)
            if a is not None:
                x, y = (i * (s + sp), 0) if not vertical else (0, i * (s + sp))
                out.alpha_composite(a, (x, y))
        return out

    def panel_bar(self, kind, vitals, t, edit):
        m = self.MARGIN
        w = self.cfg["bar_width"] or (self.size + self.cfg["spacing"] + 4) * 4 - self.cfg["spacing"] - 4
        if kind == "health":
            hp = vitals.health if vitals.health is not None else 1.0
            img = self.bar(w, hp, self.health_color(hp), "", f"{int(round(hp * 100))}%", t,
                           alert=vitals.health is not None and hp <= self.cfg["low_health_alert"])
        else:
            val = str(vitals.souls) if vitals.souls is not None else ""
            img = self.bar(w, vitals.soul_frac, CYAN, "", val, t)
        if edit:
            out = Image.new("RGBA", img.size, (0, 0, 0, 0))
            self._frame(out, kind)
            out.alpha_composite(img)
            return out
        return img

    # ---------------------------------------------------------------- F8 menu
    PANEL_TITLES = {"attack": "Attack buffs", "defense": "Defense buffs", "debuffs": "Debuffs",
                    "cooldowns": "Cooldowns", "health": "Health", "souls": "Souls"}

    def menu_image(self, panels, snap, hover, grid=0, test=False, live=False, lay=None):
        """Edit-mode options window. Returns (image, [(button id, rect)])."""
        f_title, f_row = load_font(17), load_font(15)
        W, rh, top = 440, 34, 40
        order = ["attack", "defense", "debuffs", "cooldowns", "health", "souls"]
        H = top + rh * len(order) + 140
        img = Image.new("RGBA", (W, H), (18, 20, 26, 236))
        d = ImageDraw.Draw(img)
        d.rectangle((0, 0, W - 1, H - 1), outline=(90, 95, 110, 255), width=2)
        d.rectangle((2, 2, W - 3, top - 6), fill=(34, 38, 48, 255))
        d.text((14, (top - 4) // 2), "Auras layout", font=f_title, fill=(235, 235, 240, 255), anchor="lm")
        buttons = [(("drag",), (0, 0, W, top - 4))]

        def button(bid, rect, label, on=None, accent=(70, 150, 255)):
            x0, y0, x1, y1 = rect
            hot = hover == bid
            base = (60, 64, 76) if on is None else (accent if on else (52, 55, 64))
            if hot:
                base = tuple(min(255, c + 25) for c in base)
            d.rounded_rectangle(rect, 6, fill=base + (255,))
            d.text(((x0 + x1) / 2, (y0 + y1) / 2), label, font=f_row, fill=(245, 245, 250, 255), anchor="mm")
            buttons.append((bid, rect))

        for i, k in enumerate(order):
            pc = panels[k]
            y = top + i * rh
            col = self.PANEL_COLORS[k]
            d.rounded_rectangle((14, y + 10, 28, y + 24), 3, fill=col + (255,))
            d.text((38, y + 17), self.PANEL_TITLES[k], font=f_row, fill=(225, 225, 232, 255), anchor="lm")
            shown = pc.get("show", True)
            button(("show", k), (176, y + 4, 246, y + 30), "Shown" if shown else "Hidden", on=shown,
                   accent=(60, 150, 90))
            vertical = pc.get("dir", "x") == "y"
            button(("dir", k), (254, y + 4, 316, y + 30), "Column" if vertical else "Row")
            button(("size-", k), (324, y + 4, 352, y + 30), "-")
            d.text((377, y + 17), f"{int(round(pc.get('scale', 1.0) * 100))}%", font=f_row,
                   fill=(225, 225, 232, 255), anchor="mm")
            button(("size+", k), (402, y + 4, 430, y + 30), "+")
        y = top + rh * len(order) + 12
        button(("snap",), (14, y, 140, y + 32), "Snap together" if snap else "Free move", on=snap)
        button(("grid",), (148, y, 240, y + 32), f"Grid {grid}px" if grid else "No grid", on=bool(grid))
        button(("reset",), (248, y, 340, y + 32), "Reset")
        button(("done",), (348, y, 430, y + 32), "Done", on=True, accent=(60, 150, 90))
        y += 42
        button(("test",), (14, y, 150, y + 32), "Test buffs: on" if test else "Test buffs: off", on=test,
               accent=(200, 120, 40))
        d.ellipse((168, y + 11, 178, y + 21), fill=((70, 220, 110) if live else (220, 170, 60)) + (255,))
        d.text((186, y + 16), "Exact timers (game data)" if live else "Screen reading", font=f_row,
               fill=(200, 200, 210, 255), anchor="lm")
        # layouts: Save, then click a slot to store the current layout there; click a slot to load it
        lay = lay or {"filled": set(), "save": False, "current": None, "flash": None}
        y += 42
        d.text((14, y + 16), "Layouts", font=f_row, fill=(225, 225, 232, 255), anchor="lm")
        for i, slot in enumerate(LAYOUT_SLOTS):
            x0 = 82 + i * 42
            filled = slot in lay["filled"]
            if lay["save"]:
                on, accent = True, (200, 120, 40)  # waiting for a slot to save into
            else:
                on, accent = (lay["current"] == slot) if filled else None, (70, 150, 255)
            if filled or lay["save"]:
                button(("lslot", slot), (x0, y, x0 + 36, y + 32), slot, on=on, accent=accent)
            else:  # empty slot: outline + dim number (Save, then click it to fill it)
                rect = (x0, y, x0 + 36, y + 32)
                d.rounded_rectangle(rect, 6, fill=(28, 30, 38, 255), outline=(70, 74, 88, 255), width=1)
                d.text((x0 + 18, y + 16), slot, font=f_row, fill=(110, 114, 126, 255), anchor="mm")
                buttons.append((("lslot", slot), rect))
            if lay["flash"] == slot:
                d.rounded_rectangle((x0, y, x0 + 36, y + 32), 6, outline=(255, 255, 255, 255), width=2)
        button(("lsave",), (254, y, 330, y + 32), "Pick slot" if lay["save"] else "Save", on=lay["save"],
               accent=(200, 120, 40))
        button(("ldefault",), (338, y, 430, y + 32), "Make default", on=lay["flash"] == "Default" or None,
               accent=(60, 150, 90))
        return img, buttons

    # ---------------------------------------------------------------- group
    def group(self, trackers, buffs, vitals, t, unlocked):
        """Fixed-size layout (nothing jumps when buffs come and go). Buffs fill left to right in
        the order they arrived; when one ends the rest glide over instead of snapping."""
        cfg, m = self.cfg, self.MARGIN
        s, sp, bs = self.size, cfg["spacing"], self.bsize
        cd_w = (s + sp) * len(trackers) - sp
        max_buffs = cfg["max_buffs"]
        buff_w = (bs + sp) * max_buffs - sp
        inner_w = max(cd_w, buff_w if cfg["show_buffs"] else 0)
        W = inner_w + 2 * m
        bar_h = cfg["bar_height"]
        rows_h = []
        if cfg["show_buffs"]:
            rows_h.append(("buffs", bs + bar_h // 2 + 6))
        rows_h.append(("cd", s))
        if cfg["show_health_bar"]:
            rows_h.append(("hp", bar_h))
        if cfg["show_soul_bar"]:
            rows_h.append(("souls", bar_h))
        H = sum(h for _, h in rows_h) + self.GAP * (len(rows_h) - 1) + 2 * m
        out = Image.new("RGBA", (W, H), (0, 0, 0, 0))
        if unlocked:
            ImageDraw.Draw(out).rectangle((2, 2, W - 3, H - 3), fill=(40, 200, 90, 60), outline=(60, 255, 120, 220), width=2)
        dt = min(0.1, t - getattr(self, "_last_t", t))
        self._last_t = t
        left = m + (inner_w - cd_w) // 2  # buffs start where the cooldown row starts
        y = m
        for kind, h in rows_h:
            if kind == "buffs":
                slot = 0
                for b, alpha in buffs:
                    target = left + slot * (bs + sp)
                    if b.ended is None:
                        slot += 1
                    st = self._anim.setdefault(id(b), {"x": float(target), "born": t})
                    st["x"] += (target - st["x"]) * min(1.0, dt * 14)  # glide
                    fade_in = min(1.0, (t - st["born"]) / 0.12)
                    a = self.buff_aura(b, t, alpha * fade_in)
                    if a is not None and slot <= max_buffs + 1:
                        out.alpha_composite(a, (int(st["x"]) - m, y - m))
                live = {id(b) for b, _ in buffs}
                self._anim = {k: v for k, v in self._anim.items() if k in live}
            elif kind == "cd":
                x = m + (inner_w - cd_w) // 2
                for i, tr in enumerate(trackers):
                    a = self.aura(tr, t, unlocked)
                    if a is not None:
                        out.alpha_composite(a, (x + i * (s + sp) - m, y - m))
            elif kind == "hp":
                hp = vitals.health
                if hp is not None:
                    img = self.bar(cd_w, hp, self.health_color(hp), "", f"{int(round(hp * 100))}%", t,
                                   alert=hp <= cfg["low_health_alert"])
                    out.alpha_composite(img, (m + (inner_w - cd_w) // 2 - m, y - m))
            elif kind == "souls":
                if vitals.soul_frac is not None or vitals.souls is not None:
                    val = str(vitals.souls) if vitals.souls is not None else f"{int(round((vitals.soul_frac or 0) * 100))}%"
                    img = self.bar(cd_w, vitals.soul_frac, CYAN, "", val, t)
                    out.alpha_composite(img, (m + (inner_w - cd_w) // 2 - m, y - m))
            y += h + self.GAP
        return out

# --------------------------------------------------------------------------
def load_config():
    cfg = dict(DEFAULTS)
    if os.path.exists(CONFIG_PATH):
        try:
            with open(CONFIG_PATH, encoding="utf-8") as f:
                cfg.update(json.load(f))
        except Exception as e:
            print("config.json unreadable, using defaults:", e)
            try:  # keep the broken file instead of overwriting the layout with defaults
                os.replace(CONFIG_PATH, CONFIG_PATH + ".bad")
            except OSError:
                pass
    return cfg


def save_config(cfg):
    # write a temp file and swap it in, so a crash mid-save can't leave a half-written config
    tmp = CONFIG_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(cfg, f, indent=2)
    os.replace(tmp, CONFIG_PATH)


LAYOUTS_PATH = os.path.join(HERE, "layouts.json")
LAYOUT_SLOTS = ["1", "2", "3", "4"]


def load_layouts():
    """{"Default": layout, "1".."4": layout} - Reset goes back to "Default"."""
    try:
        with open(LAYOUTS_PATH, encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except (OSError, ValueError):
        return {}


def save_layouts(layouts):
    tmp = LAYOUTS_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(layouts, f, indent=2)
    os.replace(tmp, LAYOUTS_PATH)


def capture_layout(cfg):
    """Everything F8 arranges: panel places/directions/sizes, buff order and panel assignment."""
    import copy
    return {"panels": copy.deepcopy(cfg["panels"]), "buff_order": list(cfg.get("buff_order") or []),
            "buff_group": dict(cfg.get("buff_group") or {}), "snap": cfg.get("snap", True),
            "grid": cfg.get("grid", 20)}


def apply_layout(cfg, layout):
    for k, v in (layout.get("panels") or {}).items():
        if k in cfg["panels"]:
            cfg["panels"][k].update(v)  # in place: the main loop holds this dict
    if "buff_order" in layout:
        cfg["buff_order"] = list(layout["buff_order"])
    if "buff_group" in layout:
        cfg["buff_group"].clear()
        cfg["buff_group"].update(layout["buff_group"])
    for k in ("snap", "grid"):
        if k in layout:
            cfg[k] = layout[k]


def state_line(trackers, buffs, vitals):
    parts = [f"{tr.spec['key']}:" + ("ACTIVE " if tr.active else "") +
             ("CD %.0f%% %.1fs" % (tr.frac * 100, tr.remaining) if tr.on_cd else "ready") for tr in trackers]
    hp = "-" if vitals.health is None else f"{vitals.health:.0%}"
    sf = "-" if vitals.soul_frac is None else f"{vitals.soul_frac:.0%}"
    parts.append(f"hp={hp} souls={vitals.souls}({sf})")
    parts.append(f"n={len(buffs)} buffs=" + ",".join(f"{b.name}:{b.remaining:.1f}s" for b, a in buffs))
    return "  ".join(parts)


def main():
    cfg = load_config()
    save_config(cfg)
    reader = ScreenReader(cfg.get("hud_scale") or 1.0)
    by_key = slot_specs(reader.hud)
    trackers = [SlotTracker(by_key[k], cfg["learned_durations"]) for k in cfg["slots"] if k in by_key]
    for tr in trackers:
        tr.hud = reader.hud
    vitals = VitalsReader()
    last_seen = time.perf_counter()
    last_cal = 0.0
    bufftr = BuffTracker(cfg.get("buff_durations"), cfg.get("artifact_buffs"))
    exact = ExactSource()
    tester = TestSource()
    test_mode = False
    SLOT_TAGS = {"slot1": "Artifact1", "slot2": "Artifact2", "slot3": "Artifact3", "potion": "Potion"}
    seen_cd_tags = set()
    pot_drop, pot_rem, pot_seen_full, pot_seen = None, None, False, False
    pot_prev_ch = None
    renderer = Renderer(cfg)

    # ---- panels: each block is its own window with its own position and direction
    ax = cfg["x"] if cfg["x"] is not None else reader.W // 2
    ay = cfg["y"] if cfg["y"] is not None else int(reader.H * 0.62)
    cell = renderer.size + cfg["spacing"] + 4
    cdw = cell * len(trackers)
    bcell = renderer.bsize + cfg["spacing"] + renderer.bsize // 8
    defaults = {
        "debuffs": {"x": ax + cdw // 2 + 30, "y": ay - 2 * bcell, "dir": "y"},
        "attack": {"x": ax - 3 * bcell - 6, "y": ay - bcell - 10, "dir": "x"},
        "defense": {"x": ax + 6, "y": ay - bcell - 10, "dir": "x"},
        "cooldowns": {"x": ax - cdw // 2, "y": ay, "dir": "x"},
        "health": {"x": ax - cdw // 2, "y": ay + renderer.size + 12, "dir": "x"},
        "souls": {"x": ax - cdw // 2, "y": ay + renderer.size + 12 + cfg["bar_height"] + 8, "dir": "x"},
    }
    panels_cfg = cfg.get("panels") or {}
    for k, v in defaults.items():
        panels_cfg.setdefault(k, dict(v, show=True))
    cfg["panels"] = panels_cfg
    if not cfg["show_buffs"]:
        for k in BUFF_PANELS:
            panels_cfg[k]["show"] = False
    panels_cfg["health"]["show"] = panels_cfg["health"].get("show", True) and cfg["show_health_bar"]
    panels_cfg["souls"]["show"] = panels_cfg["souls"].get("show", True) and cfg["show_soul_bar"]
    save_config(cfg)
    windows = {k: LayeredWindow(lambda dx, dy: None, native_drag=False) for k in defaults}
    menu_win = LayeredWindow(lambda dx, dy: None, native_drag=False)
    menu_win.set_locked(False)
    menu_buttons, menu_hover = [], None
    layouts = load_layouts()
    layout_save_mode, layout_current, layout_flash = False, None, (None, 0.0)
    cfg.setdefault("menu_pos", [60, 140])
    cfg.setdefault("snap", True)
    cfg.setdefault("grid", 20)
    if not cfg.get("_debuffs_column_v1"):  # one-time: debuffs stack downward
        panels_cfg["debuffs"]["dir"] = "y"
        cfg["_debuffs_column_v1"] = True
    save_config(cfg)
    grid_win = LayeredWindow(lambda dx, dy: None, native_drag=False)
    grid_shown = None
    grid_img_cache = {}

    def grid_image(step):
        if step not in grid_img_cache:
            gi = Image.new("RGBA", (reader.W, reader.H), (0, 0, 0, 0))
            gd = ImageDraw.Draw(gi)
            for x in range(0, reader.W, step):
                gd.line((x, 0, x, reader.H), fill=(255, 255, 255, 38 if x % (step * 5) else 70))
            for y in range(0, reader.H, step):
                gd.line((0, y, reader.W, y), fill=(255, 255, 255, 38 if y % (step * 5) else 70))
            grid_img_cache[step] = gi
        return grid_img_cache[step]
    placed = {}      # panel -> (left, top, w, h) on screen, for hit testing
    content = {}     # panel -> (x0, y0, x1, y1) of what's actually drawn (no glow margin)
    cells_at = {}    # buff panel -> [(name, rect in panel)]
    SNAP, GAP = 14, 6

    def reset_layout():
        saved = load_layouts().get("Default")
        if saved:
            apply_layout(cfg, saved)
        else:
            for k, v in defaults.items():
                panels_cfg[k].update(dict(v, scale=1.0))
        save_config(cfg)

    def group_of(k):
        """Panels touching k (directly or through others) move together."""
        if not cfg["snap"] or k not in content:
            return [k]
        out, todo = {k}, [k]
        while todo:
            a = content[todo.pop()]
            for o, b in content.items():
                if o in out:
                    continue
                touch_x = a[0] - GAP - 3 <= b[2] and b[0] <= a[2] + GAP + 3
                touch_y = a[1] - GAP - 3 <= b[3] and b[1] <= a[3] + GAP + 3
                if touch_x and touch_y:
                    out.add(o)
                    todo.append(o)
        return list(out)

    def snap_delta(moving, dx, dy):
        """Nudge a moving group so its edges line up with (or butt against) other panels,
        otherwise lock it to the grid."""
        if not cfg["snap"]:
            step = cfg.get("grid") or 0
            lead = moving[0]
            if step and lead in content:
                x0, y0 = content[lead][0], content[lead][1]
                dx = round((x0 + dx) / step) * step - x0
                dy = round((y0 + dy) / step) * step - y0
            return dx, dy
        others = [r for o, r in content.items() if o not in moving]
        best_x, best_y = None, None
        for k in moving:
            if k not in content:
                continue
            x0, y0, x1, y1 = content[k]
            x0, x1, y0, y1 = x0 + dx, x1 + dx, y0 + dy, y1 + dy
            for ox0, oy0, ox1, oy1 in others:
                for a, b in ((x0, ox0), (x1, ox1), (x0, ox1 + GAP), (x1, ox0 - GAP), ((x0 + x1) / 2, (ox0 + ox1) / 2)):
                    if abs(b - a) <= SNAP and (best_x is None or abs(b - a) < abs(best_x)):
                        best_x = b - a
                for a, b in ((y0, oy0), (y1, oy1), (y0, oy1 + GAP), (y1, oy0 - GAP), ((y0 + y1) / 2, (oy0 + oy1) / 2)):
                    if abs(b - a) <= SNAP and (best_y is None or abs(b - a) < abs(best_y)):
                        best_y = b - a
        dx, dy = dx + (best_x or 0), dy + (best_y or 0)
        step = cfg.get("grid") or 0
        lead = moving[0]
        if step and lead in content:
            x0, y0 = content[lead][0], content[lead][1]
            if best_x is None:
                dx = round((x0 + dx) / step) * step - x0
            if best_y is None:
                dy = round((y0 + dy) / step) * step - y0
        return dx, dy

    def buff_order_for(group):
        order = list(cfg["buff_order"])
        names = [n for n in STATUS_ICONS if (cfg["buff_group"].get(n) or default_group(n)) == group]
        names.sort(key=lambda n: order.index(n) if n in order else 999 + sorted(STATUS_ICONS).index(n))
        return names

    unlocked = False
    f8_prev = False
    lmb_prev = rmb_prev = False
    drag = None
    last_learned = dict(cfg["learned_durations"])
    debug_t = 0.0
    img = None
    fade, last_t = 0.0, time.perf_counter()
    missed = 99
    print(f"Dungeons II Auras running ({reader.W}x{reader.H}). F8 = edit layout, Ctrl+Shift+F8 = quit.")

    while True:
        try:
            t = time.perf_counter()
            for w in windows.values():
                w.pump()

            f8 = bool(user32.GetAsyncKeyState(VK_F8) & 0x8001)  # held, or tapped since the last check
            if f8 and not f8_prev:
                if key_down(VK_CONTROL) and key_down(VK_SHIFT):
                    break
                unlocked = not unlocked
                for w in windows.values():
                    w.set_locked(not unlocked)
                drag = None
                menu_win.show(unlocked)
                if not unlocked:
                    grid_win.show(False)
                if not unlocked:
                    save_config(cfg)
            f8_prev = f8

            fg = foreground_exe()
            in_game = fg == GAME_EXE or not cfg["only_when_game_focused"]
            show = False
            big = None
            if in_game or unlocked:
                big, crop = reader.grab()
                if not hotbar_visible(crop):
                    if t - last_seen > 1.5 and t - last_cal > 2.0:  # HUD Size changed? find it again
                        last_cal = t
                        if reader.calibrate():
                            cfg["hud_scale"] = reader.hud
                            save_config(cfg)
                            specs = slot_specs(reader.hud)
                            for tr in trackers:
                                tr.spec, tr.icon, tr.samples, tr.on_cd = specs[tr.spec["key"]], None, [], False
                                tr.hud, tr.art = reader.hud, None
                            big, crop = reader.grab()
                if hotbar_visible(crop):
                    last_seen = t
                    for tr in trackers:
                        tr.feed(crop, t)
                        if tr.started_at == t and tr.art:
                            bufftr.note_use(tr.art, t)
                            if bufftr.link_for(tr.art):
                                bufftr.trigger(bufftr.link_for(tr.art), t)  # artifact used: its buff starts now
                    vitals.feed(crop, t)
                    if cfg["show_buffs"] and not exact.fresh(t) and not test_mode:
                        bufftr.feed(big, t)  # fallback: read the game's buff icons off the screen
                # brief unreadable moments (flashes, effects over the hotbar) must not blink the overlay
                # hide the instant the hotbar goes away (menus, map, inventory, loading); two missed
                # frames in a row so a single combat flash over the badges doesn't blink it
                missed = 0 if last_seen == t else missed + 1
                show = missed < 2 or unlocked
            if test_mode:
                bufftr.apply_exact(tester.entries(t), t, learn=False)
                show = show or unlocked or True
            elif exact.fresh(t):
                et, ebuffs, ecds = exact.latest
                bufftr.apply_exact([(n, max(0.0, r - (t - et)) if r >= 0 else r, d) for n, r, d in ebuffs], t)
                seen_cd_tags.update(ecds)
                for tr in trackers:  # which artifact is in each slot comes straight from the game
                    k = tr.spec["key"]
                    if k.startswith("slot"):
                        item = exact.equipped.get("SW.ItemSlot.Equipment.Artifact.Slot" + k[-1])
                        name = artifact_name(item)
                        if item != getattr(tr, "item_tag", None):
                            tr.item_tag = item
                            tr.icon = None  # swapped: drop the old screen capture
                        tr.art = name
                        tr.art_from_game = True
                # values can be garbage for a moment while a level loads: ignore NaN/inf
                at = {k: v for k, v in (exact.attrs or {}).items() if v is not None and math.isfinite(v)}
                if at.get("HealthMax"):
                    vitals.health = max(0.0, min(1.0, at["Health"] / at["HealthMax"]))
                if at.get("SoulsMax"):
                    vitals.souls = int(at["Souls"])
                    vitals.soul_frac = max(0.0, min(1.0, at["Souls"] / at["SoulsMax"]))
                # potion: charges drop when you drink, then recharge over BaseCooldown x multiplier
                ch, chmax = at.get("HealthPotionCharges"), at.get("HealthPotionChargesMax")
                if ch is not None and chmax:
                    pot_cd = (at.get("HealthPotionBaseCooldown") or 20.0) * (at.get("HealthPotionCooldownMultiplier") or 1.0)
                    if pot_prev_ch is not None and ch > pot_prev_ch + 1e-3 and ch < chmax - 1e-3:
                        pot_drop = t  # one charge came back, the next one starts recharging now
                    pot_prev_ch = ch
                    if ch < chmax - 1e-3:
                        if pot_drop is None:
                            pot_drop = t if pot_seen_full else None
                        pot_seen = True
                        frac_part = ch - int(ch)
                        if frac_part > 1e-3:  # recharge stored as a fraction
                            pot_rem = (1 - frac_part) * pot_cd
                        elif pot_drop is not None:
                            pot_rem = max(0.0, pot_cd - (t - pot_drop))
                        else:
                            pot_rem = None  # started mid-cooldown: let the screen reading handle it
                    else:
                        pot_drop, pot_rem, pot_seen_full = None, 0.0, True
                    for tr in trackers:
                        if tr.spec["key"] == "potion" and pot_rem is not None:
                            tr.set_exact(pot_rem, pot_cd, t)
                for tr in trackers:
                    tag = SLOT_TAGS.get(tr.spec["key"])
                    if tr.spec["key"] == "potion" and pot_rem is not None:
                        continue  # the potion runs on its charges (set above), not a cooldown tag
                    if tag in ecds:
                        r, d = ecds[tag]
                        tr.set_exact(max(0.0, r - (t - et)), d, t)
                    elif tag in seen_cd_tags:  # this slot's cooldown is tracked in memory and isn't running
                        tr.set_exact(0.0, 1.0, t)
            for tr in trackers:
                tr.tick(t)
                # after tick: with game timers the cooldown ends inside tick, not in feed
                if cfg["sound_on_ready"] and tr.ready_at == t:
                    ctypes.windll.user32.MessageBeep(0x40)
            bufftr.tick(t)
            if bufftr.dirty:
                bufftr.dirty = False
                cfg["buff_durations"] = bufftr.export()
                cfg["artifact_buffs"] = bufftr.links
                save_config(cfg)

            # ---- edit mode: options menu, drag panels (snapping, touching panels move together;
            #      Ctrl+drag pulls one out), drag buffs to reorder / move between panels, right-click flips x/y
            if unlocked:
                pt = wt.POINT()
                user32.GetCursorPos(ctypes.byref(pt))
                cx, cy = pt.x, pt.y
                lmb, rmb = key_down(0x01), key_down(0x02)
                mx, my = cfg["menu_pos"]

                def menu_button_at(x, y):
                    for bid, (x0, y0, x1, y1) in menu_buttons:
                        if x0 <= x - mx < x1 and y0 <= y - my < y1 and bid[0] != "drag":
                            return bid
                    for bid, (x0, y0, x1, y1) in menu_buttons:
                        if bid[0] == "drag" and x0 <= x - mx < x1 and y0 <= y - my < y1:
                            return bid
                    return None

                def panel_at(x, y):
                    for k in reversed(list(placed)):
                        l, tp, w, h = placed[k]
                        if l <= x < l + w and tp <= y < tp + h:
                            return k
                    return None

                menu_hover = menu_button_at(cx, cy)
                if DEBUG and lmb and not lmb_prev:
                    print(f"   press at {cx},{cy} menu={menu_hover} panel={panel_at(cx, cy)} placed={ {k: v for k, v in placed.items()} }", flush=True)
                if lmb and not lmb_prev:
                    bid = menu_hover
                    if bid is not None:
                        kind = bid[0]
                        if kind == "drag":
                            drag = {"type": "menu", "dx": cx - mx, "dy": cy - my}
                        elif kind == "show":
                            panels_cfg[bid[1]]["show"] = not panels_cfg[bid[1]].get("show", True)
                        elif kind == "dir":
                            panels_cfg[bid[1]]["dir"] = "y" if panels_cfg[bid[1]].get("dir", "x") == "x" else "x"
                        elif kind in ("size-", "size+"):
                            pc = panels_cfg[bid[1]]
                            pc["scale"] = round(min(2.0, max(0.5, pc.get("scale", 1.0) + (0.1 if kind == "size+" else -0.1))), 2)
                        elif kind == "snap":
                            cfg["snap"] = not cfg["snap"]
                        elif kind == "test":
                            test_mode = not test_mode
                            if not test_mode:  # drop the fake buffs right away (and never learn from them)
                                bufftr.active.clear()
                                bufftr.ended.clear()
                        elif kind == "grid":
                            steps = [0, 10, 20, 40]
                            cur = cfg.get("grid") or 0
                            cfg["grid"] = steps[(steps.index(cur) + 1) % len(steps)] if cur in steps else 20
                        elif kind == "reset":
                            reset_layout()
                            layout_current, layout_flash = "Default", ("Default", t)
                        elif kind == "lsave":
                            layout_save_mode = not layout_save_mode
                        elif kind == "lslot":
                            slot = bid[1]
                            if layout_save_mode:
                                layouts[slot] = capture_layout(cfg)
                                save_layouts(layouts)
                                layout_save_mode = False
                                layout_current, layout_flash = slot, (slot, t)
                            elif slot in layouts:
                                apply_layout(cfg, layouts[slot])
                                layout_current, layout_flash = slot, (slot, t)
                        elif kind == "ldefault":
                            layouts["Default"] = capture_layout(cfg)
                            save_layouts(layouts)
                            layout_save_mode = False
                            layout_current, layout_flash = "Default", ("Default", t)
                        elif kind == "done":
                            unlocked = False
                            for w in windows.values():
                                w.set_locked(True)
                            menu_win.show(False)
                            grid_win.show(False)
                        save_config(cfg)
                    else:
                        k = panel_at(cx, cy)
                        if k is not None:
                            l, tp, w, h = placed[k]
                            hit = None
                            sc = panels_cfg[k].get("scale", 1.0)
                            for nm, (x0, y0, x1, y1) in cells_at.get(k, []):
                                if x0 * sc <= cx - l < x1 * sc and y0 * sc <= cy - tp < y1 * sc:
                                    hit = nm
                            if hit:
                                drag = {"type": "buff", "name": hit, "from": k}
                            else:
                                members = [k] if key_down(VK_CONTROL) else group_of(k)
                                drag = {"type": "move", "panels": members, "x0": cx, "y0": cy,
                                        "start": {m_: (panels_cfg[m_]["x"], panels_cfg[m_]["y"]) for m_ in members},
                                        "content": {m_: content[m_] for m_ in members if m_ in content}}
                elif lmb and drag and drag["type"] == "menu":
                    cfg["menu_pos"] = [cx - drag["dx"], cy - drag["dy"]]
                elif lmb and drag and drag["type"] == "move":
                    saved = {m_: content.get(m_) for m_ in drag["panels"]}
                    content.update(drag["content"])  # snap against where the group started
                    dx, dy = snap_delta(drag["panels"], cx - drag["x0"], cy - drag["y0"])
                    for m_, r_ in saved.items():
                        if r_ is not None:
                            content[m_] = r_
                    for m_ in drag["panels"]:
                        sx_, sy_ = drag["start"][m_]
                        panels_cfg[m_]["x"], panels_cfg[m_]["y"] = int(sx_ + dx), int(sy_ + dy)
                elif not lmb and lmb_prev and drag:
                    if drag["type"] == "buff":
                        k = panel_at(cx, cy)
                        if k in BUFF_PANELS:
                            nm = drag["name"]
                            cfg["buff_group"][nm] = k
                            target = None
                            l, tp, w, h = placed[k]
                            sc = panels_cfg[k].get("scale", 1.0)
                            for other, (x0, y0, x1, y1) in cells_at.get(k, []):
                                if x0 * sc <= cx - l < x1 * sc and y0 * sc <= cy - tp < y1 * sc and other != nm:
                                    target = other
                            order = [n for n in cfg["buff_order"] if n != nm]
                            for g in BUFF_PANELS:  # make sure every buff has a place in the order
                                for n in buff_order_for(g):
                                    if n not in order and n != nm:
                                        order.append(n)
                            if target in order:
                                order.insert(order.index(target), nm)
                            else:
                                order.append(nm)
                            cfg["buff_order"] = order
                    drag = None
                    save_config(cfg)
                if rmb and not rmb_prev:
                    k = panel_at(cx, cy)
                    if k is not None:
                        panels_cfg[k]["dir"] = "y" if panels_cfg[k]["dir"] == "x" else "x"
                        save_config(cfg)
                lmb_prev, rmb_prev = lmb, rmb
                mimg, menu_buttons = renderer.menu_image(
                    panels_cfg, cfg["snap"], menu_hover, cfg.get("grid") or 0, test_mode, exact.fresh(t),
                    {"filled": set(layouts), "save": layout_save_mode, "current": layout_current,
                     "flash": layout_flash[0] if t - layout_flash[1] < 0.6 else None})
                if cfg.get("grid") and grid_shown != cfg["grid"]:
                    grid_win.update(grid_image(cfg["grid"]), 0, 0)  # full-screen image: only push on change
                    grid_shown = cfg["grid"]
                grid_win.show(bool(cfg.get("grid")))
                grid_win.pump()
                menu_win.update(mimg, int(cfg["menu_pos"][0]), int(cfg["menu_pos"][1]))
                menu_win.show(True)
                menu_win.pump()

            if show:
                fade += (t - last_t) / 0.15  # quick fade in
            else:
                fade = 0.0  # gone instantly when a menu opens or the game loses focus
            fade = min(1.0, max(0.0, fade))
            last_t = t
            renderer.bufftr = bufftr
            renderer.test_mode = test_mode
            renderer._live_all = {id(b) for b, _ in bufftr.visible()}
            vis = bufftr.visible()
            for k, w in windows.items():
                pc = panels_cfg[k]
                on = fade > 0 and pc.get("show", True)
                if on:
                    if k in BUFF_PANELS:
                        mine = [(b, a) for b, a in vis if (cfg["buff_group"].get(b.name) or default_group(b.name)) == k]
                        if not mine and not unlocked:
                            on = False
                        else:
                            img, cells_at[k] = renderer.panel_buffs(k, mine, t, unlocked, buff_order_for(k))
                    elif k == "cooldowns":
                        img = renderer.panel_cooldowns(trackers, t, unlocked)
                    else:
                        img = renderer.panel_bar(k, vitals, t, unlocked)
                if on:
                    sc = pc.get("scale", 1.0)
                    if abs(sc - 1.0) > 1e-3:
                        img = img.resize((max(1, int(img.width * sc)), max(1, int(img.height * sc))), Image.LANCZOS)
                    if fade < 1:
                        img = _with_alpha(img, fade)
                    m = Renderer.MARGIN * sc
                    left, top = int(pc["x"] - m), int(pc["y"] - m)
                    w.update(img, left, top)
                    placed[k] = (left, top, img.width, img.height)
                    content[k] = (pc["x"], pc["y"], left + img.width - m, top + img.height - m)
                else:
                    placed.pop(k, None)
                    content.pop(k, None)
                w.show(on)

            if DEBUG and t - debug_t > 0.5:
                debug_t = t
                print(f"{t:8.1f} fg={fg} show={show} exact={exact.ok}/{exact.fresh(t)} " + state_line(trackers, vis, vitals), flush=True)

            if cfg["learned_durations"] != last_learned:
                last_learned = dict(cfg["learned_durations"])
                save_config(cfg)

            dt = time.perf_counter() - t
            time.sleep(max(0.0, 1 / 30 - dt))
        except Exception:
            # one bad frame (odd memory values while a level loads, a failed screen grab on the
            # lock screen...) must not close the overlay: note it and carry on
            import traceback
            try:
                with open(os.path.join(HERE, "errors.log"), "a", encoding="utf-8") as f:
                    f.write(time.strftime("%Y-%m-%d %H:%M:%S ") + traceback.format_exc() + chr(10))
            except OSError:
                pass
            time.sleep(0.1)


def selftest(folder, pad=0):
    """Run the readers over saved screen crops whose top-left is (OX, OY - pad) at 2560x1440."""
    by_key = {s["key"]: s for s in SLOTS}
    trackers = [SlotTracker(by_key[k], {}) for k in DEFAULTS["slots"]]
    vitals, bufftr = VitalsReader(), BuffTracker()
    files = sorted(f for f in os.listdir(folder) if f.endswith(".png"))
    P = ScreenReader.PAD
    for i, f in enumerate(files):
        a = np.asarray(Image.open(os.path.join(folder, f)).convert("RGB"))
        big = np.zeros((250 + P, ScreenReader.WIDTH, 3), np.uint8)
        src = a[max(0, pad - P):]
        dy = max(0, P - pad)
        hh, ww = min(big.shape[0] - dy, src.shape[0]), min(big.shape[1], src.shape[1])
        big[dy:dy + hh, :ww] = src[:hh, :ww]
        crop = big[P:]
        t = i * 0.2
        vis = hotbar_visible(crop)
        if vis:
            for tr in trackers:
                tr.feed(crop, t)
            vitals.feed(crop, t)
            bufftr.feed(big, t)
        print(f, "visible" if vis else "HIDDEN ", state_line(trackers, bufftr.visible(), vitals))
    return trackers, vitals, bufftr


if __name__ == "__main__":
    if len(sys.argv) > 2 and sys.argv[1] == "--selftest":
        selftest(sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 0)
    else:
        main()

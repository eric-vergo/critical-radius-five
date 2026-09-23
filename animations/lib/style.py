"""Visual language shared by all scenes.

Two themes: ``dark`` (videos, GIFs, site stills) and ``light`` (stills for the paper).
Select with the environment variable ``GG5_THEME`` (default ``dark``).
"""
from __future__ import annotations

import os

import numpy as np
from manim import (
    DOWN, LEFT, RIGHT, UP, ORIGIN, Arc, Circle, Dot, Line, MathTex, Tex, Text, VGroup, VMobject,
    Intersection, config, DashedLine, Arrow, CurvedArrow, TAU, PI,
)

from .geometry import RC

THEME = os.environ.get("GG5_THEME", "dark")

if THEME == "light":
    BG = "#FFFFFF"
    INK = "#1B1F24"          # text, outlines
    MUTED = "#6B7280"        # secondary text
    FAINT = "#C9CED6"        # grid, faint strokes
    LEFT_C = "#1F6FB2"       # left disk (a)
    RIGHT_C = "#C8641A"      # right disk (b)
    LENS_C = "#6B4FA0"       # the lens
    CHORD_C = "#1B1F24"
    I1_C = "#0E8A6A"         # piece I1
    I2_C = "#B8338A"         # piece I2
    I3_C = "#C99A06"         # piece I3
    HOT = "#D7263D"          # emphasis (tight contacts, walls)
    GOOD = "#1E8C45"
    FILL_OP = 0.10
    LENS_OP = 0.16
else:
    BG = "#0E1117"
    INK = "#E8EAED"
    MUTED = "#9AA3AE"
    FAINT = "#3A414B"
    LEFT_C = "#5AA2F0"
    RIGHT_C = "#F5A04A"
    LENS_C = "#B39DDB"
    CHORD_C = "#F4F4F4"
    I1_C = "#3DDC97"
    I2_C = "#F062C0"
    I3_C = "#F9D648"
    HOT = "#FF5A6E"
    GOOD = "#58D68D"
    FILL_OP = 0.10
    LENS_OP = 0.18

PIECE_C = {"I1": I1_C, "I2": I2_C, "I3": I3_C}
SANS = "Helvetica Neue"
MONO = "Menlo"

config.background_color = BG


def setup_defaults():
    """Make every mobject use the theme's ink by default."""
    for cls in (Text, MathTex, Tex):
        cls.set_default(color=INK)
    Line.set_default(color=INK)
    Dot.set_default(color=INK)


setup_defaults()


class Frame:
    """Affine map from the complex plane to scene coordinates."""

    def __init__(self, scale: float = 1.4, origin=(0.0, -0.35)):
        self.s = scale
        self.o = np.array([origin[0], origin[1], 0.0])

    def __call__(self, z: complex) -> np.ndarray:
        return self.o + self.s * np.array([z.real, z.imag, 0.0])

    def len(self, x: float) -> float:
        return self.s * x


def T(s: str, size: float = 30, color=None, weight="NORMAL", font=SANS, **kw) -> Text:
    return Text(s, font=font, font_size=size, color=color or INK, weight=weight, **kw)


def M(s: str, size: float = 36, color=None, **kw) -> MathTex:
    return MathTex(s, font_size=size, color=color or INK, **kw)


def disk(fr: Frame, centre: float, r: float, color, fill_opacity=None, stroke_width=3.0,
         teeth=True):
    """A closed disk: faint fill, rim, and five inward teeth that show its rotation."""
    c = fr(complex(centre, 0))
    rim = Circle(radius=fr.len(r), color=color, stroke_width=stroke_width).move_to(c)
    fill = Circle(radius=fr.len(r), stroke_width=0).move_to(c)
    fill.set_fill(color, opacity=FILL_OP if fill_opacity is None else fill_opacity)
    grp = VGroup(fill, rim)
    marks = VGroup()
    if teeth:
        for k in range(5):
            ang = PI / 2 + k * TAU / 5
            u = np.array([np.cos(ang), np.sin(ang), 0.0])
            marks.add(Line(c + u * fr.len(r) * 0.86, c + u * fr.len(r), color=color,
                           stroke_width=stroke_width + 1))
        centre_dot = Dot(c, radius=0.05, color=color)
        marks.add(centre_dot)
    grp.add(marks)
    grp.marks = marks
    grp.centre = c
    return grp


def lens_shape(fr: Frame, r: float, color=None, opacity=None):
    a = Circle(radius=fr.len(r)).move_to(fr(-1 + 0j))
    b = Circle(radius=fr.len(r)).move_to(fr(1 + 0j))
    lens = Intersection(a, b, color=color or LENS_C, fill_opacity=LENS_OP if opacity is None
                        else opacity, stroke_width=0)
    return lens


def point_label(tex: str, pos, direction, size=30, color=None, buff=0.12):
    lab = M(tex, size=size, color=color)
    lab.next_to(pos, direction, buff=buff)
    return lab


def seg(fr: Frame, p: complex, q: complex, color, width=6.0):
    return Line(fr(p), fr(q), color=color, stroke_width=width)


def row(*parts, size=22, color=None, buff=0.1):
    """A line mixing plain text and math: parts starting with '$' are typeset as math."""
    mobs = []
    for part in parts:
        if part.startswith("$"):
            last = part.rindex("$")
            body, tail = part[1:last], part[last + 1:]
            if tail:
                body += r"\text{" + tail + "}"
            mobs.append(M(body, size * 1.3, color=color))
        else:
            mobs.append(T(part, size, color=color))
    return VGroup(*mobs).arrange(RIGHT, buff=buff)

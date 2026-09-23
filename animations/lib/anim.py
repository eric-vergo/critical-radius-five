"""Small animation helpers."""
from __future__ import annotations

import numpy as np
from manim import (
    AnimationGroup, Arc, CurvedArrow, Rotate, TAU, PI, VGroup, smooth, ArcBetweenPoints,
    Create, FadeOut,
)

from .geometry import ANGLE, CENTRE
from .style import Frame


def turn_anims(fr: Frame, letter: str, movers, run_time=1.2):
    """Rotate every mobject in ``movers`` about the centre of the letter's disk."""
    c = fr(complex(CENTRE[letter], 0))
    return [Rotate(m, angle=ANGLE[letter], about_point=c, rate_func=smooth, run_time=run_time)
            for m in movers]


def turn_arrow(fr: Frame, letter: str, r: float, color, frac=0.62, width=5):
    """A curved arrow inside the disk showing the direction of the turn."""
    c = fr(complex(CENTRE[letter], 0))
    rad = fr.len(r) * frac
    ang = ANGLE[letter]
    start = PI / 2 + (0.35 if CENTRE[letter] < 0 else -0.35)
    if CENTRE[letter] < 0:
        start = PI * 0.78
    else:
        start = PI * 0.22
    arc = Arc(radius=rad, start_angle=start - ang / 2, angle=ang, arc_center=c, color=color,
              stroke_width=width)
    arc.add_tip(tip_length=0.22, tip_width=0.22)
    return arc

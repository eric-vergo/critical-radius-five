"""B3 - Tightness: the cut disappears exactly when E'E fits in the lens, at r = sqrt(3 + phi).

Render:  manim -qh scenes/b3_threshold.py B3Threshold
"""
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import numpy as np
from manim import *  # noqa: F401,F403

from lib.geometry import DELTA, E, RC, is_cut_level, lens_half_window, psiL, window_centre
from lib.style import (
    CHORD_C, FAINT, GOOD, HOT, INK, LEFT_C, LENS_C, MUTED, RIGHT_C, Frame, M, T, hold, lens_shape,
    row,
)

P0 = -0.1722 + 0.0773j
R_START, R_END = 1.8, 2.2


def chord_inside(r, n=400):
    """Sub-interval of s in [-1, 1] with s E in both closed disks (a segment, by convexity)."""
    inside = [s for s in np.linspace(-1, 1, n + 1)
              if abs(s * E + 1) <= r + 1e-12 and abs(s * E - 1) <= r + 1e-12]
    if not inside:
        return None
    # refine the ends by bisection
    def edge(a, b):
        for _ in range(50):
            m = (a + b) / 2
            ok = abs(m * E + 1) <= r and abs(m * E - 1) <= r
            a, b = (m, b) if ok else (a, m)
        return a
    lo, hi = min(inside), max(inside)
    step = 2 / n
    lo2 = edge(lo, max(lo - step, -1.0)) if lo > -1 else -1.0
    hi2 = edge(hi, min(hi + step, 1.0)) if hi < 1 else 1.0
    return lo2, hi2


class B3Threshold(Scene):
    def construct(self):
        rt = ValueTracker(R_START)
        fr = Frame(scale=0.88, origin=(-3.75, -0.5))
        title = T("The cut opens exactly when E′E fits", 32, weight="BOLD").to_corner(UL,
                                                                                         buff=0.3)
        self.add(title)
        hold(self, title)

        def disks():
            r = rt.get_value()
            g = VGroup()
            for c, col in ((-1, LEFT_C), (1, RIGHT_C)):
                circ = Circle(radius=fr.len(r), color=col, stroke_width=3).move_to(fr(complex(c, 0)))
                circ.set_fill(col, opacity=0.08)
                g.add(circ)
                g.add(Dot(fr(complex(c, 0)), radius=0.045, color=col))
            g.add(lens_shape(fr, r, opacity=0.16))
            return g

        def chord():
            r = rt.get_value()
            g = VGroup()
            g.add(DashedLine(fr(-E), fr(E), color=HOT, stroke_width=4, dash_length=0.06))
            iv = chord_inside(r)
            if iv is not None:
                g.add(Line(fr(iv[0] * E), fr(iv[1] * E), color=CHORD_C, stroke_width=5))
            g.add(Dot(fr(E), radius=0.06, color=INK), Dot(fr(-E), radius=0.06, color=INK))
            return g

        D = always_redraw(disks)
        C = always_redraw(chord)
        # buff 0.16 keeps both labels clear of the red rings (radius 0.16) drawn at the end
        lE = M("E", 28).next_to(fr(E), UR, buff=0.16)
        lEp = M("E'", 28).next_to(fr(-E), DL, buff=0.16)
        self.play(FadeIn(D), FadeIn(C), FadeIn(lE), FadeIn(lEp), run_time=1.0)

        # readouts
        r_lab = VGroup(M("r =", 32), DecimalNumber(R_START, num_decimal_places=4, font_size=32,
                                                   color=INK)).arrange(RIGHT, buff=0.15)
        r_lab[1].add_updater(lambda m: m.set_value(rt.get_value()))
        r_lab.move_to([-6.75, 2.85, 0], aligned_edge=LEFT)
        self.add(r_lab)
        hold(self, lE, lEp, r_lab)

        # ---------------- the comb, rows q = -25..25 ------------------------------------------
        Z = window_centre(P0, 1)
        xl, xr = 0.55, 6.75
        span = 2.0
        X = lambda psi: xl + (psi - (Z - span / 2)) * (xr - xl) / span
        qs = range(-25, 26)
        Y = lambda q: -0.55 + 0.112 * q
        rows = VGroup(*[Line([xl, Y(q), 0], [xr, Y(q), 0], color=FAINT, stroke_width=0.8)
                        for q in qs])
        teeth = VGroup()
        for q in qs:
            c0 = (Z + DELTA * q / ((1 + 5 ** 0.5) / 2)) / DELTA
            for P in range(math.floor(c0) - 3, math.ceil(c0) + 4):
                x = psiL(P, q)
                if Z - span / 2 < x < Z + span / 2:
                    teeth.add(Line([X(x), Y(q) - 0.05, 0], [X(x), Y(q) + 0.05, 0], color=INK,
                                   stroke_width=3.5))
        lab_q = VGroup(M("q=25", 28, MUTED).next_to([xl, Y(25), 0], LEFT, buff=0.1),
                       M("0", 28, MUTED).next_to([xl, Y(0), 0], LEFT, buff=0.1),
                       M("-25", 28, MUTED).next_to([xl, Y(-25), 0], LEFT, buff=0.1))
        hdr = T("rows of teeth (levels 5q) and the strip", 20, MUTED).move_to(
            [(xl + xr) / 2, Y(25) + 0.35, 0])
        self.play(FadeIn(rows), FadeIn(teeth), FadeIn(lab_q), FadeIn(hdr), run_time=1.2)
        hold(self, hdr)                     # the header (tick labels are not read one by one)

        def strip():
            L = lens_half_window(rt.get_value())
            rect = Rectangle(width=max(X(Z + L) - X(Z - L), 1e-3), height=Y(25.5) - Y(-25.5),
                             stroke_width=0)
            rect.set_fill(GOOD, opacity=0.16).move_to([(X(Z - L) + X(Z + L)) / 2, Y(0), 0])
            return rect

        def walls():
            L = lens_half_window(rt.get_value())
            g = VGroup()
            for q in qs:
                if is_cut_level(q, Z, L):
                    g.add(Line([xl, Y(q), 0], [xr, Y(q), 0], color=HOT, stroke_width=3.5))
            return g

        S = always_redraw(strip)
        Wl = always_redraw(walls)
        self.play(FadeIn(S), FadeIn(Wl), run_time=0.8)
        self.bring_to_front(teeth)

        # gauge: 2L(r) against the period delta
        gx0, gx1, gy = -6.75, -1.3, 2.05
        gauge_bg = Rectangle(width=gx1 - gx0, height=0.22, stroke_color=MUTED, stroke_width=1.5)
        gauge_bg.move_to([(gx0 + gx1) / 2, gy, 0])

        def gauge():
            f = min(2 * lens_half_window(rt.get_value()) / DELTA, 1.08)
            w = (gx1 - gx0) * min(f, 1.0)
            bar = Rectangle(width=max(w, 1e-3), height=0.22, stroke_width=0)
            bar.set_fill(GOOD if f < 1 - 1e-9 else HOT, opacity=0.8)
            bar.move_to([gx0 + w / 2, gy, 0])
            return bar

        G = always_redraw(gauge)
        g_lab = row("strip width", "$2L(r)$", "against the period", "$\\delta = 3-\\varphi$",
                    size=18, color=MUTED).next_to(gauge_bg, UP, buff=0.12).align_to(gauge_bg, LEFT)
        self.play(FadeIn(gauge_bg), FadeIn(G), FadeIn(g_lab), run_time=0.8)
        hold(self, g_lab, at_least=0.5)

        # ---------------- grow r to the critical radius -----------------------------------------
        self.play(rt.animate.set_value(2.05), run_time=3.0, rate_func=linear)
        self.play(rt.animate.set_value(2.13), run_time=3.0, rate_func=linear)
        self.play(rt.animate.set_value(RC), run_time=3.5, rate_func=rate_functions.ease_out_sine)
        self.wait(0.3)
        ringE = Circle(radius=0.16, color=HOT, stroke_width=4).move_to(fr(E))
        ringEp = Circle(radius=0.16, color=HOT, stroke_width=4).move_to(fr(-E))
        crit = VGroup(
            row("$r = \\sqrt{3+\\varphi}$:", size=22),
            row("$E$", "and", "$E'$", "reach the rims,", "$E'E$", "fits the lens;", size=20),
            T("the strip is exactly one period wide:", 20),
            T("every row has a tooth inside, no cut is left.", 20),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.08).move_to([-6.75, -3.2, 0], aligned_edge=LEFT)
        self.play(Create(ringE), Create(ringEp), FadeIn(crit), run_time=1.0)
        hold(self, crit, at_least=3.5)

        # beyond
        self.play(FadeOut(ringE), FadeOut(ringEp), FadeOut(crit), run_time=0.5)
        self.play(rt.animate.set_value(R_END), run_time=2.0, rate_func=smooth)
        beyond = VGroup(
            T("From here on the three words carry E′E onto itself:", 20),
            T("the orbit of 0 is infinite (and stays so for larger r).", 20),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.08).move_to([-6.75, -3.35, 0], aligned_edge=LEFT)
        self.play(FadeIn(beyond), run_time=0.8)
        hold(self, beyond, at_least=3.0)
        self.play(FadeOut(beyond), rt.animate.set_value(RC), run_time=1.5)
        self.play(FadeIn(crit), Create(ringE), Create(ringEp), run_time=0.8)
        hold(self, crit, at_least=4.0)

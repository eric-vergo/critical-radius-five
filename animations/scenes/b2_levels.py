"""B2 - The level function and the cut: below the critical radius every orbit stays in a band.

Render:  manim -qh scenes/b2_levels.py B2Levels
"""
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import numpy as np
from manim import *  # noqa: F401,F403

from lib.geometry import (
    Cl, DELTA, UNIT5, ZETA, in_window, is_cut_level, lens_half_window, lv1, lv2,
    orbit_states, psiL, pt, qs1, window_centre,
)
from lib.style import (
    FAINT, GOOD, HOT, INK, LEFT_C, LENS_C, MUTED, RIGHT_C, Frame, M, T, disk, hold, lens_shape,
    row,
)

P0 = -0.1722 + 0.0773j
R0 = 2.0
U = 1 - ZETA + ZETA**2


class B2Levels(Scene):
    def construct(self):
        p, r = P0, R0
        title = T("A level that cannot be crossed", 32, weight="BOLD").to_corner(UL, buff=0.3)
        rlab = M(r"r = 2 < \sqrt{3+\varphi}", 30).to_corner(UR, buff=0.35)
        self.add(title, rlab)
        hold(self, title, rlab)

        # ---------------- small copy of the puzzle, bottom left ----------------------------
        fr = Frame(scale=0.44, origin=(-4.6, -2.75))
        Ld = disk(fr, -1, r, LEFT_C, stroke_width=2)
        Rd = disk(fr, 1, r, RIGHT_C, stroke_width=2)
        lens = lens_shape(fr, r, opacity=0.25)
        self.play(FadeIn(Ld), FadeIn(Rd), FadeIn(lens), run_time=0.8)

        # ---------------- the functional and the level ----------------------------------------
        defs = VGroup(
            row("$u = 1-\\zeta+\\zeta^2$,", "$|u| = 2-\\varphi$", size=20),
            row("$\\psi(v) = 2\\langle u, v\\rangle = A + B\\varphi$,", "$A,B\\in\\mathbb{Z}$",
                size=20),
            row("level", "$\\ell(v) = -A-3B\\in\\mathbb{Z}$", size=20),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.16).move_to([-6.85, 2.3, 0], aligned_edge=LEFT)
        self.play(FadeIn(defs), run_time=1.2)
        hold(self, defs, at_least=2.0)
        steps = VGroup(
            row("A step from a left centre changes", "$\\ell$", "by", "$+3$", "or", "$-2$,",
                size=20),
            row("one from a right centre by", "$-3$", "or", "$+2$;", size=20),
            row("left centres:", "$\\ell\\equiv 0$,", "right centres:", "$\\ell\\equiv 3 \\pmod 5$",
                size=20),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.12).next_to(defs, DOWN, aligned_edge=LEFT,
                                                              buff=0.35)
        self.play(FadeIn(steps), run_time=1.2)
        hold(self, steps, at_least=3.0)

        # ---------------- the comb diagram ----------------------------------------------------
        L = lens_half_window(r)
        Z = window_centre(p, 1)
        xl, xr = -0.05, 6.8
        span = 3.3
        def X(psi):
            return xl + (psi - (Z - span / 2)) * (xr - xl) / span
        def Y(level):
            return -0.78 + 0.09 * level
        qs = range(-5, 6)
        rows = VGroup()
        rlabels = VGroup()
        for q in qs:
            rows.add(Line([xl, Y(5 * q), 0], [xr, Y(5 * q), 0], color=FAINT, stroke_width=1.5))
            rlabels.add(M(str(5 * q), 20, MUTED).next_to([xl, Y(5 * q), 0], LEFT, buff=0.12))
        axis_l = T("level ℓ", 20, MUTED).next_to(rlabels, UP, buff=0.18)
        axis_x = M(r"\psi = 2\langle u, v\rangle", 26, MUTED).move_to([(xl + xr) / 2, Y(-25) - 0.42,
                                                                       0])
        self.play(Create(rows), FadeIn(rlabels), FadeIn(axis_l), FadeIn(axis_x), run_time=1.2)
        hold(self, axis_l, axis_x)          # the axis titles (tick labels are not read one by one)

        teeth = VGroup()
        for q in qs:
            c0 = (Z + DELTA * q / ((1 + 5 ** 0.5) / 2)) / DELTA
            for P in range(math.floor(c0) - 3, math.ceil(c0) + 4):
                x = psiL(P, q)
                if Z - span / 2 < x < Z + span / 2:
                    teeth.add(Line([X(x), Y(5 * q) - 0.13, 0], [X(x), Y(5 * q) + 0.13, 0],
                                   color=INK, stroke_width=3))
        tcap = VGroup(
            row("teeth: the possible values of", "$\\psi$", "for left centres on row", "$5q$",
                size=18, color=MUTED, buff=0.08),
            row("(spacing", "$\\delta = 3-\\varphi$,", "shifted by", "$\\delta/\\varphi$",
                "from row to row)", size=18, color=MUTED, buff=0.08),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.06).move_to([xl - 0.55, 3.0, 0],
                                                              aligned_edge=LEFT)
        self.play(LaggedStart(*[Create(t) for t in teeth], lag_ratio=0.03), FadeIn(tcap),
                  run_time=2.0)
        hold(self, tcap, at_least=2.5)

        # the walk's lattice points in the window
        states, _ = orbit_states(p, r)
        win = {}
        for s in states:
            for v in (s.nu, s.other_end()):
                if in_window(v, p, r):
                    win[(round(qs1(v), 6), lv1(v))] = Cl(v) % 5
        pts = VGroup(*[
            Dot([X(x), Y(l), 0], radius=0.075, color=LEFT_C if c == 0 else RIGHT_C)
            for (x, l), c in win.items()])
        wcap = VGroup(Dot(radius=0.06, color=LEFT_C), T("left", 18),
                      Dot(radius=0.06, color=RIGHT_C),
                      T(f"right centres in the window, orbit of p ({len(states)} positions)", 18)
                      ).arrange(RIGHT, buff=0.1)
        wcap.next_to(tcap, DOWN, aligned_edge=LEFT, buff=0.14)
        self.play(LaggedStart(*[FadeIn(d, scale=1.6) for d in pts], lag_ratio=0.08),
                  FadeIn(wcap), run_time=2.0)
        hold(self, wcap, at_least=2.0)

        # ---------------- the strip: the lens bound ----------------------------------------------
        self.play(FadeOut(steps), run_time=0.5)
        lensc = VGroup(
            T("To climb (+3) from a left centre to a right centre", 20),
            T("that is also in the window, the point must lie in", 20),
            row("the lens of both disks. Projected on", "$u$:", size=20),
            M(r"|\psi - Z| \le L(r) = \tfrac12\sqrt{7-4\varphi}\,\sqrt{r^2-1},", 26),
            T("attained at the lens tips.", 20),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.1).next_to(defs, DOWN, aligned_edge=LEFT,
                                                             buff=0.35)
        # the lens tips and their projection onto the u direction (inset)
        h = math.sqrt(r * r - 1)
        tips = VGroup(Dot(fr(complex(0, h)), radius=0.05, color=GOOD),
                      Dot(fr(complex(0, -h)), radius=0.05, color=GOOD))
        ud = U / abs(U)
        uline = Line(fr(-2.3 * ud), fr(2.3 * ud), color=GOOD, stroke_width=2)
        proj = [complex(0, h), complex(0, -h)]
        feet = [(z.real * ud.real + z.imag * ud.imag) * ud for z in proj]
        drops = VGroup(*[DashedLine(fr(z), fr(f), color=GOOD, stroke_width=1.5, dash_length=0.05)
                         for z, f in zip(proj, feet)])
        bracket = Line(fr(feet[0]), fr(feet[1]), color=GOOD, stroke_width=6)
        ulab = M("u", 24, GOOD).next_to(fr(2.3 * ud), DOWN, buff=0.05)
        self.play(FadeIn(lensc), Create(uline), FadeIn(ulab), run_time=1.0)
        hold(self, lensc, ulab)
        self.play(FadeIn(tips), Create(drops), Create(bracket), run_time=1.0)
        strip = Rectangle(width=X(Z + L) - X(Z - L), height=Y(27) - Y(-27), stroke_width=0)
        strip.set_fill(GOOD, opacity=0.13).move_to([(X(Z - L) + X(Z + L)) / 2, (Y(27) + Y(-27)) / 2,
                                                    0])
        sl = DashedLine([X(Z - L), Y(-27), 0], [X(Z - L), Y(27), 0], color=GOOD, stroke_width=2)
        sr = DashedLine([X(Z + L), Y(-27), 0], [X(Z + L), Y(27), 0], color=GOOD, stroke_width=2)
        slab = row("strip of width", "$2L(r)$", size=17, color=GOOD).move_to(
            [(X(Z - L) + X(Z + L)) / 2, Y(27) + 0.22, 0])
        self.play(Indicate(bracket, color=GOOD), run_time=0.8)
        self.play(FadeIn(strip), Create(sl), Create(sr), FadeIn(slab), run_time=1.2)
        self.bring_to_front(teeth, pts)
        hold(self, slab, at_least=3.0)

        # ---------------- the walls ---------------------------------------------------------
        walls = VGroup()
        wlabels = VGroup()
        for q in qs:
            if is_cut_level(q, Z, L):
                walls.add(Line([xl, Y(5 * q), 0], [xr, Y(5 * q), 0], color=HOT, stroke_width=5))
                wlabels.add(T("cut level", 18, HOT).next_to([xr, Y(5 * q), 0], UP, buff=0.06)
                            .shift(0.55 * LEFT))
        self.play(FadeOut(lensc), run_time=0.4)
        cutc = VGroup(
            T("A cut level has no tooth inside the strip: no", 20),
            T("left centre on it can climb to a right centre in", 20),
            T("the window, so the walk's points in the window", 20),
            T("never pass it (and likewise from below).", 20),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.1).next_to(defs, DOWN, aligned_edge=LEFT,
                                                             buff=0.35)
        self.play(Create(walls), FadeIn(wlabels), FadeIn(cutc), run_time=1.2)
        self.bring_to_front(teeth, pts)
        hold(self, wlabels, cutc)
        band = Rectangle(width=xr - xl + 0.3, height=Y(20) - Y(-20), stroke_width=0)
        band.set_fill(HOT, opacity=0.06).move_to([(xl + xr) / 2, (Y(20) + Y(-20)) / 2, 0])
        self.play(FadeIn(band), run_time=0.8)
        self.wait(3.0)

        # ---------------- why cut levels exist, and the conclusion ------------------------------
        self.play(FadeOut(cutc), run_time=0.4)
        why = VGroup(
            row("Strip width", "$<\\delta$", "exactly when", "$r<\\sqrt{3+\\varphi}$.", size=20),
            T("The golden shift then puts some row's teeth", 20),
            T("outside the strip, above and below, within a", 20),
            T("bound that depends only on r.", 20),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.1).next_to(defs, DOWN, aligned_edge=LEFT,
                                                             buff=0.35)
        self.play(FadeIn(why), run_time=1.0)
        hold(self, why, at_least=4.0)
        concl = VGroup(
            row("The same with", "$\\zeta u$", "gives a second band.", size=20),
            T("Two bands and the window leave finitely many", 20),
            T("lattice points: every orbit has at most N(r)", 20),
            T("points, so GG₅(r) is finite.", 20),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.1).next_to(why, DOWN, aligned_edge=LEFT,
                                                             buff=0.3)
        self.play(FadeOut(why), run_time=0.4)
        concl.next_to(defs, DOWN, aligned_edge=LEFT, buff=0.35)
        self.play(FadeIn(concl), run_time=1.2)
        hold(self, concl, at_least=4.5)

"""B4 - Monotonicity: enlarging the radius only enlarges orbits.

Render:  manim -qh scenes/b4_monotone.py B4Monotone
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import numpy as np
from manim import *  # noqa: F401,F403

from lib.geometry import E, RC, direct_orbit
from lib.style import (
    CHORD_C, FAINT, GOOD, HOT, INK, LEFT_C, LENS_C, MUTED, RIGHT_C, Frame, M, T, hold, lens_shape,
    row,
)

STAGES = [1.0, 1.9, 2.0, 2.05, 2.1, 2.13]


def key(z):
    return (round(z.real, 7), round(z.imag, 7))


def count_tex(n):
    """The number n in math, with a thin space as the thousands separator (2\\,543)."""
    return M(f"{n:,}".replace(",", r"\,"), 30)


class B4Monotone(Scene):
    def construct(self):
        fr = Frame(scale=1.0, origin=(-3.45, -0.35))
        title = T("Monotone in r: a larger radius only adds positions", 30,
                  weight="BOLD").to_corner(UL, buff=0.3)
        self.add(title)
        hold(self, title)
        rt = ValueTracker(STAGES[0])

        def disks():
            r = rt.get_value()
            g = VGroup()
            for c, col in ((-1, LEFT_C), (1, RIGHT_C)):
                circ = Circle(radius=fr.len(r), color=col, stroke_width=2.5).move_to(
                    fr(complex(c, 0)))
                circ.set_fill(col, opacity=0.07)
                g.add(circ, Dot(fr(complex(c, 0)), radius=0.04, color=col))
            g.add(lens_shape(fr, r, opacity=0.12))
            return g

        D = always_redraw(disks)
        r_lab = VGroup(M("r =", 30), DecimalNumber(STAGES[0], num_decimal_places=3, font_size=30,
                                                   color=INK)).arrange(RIGHT, buff=0.15)
        r_lab[1].add_updater(lambda m: m.set_value(rt.get_value()))
        n_lab = VGroup(T("points in the orbit of 0:", 22, MUTED),
                       count_tex(0)).arrange(RIGHT, buff=0.18)
        info = VGroup(r_lab, n_lab).arrange(DOWN, aligned_edge=LEFT, buff=0.2)
        info.move_to([0.35, 2.45, 0], aligned_edge=LEFT)
        o = Dot(fr(0j), radius=0.06, color=INK)
        self.play(FadeIn(D), FadeIn(info), FadeIn(o), run_time=1.0)
        hold(self, info)

        seen = {}
        all_dots = VGroup()
        self.add(all_dots)
        prev_new = None
        for k, r in enumerate(STAGES):
            if k > 0:
                self.play(rt.animate.set_value(r), run_time=1.6, rate_func=smooth)
            pts = direct_orbit(0j, r)
            new = [z for z in pts if key(z) not in seen]
            size = 0.05 if len(pts) < 200 else (0.03 if len(pts) < 1000 else 0.018)
            nd = VGroup(*[Dot(fr(z), radius=size, color=GOOD) for z in new])
            for z in new:
                seen[key(z)] = z
            count = count_tex(len(pts)).move_to(n_lab[1], aligned_edge=LEFT)
            anims = [Transform(n_lab[1], count)]
            if prev_new is not None:
                anims.append(prev_new.animate.set_color(INK))
            if len(nd):
                anims.append(FadeIn(nd, scale=1.5))
            self.play(*anims, run_time=1.0)
            hold(self, count)
            all_dots.add(nd)
            prev_new = nd
            if k == 0:
                why = VGroup(
                    T("A turn that moves a point at radius r", 20),
                    T("moves it the same way at every larger radius:", 20),
                    T("the point lies in the smaller disk, hence in the", 20),
                    T("larger one. A turn that does nothing at radius r", 20),
                    T("is simply left out of the word.", 20),
                ).arrange(DOWN, aligned_edge=LEFT, buff=0.08).next_to(info, DOWN,
                                                                     aligned_edge=LEFT, buff=0.45)
                self.play(FadeIn(why), run_time=1.0)
                hold(self, why, at_least=3.0)
        self.play(prev_new.animate.set_color(INK), run_time=0.5)
        legend = VGroup(Dot(radius=0.06, color=GOOD), T("new at this radius", 20, MUTED),
                        Dot(radius=0.06, color=INK), T("already there", 20, MUTED)).arrange(
            RIGHT, buff=0.15).next_to(why, DOWN, aligned_edge=LEFT, buff=0.35)
        self.play(FadeIn(legend), run_time=0.5)
        hold(self, legend)
        so = VGroup(
            row("So", "$r\\le r'$", "gives", "$\\mathrm{orbit}_r(p)\\subseteq\\mathrm{orbit}_{r'}(p)$.",
                size=20),
            T("Finite at r′ ⇒ finite at r (orbits stay bounded);", 20),
            T("infinite at r ⇒ infinite at every larger radius.", 20),
            row("At", "$r=\\sqrt{3+\\varphi}$", "the orbit of 0 is infinite.", size=20),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.1).next_to(legend, DOWN, aligned_edge=LEFT,
                                                             buff=0.35)
        self.play(FadeIn(so), run_time=1.2)
        hold(self, so, at_least=4.5)

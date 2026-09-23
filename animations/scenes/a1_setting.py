"""A1 - The two disks at the critical radius, the lens, and the chord E'E.

Render:  manim -qh scenes/a1_setting.py A1Setting
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import numpy as np
from manim import *  # noqa: F401,F403

from lib.geometry import CC, E, F, G, PHI, RC, chord_point, PIECES
from lib.style import (
    BG, CHORD_C, FAINT, HOT, I1_C, I2_C, I3_C, INK, LEFT_C, LENS_C, MUTED, PIECE_C, RIGHT_C,
    Frame, M, T, disk, lens_shape, seg,
)
from lib.anim import turn_anims, turn_arrow


class A1Setting(Scene):
    def construct(self):
        fr = Frame(scale=1.28, origin=(-1.95, -0.25))
        r = RC

        title = T("Two disks, five-fold turns", size=34, weight="BOLD").to_corner(UL, buff=0.35)
        self.add(title)

        L = disk(fr, -1, r, LEFT_C)
        R = disk(fr, 1, r, RIGHT_C)
        self.play(FadeIn(L[0]), Create(L[1]), FadeIn(R[0]), Create(R[1]), run_time=1.6)
        self.play(FadeIn(L.marks), FadeIn(R.marks), run_time=0.6)
        cl = M("-1", 28, LEFT_C).next_to(fr(-1 + 0j), UP, buff=0.1)
        cr = M("+1", 28, RIGHT_C).next_to(fr(1 + 0j), DOWN, buff=0.1)
        self.play(FadeIn(cl), FadeIn(cr), run_time=0.5)

        # --- the two turns ------------------------------------------------------------------
        panel_x = 2.75
        ta = M(r"a:\ z\mapsto \zeta^{-1}(z+1)-1", 30, LEFT_C)
        ta2 = T("left disk, 72° clockwise", 22, MUTED)
        tb = M(r"b:\ z\mapsto \zeta^{-1}(z-1)+1", 30, RIGHT_C)
        tb2 = T("right disk, 72° clockwise", 22, MUTED)
        zeta = M(r"\zeta=e^{2\pi i/5}", 30)
        panel = VGroup(zeta, ta, ta2, tb, tb2).arrange(DOWN, aligned_edge=LEFT, buff=0.18)
        ta2.shift(0.05 * UP)
        tb2.shift(0.05 * UP)
        panel.move_to([panel_x, 2.2, 0], aligned_edge=LEFT)
        self.play(FadeIn(zeta), FadeIn(ta), FadeIn(ta2), run_time=0.8)
        arr = turn_arrow(fr, "a", r, LEFT_C)
        self.play(Create(arr), run_time=0.5)
        self.play(*turn_anims(fr, "a", [L.marks]), run_time=1.3)
        self.play(FadeOut(arr), run_time=0.3)
        self.play(FadeIn(tb), FadeIn(tb2), run_time=0.6)
        arr = turn_arrow(fr, "b", r, RIGHT_C)
        self.play(Create(arr), run_time=0.5)
        self.play(*turn_anims(fr, "b", [R.marks]), run_time=1.3)
        self.play(FadeOut(arr), run_time=0.3)

        # --- the lens ------------------------------------------------------------------------
        lens = lens_shape(fr, r)
        lens_lab = T("the lens", 24, LENS_C).move_to(fr(0 + 1.45j))
        self.play(FadeIn(lens), FadeIn(lens_lab), run_time=1.0)
        self.wait(1.2)

        # --- the chord E'E -------------------------------------------------------------------
        Ep = -E
        chord = seg(fr, Ep, E, CHORD_C, width=4)
        o_dot = Dot(fr(0j), radius=0.04, color=INK)
        self.play(FadeIn(o_dot), Create(chord), run_time=1.2)
        dE = Dot(fr(E), radius=0.065, color=INK)
        dEp = Dot(fr(Ep), radius=0.065, color=INK)
        lE = M("E", 30).next_to(fr(E), UR, buff=0.06)
        lEp = M("E'", 30).next_to(fr(Ep), DL, buff=0.06)
        self.play(FadeIn(dE), FadeIn(dEp), FadeIn(lE), FadeIn(lEp), run_time=0.6)

        rad_l = DashedLine(fr(-1 + 0j), fr(E), color=LEFT_C, stroke_width=2.5, dash_length=0.08)
        rad_r = DashedLine(fr(1 + 0j), fr(Ep), color=RIGHT_C, stroke_width=2.5, dash_length=0.08)
        self.play(Create(rad_l), Create(rad_r), run_time=1.0)
        fE = VGroup(
            M(r"E=\zeta-\zeta^{2}", 30),
            M(r"|E+1| = r", 30, LEFT_C),
            M(r"|E'-1| = r", 30, RIGHT_C),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.16).move_to([panel_x, 0.05, 0], aligned_edge=LEFT)
        fE.align_to(panel, LEFT)
        self.play(FadeIn(fE), run_time=0.8)
        self.wait(1.0)
        note = T("E on the rim of the left disk,\nE' on the rim of the right disk", 20, MUTED,
                 line_spacing=0.8).next_to(fE, DOWN, aligned_edge=LEFT, buff=0.2)
        self.play(FadeIn(note), run_time=0.6)
        self.wait(2.0)

        # --- the points F', G', G, F and the three pieces -------------------------------------
        pieces = VGroup()
        for pc in PIECES:
            pieces.add(seg(fr, chord_point(pc["s0"]), chord_point(pc["s1"]), PIECE_C[pc["name"]],
                           width=9))
        ticks = VGroup()
        labels = VGroup()
        pts = [(-1, "E'"), (-CC, "F'"), (1 - 2 * CC, "G'"), (2 * CC - 1, "G"), (CC, "F"), (1, "E")]
        nrm = 1j * E / abs(E)
        for s, name in pts:
            z = chord_point(s)
            ticks.add(Line(fr(z - 0.07 * nrm), fr(z + 0.07 * nrm), color=INK, stroke_width=2.5))
            if name in ("E", "E'"):
                continue
            off = 0.25 if name in ("F", "G'") else -0.25
            labels.add(M(name, 26).move_to(fr(z + off * nrm)))
        self.play(FadeOut(rad_l), FadeOut(rad_r), run_time=0.4)
        self.play(Create(ticks), FadeIn(labels), run_time=0.8)
        self.play(LaggedStart(*[Create(p) for p in pieces], lag_ratio=0.5), run_time=1.6)
        self.bring_to_front(dE, dEp)

        fF = VGroup(
            M(r"F=\tfrac{1}{\varphi}E,\quad G=2F-E", 28),
            M(r"\text{primes: } X'=-X", 26, MUTED),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.14)
        fF.next_to(note, DOWN, aligned_edge=LEFT, buff=0.3)
        legend = VGroup()
        for name, c, tex in (("I1", I1_C, r"I_1=[E',F']"), ("I2", I2_C, r"I_2=[F',G']"),
                             ("I3", I3_C, r"I_3=[G',E]")):
            sw = Line(ORIGIN, 0.45 * RIGHT, color=c, stroke_width=9)
            legend.add(VGroup(sw, M(tex, 26)).arrange(RIGHT, buff=0.15))
        legend.arrange(DOWN, aligned_edge=LEFT, buff=0.12).next_to(fF, DOWN, aligned_edge=LEFT,
                                                                     buff=0.25)
        self.play(FadeIn(fF), run_time=0.6)
        self.play(FadeIn(legend), run_time=0.8)

        # --- the number ------------------------------------------------------------------------
        num = M(r"r=\sqrt{3+\varphi}=2.148961\ldots", 34).to_corner(DL, buff=0.35)
        num.shift(0.1 * UP)
        self.play(Write(num), run_time=1.2)
        self.wait(4.0)

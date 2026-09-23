"""B1 - Behind every position, a lattice point: the point's-eye view of the puzzle.

Render:  manim -qh scenes/b1_lattice.py B1Lattice
"""
import cmath
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import numpy as np
from manim import *  # noqa: F401,F403

from lib.geometry import (
    ANGLE, CENTRE, TURN, State, conj_pt, in_window, orbit_states, pt, state_step, turn,
)
from lib.style import (
    row, FAINT, GOOD, HOT, INK, LEFT_C, LENS_C, MUTED, RIGHT_C, BG, Frame, M, T, disk, lens_shape,
)

P0 = -0.1722 + 0.0773j
R0 = 2.0
DEMO = "abab"


class B1Lattice(Scene):
    def construct(self):
        p, r = P0, R0
        fr = Frame(scale=0.75, origin=(-3.15, -0.35))
        title = T("Behind every position, a lattice point", 32, weight="BOLD").to_corner(UL,
                                                                                         buff=0.3)
        self.add(title)
        rlab = M(r"r = 2 < \sqrt{3+\varphi}", 30).to_corner(UR, buff=0.35)
        self.add(rlab)

        L = disk(fr, -1, r, LEFT_C, teeth=True)
        R = disk(fr, 1, r, RIGHT_C, teeth=True)
        self.play(FadeIn(L), FadeIn(R), run_time=0.8)
        pd = Dot(fr(p), radius=0.08, color=INK)
        halo = Circle(radius=0.16, color=INK, stroke_width=2).move_to(fr(p))
        plab = M("p", 30).next_to(pd, DR, buff=0.12)
        self.play(FadeIn(pd), Create(halo), FadeIn(plab), run_time=0.6)

        # ---- 1. the usual view: the point moves -------------------------------------------
        cap = T("The usual view: the disks turn, the point moves.", 20, MUTED)
        cap.move_to([-3.15, -3.7, 0])
        self.play(FadeIn(cap), run_time=0.5)
        z = p
        trail = VGroup()
        for letter in DEMO:
            c = CENTRE[letter]
            znew = turn(letter, z, r)
            arc = Arc(radius=fr.len(abs(z - c)), start_angle=cmath.phase(z - c),
                      angle=ANGLE[letter], arc_center=fr(complex(c, 0)), color=MUTED,
                      stroke_width=2)
            trail.add(arc)
            dm = L if c < 0 else R
            self.play(Rotate(dm.marks, ANGLE[letter], about_point=fr(complex(c, 0))),
                      MoveAlongPath(VGroup(pd, halo), arc), Create(arc),
                      plab.animate.next_to(fr(znew), DR, buff=0.12), run_time=1.0)
            z = znew
        word = M(r"a\,b\,a\,b", 34).next_to(rlab, DOWN, aligned_edge=RIGHT, buff=0.3)
        self.play(FadeIn(word), run_time=0.4)
        self.wait(0.5)

        # ---- 2. the point's view: the puzzle moves ------------------------------------------
        cap2 = T("The point's view: the point stays; the pair of disks turns about a centre.", 19,
                 MUTED).move_to([-2.9, -3.7, 0])
        self.play(FadeOut(trail), VGroup(pd, halo).animate.move_to(fr(p)),
                  plab.animate.next_to(fr(p), DR, buff=0.12), FadeOut(cap), run_time=1.0)
        cap = cap2
        self.play(FadeIn(cap), run_time=0.5)
        # reset the teeth
        L2 = disk(fr, -1, r, LEFT_C)
        R2 = disk(fr, 1, r, RIGHT_C)
        self.remove(L, R)
        self.add(L2, R2)
        self.bring_to_front(pd, halo, plab)
        cm = Dot(fr(-1 + 0j), radius=0.07, color=LEFT_C)
        cp = Dot(fr(1 + 0j), radius=0.07, color=RIGHT_C)
        bar = Line(fr(-1 + 0j), fr(1 + 0j), color=INK, stroke_width=4)
        pair = VGroup(L2, R2, bar, cm, cp)
        self.play(Create(bar), FadeIn(cm), FadeIn(cp), run_time=0.6)
        s = State(0, (0, 0, 0, 0))
        centre_trail = VGroup()
        for k, letter in enumerate(DEMO):
            cmin, cplus = s.centres(p)
            about = cmin if letter in "aA" else cplus
            ang = -ANGLE[letter]  # the opposite turn, in the point's frame
            ghost = VGroup(Dot(fr(cmin), radius=0.045, color=LEFT_C),
                           Dot(fr(cplus), radius=0.045, color=RIGHT_C),
                           Line(fr(cmin), fr(cplus), color=INK, stroke_width=1.5)).set_opacity(
                0.45)
            centre_trail.add(ghost)
            self.add(ghost)
            self.play(Rotate(pair, ang, about_point=fr(about)), run_time=1.1)
            s = state_step(s, letter, p, r)
        self.bring_to_front(pd, halo, plab)
        self.wait(0.4)

        # ---- 3. the centres are lattice points ------------------------------------------------
        box = VGroup(
            VGroup(T("left centre", 22, LEFT_C), M(r"2\nu-1", 28)).arrange(RIGHT, buff=0.2),
            VGroup(T("right centre", 22, RIGHT_C), M(r"2\nu-1+2\bar m", 28)).arrange(RIGHT,
                                                                                    buff=0.2),
            M(r"\nu\in\mathbb{Z}[\zeta],\quad m\in\{1,\zeta,\dots,\zeta^4\}", 28),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.14)
        box.move_to([1.2, 2.05, 0], aligned_edge=LEFT)
        self.play(FadeIn(box), run_time=0.8)
        self.wait(2.0)
        rule = VGroup(
            T("A turn about a centre is possible", 22),
            T("only if the point lies within r of it.", 22),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.08).next_to(box, DOWN, aligned_edge=LEFT,
                                                              buff=0.35)
        self.play(FadeIn(rule), run_time=0.6)
        win = DashedLine  # noqa: F841 (placeholder to keep imports tidy)
        window = DashedVMobject(Circle(radius=fr.len(r), color=GOOD, stroke_width=3).move_to(
            fr(p)), num_dashes=60)
        wlab = VGroup(DashedLine(ORIGIN, 0.5 * RIGHT, color=GOOD, stroke_width=3),
                      T("the window  |c − p| ≤ r", 20, GOOD)).arrange(RIGHT, buff=0.15)
        wlab.next_to(rule, DOWN, aligned_edge=LEFT, buff=0.25)
        self.play(Create(window), FadeIn(wlab), run_time=1.0)
        self.wait(2.0)

        # ---- 4. all positions of the orbit -------------------------------------------------------
        states, _ = orbit_states(p, r)
        self.play(FadeOut(pair), FadeOut(centre_trail), run_time=0.6)
        bars = VGroup()
        cdots = {}
        for st in states:
            a0, a1 = st.centres(p)
            bars.add(Line(fr(a0), fr(a1), color=INK, stroke_width=0.9).set_opacity(0.35))
            for v, col in ((st.nu, LEFT_C), (st.other_end(), RIGHT_C)):
                if v not in cdots:
                    c = 2 * pt(v) - 1
                    inside = in_window(v, p, r)
                    cdots[v] = Dot(fr(c), radius=0.05 if inside else 0.035,
                                   color=col if inside else MUTED)
        dots = VGroup(*cdots.values())
        cap3 = T(f"All {len(states)} positions of the orbit of p, as pairs of centres.", 20,
                 MUTED).move_to([-3.15, -3.7, 0])
        self.play(FadeOut(cap), run_time=0.3)
        cap = cap3
        self.play(FadeIn(cap), LaggedStart(*[Create(b) for b in bars], lag_ratio=0.02),
                  LaggedStart(*[FadeIn(d) for d in dots], lag_ratio=0.02), run_time=3.5)
        self.bring_to_front(pd, halo, plab)
        leg = VGroup(
            VGroup(Dot(radius=0.06, color=LEFT_C), T("left centres (can turn a)", 20)).arrange(
                RIGHT, buff=0.15),
            VGroup(Dot(radius=0.06, color=RIGHT_C), T("right centres (can turn b)",
                                                      20)).arrange(RIGHT, buff=0.15),
            VGroup(Dot(radius=0.045, color=MUTED), T("outside the window: cannot turn", 20)).arrange(
                RIGHT, buff=0.15),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.1).next_to(wlab, DOWN, aligned_edge=LEFT,
                                                             buff=0.2)
        self.play(FadeIn(leg), run_time=0.8)
        self.wait(2.5)

        # ---- 5. the hidden coordinates -------------------------------------------------------------
        dense = VGroup(
            row("$\\mathbb{Z}[\\zeta]$", "has rank 4, so it is dense in the plane:", size=20),
            T("finiteness is decided in the two hidden", 20),
            T("coordinates (the conjugate ζ ↦ ζ²).", 20),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.07)
        dense.next_to(leg, DOWN, aligned_edge=LEFT, buff=0.3)
        self.play(FadeIn(dense), run_time=0.8)
        self.wait(1.5)
        # inset: conjugates of the window centres
        ins_c = np.array([2.35, -2.9, 0.0])
        ins_s = 0.04
        frame_ins = RoundedRectangle(width=2.3, height=1.25, corner_radius=0.1, color=FAINT,
                                     stroke_width=1.5).move_to(ins_c)
        cl = VGroup()
        for v, d in cdots.items():
            w = 2 * conj_pt(v) - 1          # the centre 2v - 1, under zeta -> zeta^2
            cl.add(Dot(ins_c + ins_s * np.array([w.real, w.imag, 0]), radius=0.028,
                       color=d.get_color()))
        self.play(Create(frame_ins), FadeIn(cl), run_time=1.0)
        ins_lab = VGroup(T("the same centres,", 18, MUTED), T("conjugated:", 18, MUTED),
                         T("a bounded cloud", 18, MUTED)).arrange(DOWN, aligned_edge=LEFT,
                                                                  buff=0.05)
        ins_lab.next_to(frame_ins, RIGHT, buff=0.2)
        self.play(FadeIn(ins_lab), run_time=0.5)
        self.wait(4.0)

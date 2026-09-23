"""A5 - The three words together: an exchange of three pieces = a golden rotation.

Render:  manim -qh scenes/a5_exchange.py A5Exchange
"""
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import numpy as np
from manim import *  # noqa: F401,F403

from lib.geometry import CC, E, PHI, PIECES, RC, chord_point, rot
from lib.style import (
    CHORD_C, FAINT, HOT, INK, LEFT_C, LENS_C, MUTED, PIECE_C, RIGHT_C, Frame, M, T, disk,
    hold, lens_shape, seg,
)

ALPHA = 2 * CC          # rotation amount in t = s + 1 units (circle length 2)
BETA = 2 - 2 * CC


class A5Exchange(Scene):
    def construct(self):
        # --- small copy of the disks, top left ---------------------------------------------
        fr = Frame(scale=0.74, origin=(-4.6, 1.38))
        r = RC
        L = disk(fr, -1, r, LEFT_C, stroke_width=2.2)
        R = disk(fr, 1, r, RIGHT_C, stroke_width=2.2)
        lens = lens_shape(fr, r, opacity=0.14)
        chord = seg(fr, -E, E, CHORD_C, width=2).set_opacity(0.5)
        pcs_small = VGroup(*[seg(fr, chord_point(q["s0"]), chord_point(q["s1"]),
                                 PIECE_C[q["name"]], width=5) for q in PIECES])
        title = T("Three pieces, one golden rotation", 32, weight="BOLD").to_corner(UL, buff=0.3)
        self.add(title)
        hold(self, title)
        self.play(FadeIn(L), FadeIn(R), FadeIn(lens), FadeIn(chord), FadeIn(pcs_small),
                  run_time=1.0)

        # --- the unrolled chord ------------------------------------------------------------
        x0, x1, yb = 0.35, 6.55, 2.45
        W = x1 - x0

        def X(t):  # t in [0, 2]
            return np.array([x0 + W * t / 2, yb, 0.0])

        base = Line(X(0), X(2), color=CHORD_C, stroke_width=2).set_opacity(0.5)
        bars = VGroup(*[Line(X(q["s0"] + 1), X(q["s1"] + 1), color=PIECE_C[q["name"]],
                             stroke_width=12) for q in PIECES])
        names = ["E'", "F'", "G'", "G", "F", "E"]
        svals = [-1, -CC, 1 - 2 * CC, 2 * CC - 1, CC, 1]
        ticks = VGroup(*[Line(X(s + 1) + 0.13 * DOWN, X(s + 1) + 0.13 * UP, stroke_width=2)
                         for s in svals])
        tlabels = VGroup(*[M(n, 26).next_to(X(s + 1), DOWN, buff=0.2)
                           for n, s in zip(names, svals)])
        plabels = VGroup(*[M(f"I_{k + 1}", 28, PIECE_C[q['name']]).next_to(
            X((q["s0"] + q["s1"]) / 2 + 1), UP, buff=0.18) for k, q in enumerate(PIECES)])
        link = DashedLine(fr(0.35 * E + 0.45j), X(0.2) + 0.3 * DOWN + 0.2 * LEFT, color=FAINT,
                          stroke_width=1.5)
        self.play(TransformFromCopy(pcs_small, bars), FadeIn(base), run_time=1.3)
        self.play(FadeIn(ticks), FadeIn(tlabels), FadeIn(plabels), run_time=0.8)
        hold(self, tlabels, plabels)

        cap1 = VGroup(M(r"|I_1|=|I_2|", 28), M(r"|I_3| = 2\varphi\,|I_1|", 28),
                      M(r"|I_3| : |I_1\cup I_2| = \varphi", 28)).arrange(RIGHT, buff=0.5)
        cap1.move_to([3.45, 1.1, 0])
        self.play(FadeIn(cap1), run_time=0.8)
        hold(self, cap1, at_least=2.2)

        # --- the exchange ------------------------------------------------------------------
        lifts = [0.5 * UP, 0.5 * UP, 0.5 * DOWN]   # I3 passes below I1, I2
        self.play(*[b.animate.shift(l) for b, l in zip(bars, lifts)],
                  *[p.animate.shift(l) for p, l in zip(plabels, lifts)],
                  FadeOut(tlabels), run_time=0.6)
        moves = []
        for b, p, q in zip(bars, plabels, PIECES):
            d = X(q["s0"] + q["shift"] + 1) - X(q["s0"] + 1)
            moves += [b.animate.shift(d), p.animate.shift(d)]
        self.play(*moves, run_time=1.8)
        self.play(*[b.animate.shift(-l) for b, l in zip(bars, lifts)],
                  *[p.animate.shift(-l) for p, l in zip(plabels, lifts)],
                  FadeIn(tlabels), run_time=0.6)
        cap2 = VGroup(M(r"I_1, I_2 \mapsto +2F", 28, INK), M(r"I_3 \mapsto 2F-2E", 28, INK),
                      M(r"|E'E| : |2F| = \varphi", 28, INK)).arrange(RIGHT, buff=0.5)
        cap2.move_to(cap1)
        self.play(FadeOut(cap1), FadeIn(cap2), run_time=0.7)
        hold(self, tlabels, cap2, at_least=2.5)       # the point labels came back just before

        # --- glue the ends: a rotation of a circle ------------------------------------------
        cc_ = np.array([4.1, -1.8, 0.0])
        rad = 1.5

        def C(t):  # t in [0, 2): clockwise from the top
            th = PI / 2 - PI * t
            return cc_ + rad * np.array([math.cos(th), math.sin(th), 0.0])

        def arc_of(t0, t1, color, width=12):
            return Arc(radius=rad, start_angle=PI / 2 - PI * t0, angle=-PI * (t1 - t0),
                       arc_center=cc_, color=color, stroke_width=width)

        # current bars after the exchange sit at s0 + shift; draw the circle in the ORIGINAL order
        ring = Circle(radius=rad, color=CHORD_C, stroke_width=2).move_to(cc_).set_stroke(
            opacity=0.5)
        arcs = VGroup(*[arc_of(q["s0"] + 1, q["s1"] + 1, PIECE_C[q["name"]]) for q in PIECES])
        glue = M(r"\text{glue }E'\text{ to }E", 28, MUTED).next_to(ring, LEFT, buff=0.35).shift(
            1.1 * UP)
        # restore the unrolled chord to the original order for the morph
        self.play(*[b.animate.shift(X(q["s0"] + 1) - X(q["s0"] + q["shift"] + 1))
                    for b, q in zip(bars, PIECES)], FadeOut(plabels), run_time=0.9)
        self.play(FadeIn(ring), FadeIn(glue), run_time=0.5)
        hold(self, glue)
        self.play(LaggedStart(*[Create(a) for a in arcs], lag_ratio=0.6), run_time=1.6)
        top = Dot(C(0), radius=0.06, color=INK)
        top_l = M("E'\\equiv E", 26).next_to(C(0), UP, buff=0.42)
        self.play(FadeIn(top), FadeIn(top_l), run_time=0.5)
        hold(self, top_l)
        rot_txt = VGroup(
            M(r"t \mapsto t + \tfrac{2}{\varphi} \pmod 2", 30),
            T("t = position along E′E  (E′ = 0, E = 2)", 20, MUTED),
            T("a rotation by 1/φ of a full turn", 20, MUTED),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.12).move_to([-6.7, -1.05, 0], aligned_edge=LEFT)
        self.play(FadeIn(rot_txt), run_time=0.6)
        hold(self, rot_txt, at_least=1.5)
        self.play(Rotate(arcs, angle=-2 * PI * CC, about_point=cc_), run_time=2.0)
        self.wait(0.5)

        # --- the orbit of the origin -------------------------------------------------------
        orbit_hdr = T("the orbit of the origin", 24, weight="BOLD").next_to(rot_txt, DOWN,
                                                                            aligned_edge=LEFT,
                                                                            buff=0.3)
        self.play(FadeIn(orbit_hdr), arcs.animate.set_stroke(opacity=0.35), run_time=0.6)
        t = 1.0
        counter = VGroup(M("k =", 28), Integer(0, font_size=28, color=INK)).arrange(RIGHT,
                                                                                buff=0.12)
        counter.next_to(orbit_hdr, DOWN, aligned_edge=LEFT, buff=0.2)
        self.add(counter)
        hold(self, orbit_hdr, counter)
        dots_c, dots_x, dots_d = VGroup(), VGroup(), VGroup()

        def piece_of(t):
            s = t - 1
            for q in PIECES:
                if q["s0"] <= s < q["s1"] or (q["name"] == "I3" and abs(s - 1) < 1e-12):
                    return q
            raise ValueError

        def Cout(t):
            th = PI / 2 - PI * t
            return cc_ + (rad + 0.2) * np.array([math.cos(th), math.sin(th), 0.0])

        def add_point(t, k, big):
            col = INK if k == 0 else PIECE_C[piece_of(t)["name"]]
            if big:
                dc = Dot(Cout(t), radius=0.07, color=col)
                dx = Dot(X(t) + 0.28 * UP, radius=0.07, color=col)
                dd = Dot(fr(chord_point(t - 1)), radius=0.05, color=col)
            else:
                th = PI / 2 - PI * t
                u = np.array([math.cos(th), math.sin(th), 0.0])
                dc = Line(cc_ + (rad + 0.13) * u, cc_ + (rad + 0.3) * u, color=col,
                          stroke_width=1.6)
                dx = Line(X(t) + 0.2 * UP, X(t) + 0.36 * UP, color=col, stroke_width=1.6)
                dd = Dot(fr(chord_point(t - 1)), radius=0.018, color=col)
            dots_c.add(dc)
            dots_x.add(dx)
            dots_d.add(dd)
            return dc, dx, dd

        first = add_point(t, 0, True)
        self.play(*[FadeIn(d, scale=2) for d in first], run_time=0.5)
        for k in range(1, 9):
            t_new = rot(t, ALPHA, BETA)
            path = Arc(radius=rad + 0.2, start_angle=PI / 2 - PI * t, angle=-PI * ALPHA,
                       arc_center=cc_, color=MUTED, stroke_width=2).set_stroke(opacity=0.8)
            path.add_tip(tip_length=0.15, tip_width=0.15)
            new = add_point(t_new, k, True)
            self.play(Create(path), run_time=0.45)
            counter[1].set_value(k)
            self.play(*[FadeIn(d, scale=2) for d in new], FadeOut(path), run_time=0.35)
            t = t_new
        # fast forward
        batch = []
        for k in range(9, 300):
            t = rot(t, ALPHA, BETA)
            batch.append(add_point(t, k, False))
            if len(batch) == 30 or k == 299:
                counter[1].set_value(k)
                self.play(*[FadeIn(d) for trip in batch for d in trip], run_time=0.35)
                batch = []
        never = VGroup(
            T("1/φ is irrational: the orbit never closes.", 22, INK),
            T("Infinitely many positions  ⇒  GG₅(√(3+φ)) is infinite.", 22,
              INK),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.12)
        never.next_to(counter, DOWN, aligned_edge=LEFT, buff=0.22)
        self.play(FadeIn(never), run_time=1.0)
        hold(self, never, at_least=4.5)

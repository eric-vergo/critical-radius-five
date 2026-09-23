"""A2-A4 - The three words of the interval exchange, turn by turn.

Render:  manim -qh scenes/a2_a4_words.py A2WordOne A3WordTwo A4WordThree
"""
import cmath
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import numpy as np
from manim import *  # noqa: F401,F403

from lib.geometry import ANGLE, CC, CENTRE, E, PIECES, RC, chord_point, segment_trace
from lib.style import (
    CHORD_C, FAINT, HOT, INK, LEFT_C, LENS_C, MUTED, PIECE_C, RIGHT_C, Frame, M, T, disk,
    lens_shape, seg,
)
from lib.anim import turn_arrow

LETTER_TEX = {"a": r"a", "A": r"a^{-1}", "b": r"b", "B": r"b^{-1}"}
POINT_NAMES = {-1.0: "E'", -CC: "F'", 1 - 2 * CC: "G'", 2 * CC - 1: "G", CC: "F", 1.0: "E"}


def pname(s):
    for k, v in POINT_NAMES.items():
        if abs(k - s) < 1e-9:
            return v
    raise KeyError(s)


class WordScene(Scene):
    piece_index = 0
    heading = ""
    shift_tex = ""

    def construct(self):
        pc = PIECES[self.piece_index]
        col = PIECE_C[pc["name"]]
        fr = Frame(scale=1.28, origin=(-1.95, -0.25))
        r = RC

        L = disk(fr, -1, r, LEFT_C)
        R = disk(fr, 1, r, RIGHT_C)
        lens = lens_shape(fr, r, opacity=0.10)
        chord = seg(fr, -E, E, CHORD_C, width=2.5).set_opacity(0.45)
        faint_pieces = VGroup(*[
            seg(fr, chord_point(q["s0"]), chord_point(q["s1"]), PIECE_C[q["name"]], width=5)
            .set_opacity(0.28) for q in PIECES])
        self.add(L, R, lens, chord, faint_pieces)

        title = T(self.heading, size=32, weight="BOLD").to_corner(UL, buff=0.35)
        self.add(title)

        # the word, letter by letter
        letters = VGroup(*[M(LETTER_TEX[x], 40) for x in pc["word"]]).arrange(RIGHT, buff=0.2)
        word_lab = T("the word (read left to right)", 22, MUTED)
        src = VGroup(T("carries", 24), M(self.src_tex, 30)).arrange(RIGHT, buff=0.15)
        panel = VGroup(word_lab, letters, src).arrange(DOWN, aligned_edge=LEFT, buff=0.22)
        panel.move_to([2.75, 2.35, 0], aligned_edge=LEFT)
        self.play(FadeIn(title), FadeIn(word_lab), FadeIn(letters), run_time=0.8)

        p0, q0 = chord_point(pc["s0"]), chord_point(pc["s1"])
        moving = seg(fr, p0, q0, col, width=9)
        dp = Dot(fr(p0), radius=0.06, color=INK)
        dq = Dot(fr(q0), radius=0.06, color=INK)
        mover = VGroup(moving, dp, dq)
        lp = M(pname(pc["s0"]), 28).next_to(fr(p0), DOWN + LEFT * 0.3, buff=0.08)
        lq = M(pname(pc["s1"]), 28).next_to(fr(q0), UP + RIGHT * 0.3, buff=0.08)
        self.play(Create(moving), FadeIn(dp), FadeIn(dq), FadeIn(lp), FadeIn(lq), FadeIn(src),
                  run_time=1.0)
        self.wait(1.2)
        self.play(FadeOut(lp), FadeOut(lq), run_time=0.3)

        trace = segment_trace(pc["word"], p0, q0, r)
        ghosts = VGroup()
        contact_note = None
        for k, letter in enumerate(pc["word"]):
            c = CENTRE[letter]
            disk_m = L if c < 0 else R
            dcol = LEFT_C if c < 0 else RIGHT_C
            (pk, qk), (pn, qn) = trace[k], trace[k + 1]
            # highlight the letter and the disk
            self.play(letters[k].animate.set_color(dcol).scale(1.18),
                      disk_m[1].animate.set_stroke(width=6), run_time=0.35)
            # contacts with the rim before this turn
            rings = VGroup()
            for z in (pk, qk):
                if abs(abs(z - c) - r) < 1e-9:
                    rings.add(Circle(radius=0.16, color=HOT, stroke_width=4).move_to(fr(z)))
            if len(rings):
                if contact_note is None:
                    contact_note = T("on the rim", 22, HOT)
                note = contact_note.copy().next_to(rings[0], UP, buff=0.08)
                self.play(Create(rings), FadeIn(note), run_time=0.45)
            arr = turn_arrow(fr, letter, r, dcol)
            ghost = moving.copy().set_opacity(0.30).set_stroke(width=5)
            ghosts.add(ghost)
            self.add(ghost)
            mid_old = (pk + qk) / 2
            path = Arc(radius=fr.len(abs(mid_old - c)), start_angle=cmath.phase(mid_old - c),
                       angle=ANGLE[letter], arc_center=fr(complex(c, 0)), color=col,
                       stroke_width=2).set_stroke(opacity=0.55)
            anims = [Rotate(mover, angle=ANGLE[letter], about_point=fr(complex(c, 0))),
                     Rotate(disk_m.marks, angle=ANGLE[letter], about_point=fr(complex(c, 0))),
                     Create(path)]
            if len(rings):
                anims.append(Rotate(rings, angle=ANGLE[letter], about_point=fr(complex(c, 0))))
            self.play(Create(arr), run_time=0.3)
            self.play(*anims, run_time=1.25, rate_func=smooth)
            ghosts.add(path)
            fades = [FadeOut(arr), letters[k].animate.set_color(MUTED).scale(1 / 1.18),
                     disk_m[1].animate.set_stroke(width=3)]
            if len(rings):
                marks = VGroup(*[Dot(fr(z), radius=0.055, color=HOT) for z in (pk, qk)
                                 if abs(abs(z - c) - r) < 1e-9])
                ghosts.add(marks)
                fades += [FadeOut(rings), FadeOut(note), FadeIn(marks)]
            self.play(*fades, run_time=0.35)

        # the result: a translation along the chord
        p1, q1 = trace[-1]
        tgt_l = M(pname(pc["s0"] + pc["shift"]), 28).next_to(fr(p1), DOWN + LEFT * 0.3, buff=0.08)
        tgt_r = M(pname(pc["s1"] + pc["shift"]), 28).next_to(fr(q1), UP + RIGHT * 0.3, buff=0.08)
        self.play(FadeIn(tgt_l), FadeIn(tgt_r), run_time=0.5)
        nrm = 1j * E / abs(E)
        off = 0.42 * nrm if self.piece_index != 2 else -0.42 * nrm
        a0, a1 = (p0 + q0) / 2 + off, (p1 + q1) / 2 + off
        orig = seg(fr, p0, q0, col, width=6).set_opacity(0.55)
        self.add(orig)
        arrow = Arrow(fr(a0), fr(a1), buff=0, color=col, stroke_width=5,
                      max_tip_length_to_length_ratio=0.12)
        self.play(GrowArrow(arrow), run_time=0.9)
        res = VGroup(
            VGroup(T("onto", 24), M(self.dst_tex, 30)).arrange(RIGHT, buff=0.15),
            VGroup(T("a translation by", 24, col), M(self.shift_tex, 32, col)).arrange(RIGHT,
                                                                                    buff=0.15),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.16)
        res.next_to(panel, DOWN, aligned_edge=LEFT, buff=0.3)
        self.play(FadeIn(res), run_time=0.8)
        foot = T("Red: an endpoint lies exactly on the rim of the disk about to turn;"
                 " at any smaller radius that turn would split the segment.", 17, MUTED)
        foot.to_edge(DOWN, buff=0.3)
        self.play(FadeIn(foot), run_time=0.8)
        self.wait(4.0)


class A2WordOne(WordScene):
    piece_index = 0
    heading = "Word 1:  the piece I₁"
    src_tex = r"I_1=[E',F']"
    dst_tex = r"[G,F]"
    shift_tex = r"2F"


class A3WordTwo(WordScene):
    piece_index = 1
    heading = "Word 2:  the piece I₂"
    src_tex = r"I_2=[F',G']"
    dst_tex = r"[F,E]"
    shift_tex = r"2F"


class A4WordThree(WordScene):
    piece_index = 2
    heading = "Word 3:  the piece I₃"
    src_tex = r"I_3=[G',E]"
    dst_tex = r"[E',G]"
    shift_tex = r"2F-2E"

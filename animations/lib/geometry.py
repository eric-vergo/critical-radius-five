"""Exact geometry of the two-disk group GG5, for figures only.

Conventions (as in the Lean development):

* closed disks of radius ``r`` about ``-1`` and ``+1`` in the complex plane;
* ``zeta = exp(2 pi i / 5)``;
* ``a(z) = zeta^-1 (z + 1) - 1`` on ``|z + 1| <= r`` (identity outside): the left disk turns
  clockwise by 72 degrees; ``b(z) = zeta^-1 (z - 1) + 1`` on ``|z - 1| <= r``;
  capital letters are inverses (``A = a^-1``, ``B = b^-1``);
* words act left to right: the word ``"ab"`` first applies ``a``, then ``b``.

Floating point is used only to draw pictures.  The lattice ``Z[zeta_5] = Z[zeta_10]`` is handled
with integer coordinates in the basis ``1, w, w^2, w^3`` (``w = exp(2 pi i / 10)``), so levels and
classes are exact integers.  (The Lean library, ``CriticalRadiusFive/Cyclotomic.lean``, uses the
power basis ``1, zeta, zeta^2, zeta^3`` instead; both are bases of the same lattice.)
"""
from __future__ import annotations

import cmath
import math
from collections import deque
from dataclasses import dataclass

# ----------------------------------------------------------------------------------------------
# Numbers
# ----------------------------------------------------------------------------------------------

SQRT5 = math.sqrt(5.0)
PHI = (1.0 + SQRT5) / 2.0              # golden ratio
CC = PHI - 1.0                         # 1/phi = 2 cos(72 deg)
RC = math.sqrt(3.0 + PHI)              # the critical radius, 2.148961141749635...
ZETA = cmath.exp(2j * math.pi / 5)     # zeta_5
W10 = cmath.exp(1j * math.pi / 5)      # zeta_10, zeta_5 = W10**2
TURN = 2 * math.pi / 5                 # 72 degrees

# The chord E'E of Theorem 2 (z = s E, s in [-1, 1]).
E = ZETA - ZETA**2                     # |E + 1| = RC: E lies on the left circle at r = RC
F = CC * E                             # F = 1 - zeta + zeta^2 - zeta^3
G = 2 * F - E
S_F = CC                               # s-coordinate of F
S_G = 2 * CC - 1                       # s-coordinate of G

# The three pieces (s-intervals) and their translations (in s units of E).
PIECES = [
    dict(name="I1", word="AABAB", s0=-1.0, s1=-CC, shift=2 * CC),        # [E', F'] -> [G, F]
    dict(name="I2", word="ababb", s0=-CC, s1=1 - 2 * CC, shift=2 * CC),  # [F', G'] -> [F, E]
    dict(name="I3", word="abaBAB", s0=1 - 2 * CC, s1=1.0, shift=2 * CC - 2),  # [G', E] -> [E', G]
]


def chord_point(s: float) -> complex:
    return s * E


# ----------------------------------------------------------------------------------------------
# The turns
# ----------------------------------------------------------------------------------------------

CENTRE = {"a": -1.0, "A": -1.0, "b": 1.0, "B": 1.0}
ANGLE = {"a": -TURN, "A": TURN, "b": -TURN, "B": TURN}   # clockwise = negative angle


def in_disk(z: complex, c: float, r: float, tol: float = 1e-12) -> bool:
    return abs(z - c) <= r + tol


def turn(letter: str, z: complex, r: float) -> complex:
    """Apply one letter (a, A, b, B) at radius r to the point z."""
    c = CENTRE[letter]
    if not in_disk(z, c, r):
        return z
    return cmath.exp(1j * ANGLE[letter]) * (z - c) + c


def apply_word(word: str, z: complex, r: float) -> complex:
    for letter in word:
        z = turn(letter, z, r)
    return z


def segment_trace(word: str, p: complex, q: complex, r: float):
    """Images of the segment [p, q] after each prefix of ``word``.

    Returns a list of (p_k, q_k) and asserts that before each letter both endpoints lie in that
    letter's disk (then, by convexity, the whole segment turns rigidly)."""
    out = [(p, q)]
    for letter in word:
        c = CENTRE[letter]
        assert in_disk(p, c, r, 1e-9) and in_disk(q, c, r, 1e-9), (word, letter, p, q)
        p, q = turn(letter, p, r), turn(letter, q, r)
        out.append((p, q))
    return out


def rot(t: float, alpha: float = 2 * CC, beta: float = 2 - 2 * CC) -> float:
    """The rotation of the circle R/(alpha+beta)Z written on [0, alpha+beta)."""
    return t + alpha if t < beta else t - beta


def exchange_step(s: float) -> tuple[float, str]:
    """One step of the three-piece exchange on the chord (s-coordinate) and the word used."""
    for pc in PIECES:
        if pc["s0"] <= s < pc["s1"] or (pc["name"] == "I3" and s == 1.0):
            return s + pc["shift"], pc["word"]
    raise ValueError(s)


# ----------------------------------------------------------------------------------------------
# The lattice Z[zeta_5] = Z[zeta_10] in the basis 1, w, w^2, w^3 (w = zeta_10)
# ----------------------------------------------------------------------------------------------

Q4 = tuple  # (a, b, c, d) <-> a + b w + c w^2 + d w^3


def pt(v: Q4) -> complex:
    a, b, c, d = v
    return a + b * W10 + c * W10**2 + d * W10**3


def conj_pt(v: Q4) -> complex:
    """The Galois conjugate sigma(v), sigma: zeta_5 -> zeta_5^2 (i.e. w -> w^3)."""
    a, b, c, d = v
    w3 = W10**3
    return a + b * w3 + c * w3**2 + d * w3**3


def add(v: Q4, w: Q4) -> Q4:
    return tuple(x + y for x, y in zip(v, w))


def sub(v: Q4, w: Q4) -> Q4:
    return tuple(x - y for x, y in zip(v, w))


def shift(v: Q4) -> Q4:
    """Multiplication by w = zeta_10 (w^4 = w^3 - w^2 + w - 1)."""
    a, b, c, d = v
    return (-d, a + d, b - d, c + d)


def cj(v: Q4) -> Q4:
    """Complex conjugation."""
    a, b, c, d = v
    return (a + b, -b, b - d, -b - c)


def w_pow(k: int) -> Q4:
    v = (1, 0, 0, 0)
    for _ in range(k % 10):
        v = shift(v)
    return v


def z5_pow(j: int) -> Q4:
    """zeta_5^j = w^(2j)."""
    return w_pow(2 * (j % 5))


UNIT5 = [z5_pow(j) for j in range(5)]
assert UNIT5 == [(1, 0, 0, 0), (0, 0, 1, 0), (-1, 1, -1, 1), (0, -1, 0, 0), (0, 0, 0, -1)]


def AA1(v):
    a, b, c, d = v
    return 3 * a + b - 4 * c + d


def BB1(v):
    a, b, c, d = v
    return -2 * a - b + 2 * c - d


def AA2(v):
    a, b, c, d = v
    return -a - 3 * b + 3 * c + d


def BB2(v):
    a, b, c, d = v
    return a + 2 * b - 2 * c - d


def lv1(v) -> int:
    """The level of the first functional (u = 1 - zeta + zeta^2)."""
    return -AA1(v) - 3 * BB1(v)


def lv2(v) -> int:
    """The level of the rotated functional (zeta u)."""
    return -AA2(v) - 3 * BB2(v)


def Cl(v) -> int:
    """The class of v modulo the prime (1 - zeta_5) (only its residue mod 5 matters)."""
    a, b, c, d = v
    return a - b + c - d


def qs1(v) -> float:
    """psi_u(v) = 2 <u, v> = AA1 + BB1 phi (physical projection)."""
    return AA1(v) + BB1(v) * PHI


def qs2(v) -> float:
    return AA2(v) + BB2(v) * PHI


def qh1(v) -> float:
    """Galois conjugate of qs1 (phi -> 1 - phi): an internal coordinate."""
    return AA1(v) + BB1(v) * (1 - PHI)


def qh2(v) -> float:
    return AA2(v) + BB2(v) * (1 - PHI)


UB1 = 1 - W10 + W10**3                 # conj(u), u = 1 - zeta + zeta^2, |u| = 2 - phi
UB2 = -1 + 2 * W10 - W10**2            # conj(zeta u)
DELTA = 3 - PHI                        # the lattice period of the cut, 1.3819660...
ALPHA = 1 / PHI                        # the golden rotation number
D5 = math.sqrt((5 - 2 * SQRT5) / 4)    # |Im(conj(u) e)| for an active step e, = tan(36 deg)/2
C5 = (SQRT5 - 2) / 2                   # |Re(conj(u) e)| for an active step e


def lens_half_window(r: float) -> float:
    """L(r) = D sqrt(r^2 - 1): half the length of the window an active step must hit."""
    return D5 * math.sqrt(max(r * r - 1.0, 0.0))


def psiL(P: int, q: int) -> float:
    """psi_u of a class-0 lattice point at level 5q: delta P - delta alpha q."""
    return DELTA * P - DELTA * ALPHA * q


def window_centre(p: complex, which: int = 1) -> float:
    ub = UB1 if which == 1 else UB2
    return (ub * (p + 1)).real - (3 - 2 * PHI) / 2


def is_cut_level(q: int, Z: float, L: float) -> bool:
    """No class-0 value delta P - delta alpha q lies within L of Z."""
    x = (Z + DELTA * ALPHA * q) / DELTA           # want |P - x| > L / delta for all P
    frac = x - math.floor(x)
    return min(frac, 1 - frac) > L / DELTA


# ----------------------------------------------------------------------------------------------
# Orbits through the dumbbell walk (the orbit invariant of the lower bound)
# ----------------------------------------------------------------------------------------------

@dataclass(frozen=True)
class State:
    j: int        # m = zeta_5^j
    nu: Q4        # the pivot, class 0

    def point(self, p: complex) -> complex:
        return ZETA**self.j * (p + 1 - 2 * pt(self.nu)) - 1

    def other_end(self) -> Q4:
        """nu + conj(m)."""
        return add(self.nu, z5_pow(-self.j))

    def centres(self, p: complex) -> tuple[complex, complex]:
        """In the frame of p: where the left and right disk centres sit."""
        c_minus = 2 * pt(self.nu) - 1
        c_plus = 2 * pt(self.other_end()) - 1
        return c_minus, c_plus


def in_window(v: Q4, p: complex, r: float) -> bool:
    return abs(p + 1 - 2 * pt(v)) <= r


def state_step(s: State, letter: str, p: complex, r: float) -> State:
    """The action of one letter on a state (m, nu), exactly as in the Lean orbit invariant."""
    if letter in "aA":
        if not in_window(s.nu, p, r):
            return s
        return State((s.j - 1) % 5 if letter == "a" else (s.j + 1) % 5, s.nu)
    end = s.other_end()
    if not in_window(end, p, r):
        return s
    j2 = (s.j - 1) % 5 if letter == "b" else (s.j + 1) % 5
    return State(j2, sub(end, z5_pow(-j2)))


def orbit_states(p: complex, r: float, limit: int = 2_000_000):
    """BFS over states reachable from (m, nu) = (1, 0).  Returns the list of states (in BFS
    order) and the BFS parent map (state -> (parent, letter))."""
    start = State(0, (0, 0, 0, 0))
    seen = {start: None}
    order = [start]
    dq = deque([start])
    while dq:
        s = dq.popleft()
        for letter in "aAbB":
            t = state_step(s, letter, p, r)
            if t not in seen:
                seen[t] = (s, letter)
                order.append(t)
                dq.append(t)
                if len(order) > limit:
                    raise RuntimeError("orbit too large")
    return order, seen


def orbit_points(p: complex, r: float, limit: int = 2_000_000, digits: int = 9):
    """Distinct orbit points of p at radius r (deduplicated after rounding)."""
    states, _ = orbit_states(p, r, limit)
    pts = {}
    for s in states:
        z = s.point(p)
        key = (round(z.real, digits), round(z.imag, digits))
        pts.setdefault(key, z)
    return list(pts.values()), states


def direct_orbit(p: complex, r: float, limit: int = 2_000_000, digits: int = 9):
    """Orbit by applying the four turns to points directly (a cross-check of the state walk)."""
    key = lambda z: (round(z.real, digits), round(z.imag, digits))
    seen = {key(p): p}
    dq = deque([p])
    while dq:
        z = dq.popleft()
        for letter in "aAbB":
            w = turn(letter, z, r)
            k = key(w)
            if k not in seen:
                seen[k] = w
                dq.append(w)
                if len(seen) > limit:
                    raise RuntimeError("orbit too large")
    return list(seen.values())

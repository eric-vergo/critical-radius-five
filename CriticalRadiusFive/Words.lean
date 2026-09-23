/-
Copyright (c) 2026 The critical-radius-five authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The critical-radius-five authors
-/
import CriticalRadiusFive.Basic

/-!
# Words in the generators, acting on segments

A word in the letters `a, a⁻¹, b, b⁻¹` is applied letter by letter, from left to right, as in the
paper: the word `ab` is the map `z ↦ b (a z)`. Each letter rotates its own disk and fixes everything
else, so on a given point a word acts as the corresponding composition of rotations of the whole
plane — its *formal action*, an isometry of `ℂ` — provided every letter finds the current point
inside its disk. We then call the point *admissible* for the word.

Disks are convex and the formal action of a letter is affine, so a word that is admissible at the
two endpoints of a segment is admissible along the whole segment (`admissible_of_mem_segment`), and
on that segment it acts as a single isometry. If that isometry moves both endpoints by the same
vector, the word translates the whole segment (`wordPerm_apply_of_mem_segment`). This is how the
three words behind the upper bound are handled: everything is checked at the endpoints.
-/

noncomputable section

open Complex Set

namespace CriticalRadiusFive

/-- The four letters: `a`, `A = a⁻¹`, `b`, `B = b⁻¹`. -/
inductive Letter
  | a
  | A
  | b
  | B

namespace Letter

variable {n : ℕ} {r : ℝ}

/-- The centre of the disk turned by a letter: `-1` for `a^{±1}`, `1` for `b^{±1}`. -/
def center : Letter → ℂ
  | a | A => -1
  | b | B => 1

/-- The rotation factor of a letter: `ζ⁻¹` for the clockwise turns `a`, `b`, and `ζ` for their
inverses. -/
def rot (n : ℕ) : Letter → ℂ
  | a | b => (zeta n)⁻¹
  | A | B => zeta n

/-- The permutation of `ℂ` given by a letter. -/
def perm (n : ℕ) (r : ℝ) : Letter → Equiv.Perm ℂ
  | a => genA n r
  | A => (genA n r)⁻¹
  | b => genB n r
  | B => (genB n r)⁻¹

/-- The formal action of a letter: the rotation of the whole plane about the letter's centre. -/
def act (n : ℕ) (l : Letter) (z : ℂ) : ℂ := l.center + l.rot n * (z - l.center)

/-- Every letter is an element of `GG n r`. -/
theorem perm_mem_GG (n : ℕ) (r : ℝ) (l : Letter) : l.perm n r ∈ GG n r := by
  cases l
  exacts [genA_mem_GG n r, inv_mem (genA_mem_GG n r), genB_mem_GG n r, inv_mem (genB_mem_GG n r)]

/-- Inside its disk a letter acts by its formal action. -/
theorem perm_apply_of_le {l : Letter} {z : ℂ} (h : ‖z - l.center‖ ≤ r) :
    l.perm n r z = l.act n z := by
  cases l <;> simp only [center, sub_neg_eq_add] at h <;>
    simp only [perm, act, center, rot, genA_apply_of_le, genA_inv_apply_of_le, genB_apply_of_le,
      genB_inv_apply_of_le, h] <;> ring

/-- The formal action of a letter maps segments to segments. -/
theorem act_mem_segment (l : Letter) {P Q z : ℂ} (hz : z ∈ segment ℝ P Q) :
    l.act n z ∈ segment ℝ (l.act n P) (l.act n Q) := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
  refine ⟨s, t, hs, ht, hst, ?_⟩
  have hst' : (s : ℂ) + t = 1 := by exact_mod_cast hst
  simp only [act, real_smul]
  linear_combination (l.center - l.rot n * l.center) * hst'

end Letter

/-- The permutation of `ℂ` given by a word, read from left to right. -/
def wordPerm (n : ℕ) (r : ℝ) : List Letter → Equiv.Perm ℂ
  | [] => 1
  | l :: w => wordPerm n r w * l.perm n r

/-- The formal action of a word: the composition of the formal actions of its letters. -/
def formalAct (n : ℕ) : List Letter → ℂ → ℂ
  | [], z => z
  | l :: w, z => formalAct n w (l.act n z)

/-- A point is *admissible* for a word if each letter finds the current point inside its disk. -/
def Admissible (n : ℕ) (r : ℝ) : List Letter → ℂ → Prop
  | [], _ => True
  | l :: w, z => ‖z - l.center‖ ≤ r ∧ Admissible n r w (l.act n z)

variable {n : ℕ} {r : ℝ}

/-- Every word is an element of `GG n r`. -/
theorem wordPerm_mem_GG (n : ℕ) (r : ℝ) : ∀ w : List Letter, wordPerm n r w ∈ GG n r
  | [] => one_mem _
  | l :: w => mul_mem (wordPerm_mem_GG n r w) (l.perm_mem_GG n r)

/-- On an admissible point a word acts by its formal action. -/
theorem wordPerm_apply_of_admissible :
    ∀ {w : List Letter} {z : ℂ}, Admissible n r w z → wordPerm n r w z = formalAct n w z
  | [], _, _ => rfl
  | l :: w, z, ⟨hz, hw⟩ => by
    rw [wordPerm, Equiv.Perm.mul_apply, Letter.perm_apply_of_le hz]
    exact wordPerm_apply_of_admissible hw

/-- **Convexity.** A word admissible at the endpoints of a segment is admissible along it. -/
theorem admissible_of_mem_segment :
    ∀ {w : List Letter} {P Q z : ℂ}, Admissible n r w P → Admissible n r w Q →
      z ∈ segment ℝ P Q → Admissible n r w z
  | [], _, _, _, _, _, _ => trivial
  | l :: w, P, Q, z, ⟨hP, hwP⟩, ⟨hQ, hwQ⟩, hz => by
    refine ⟨?_, admissible_of_mem_segment hwP hwQ (l.act_mem_segment hz)⟩
    have hball := (convex_closedBall l.center r).segment_subset
      (mem_closedBall_iff_norm.2 hP) (mem_closedBall_iff_norm.2 hQ) hz
    exact mem_closedBall_iff_norm.1 hball

/-- The formal action of a word is affine: `formalAct w z = formalAct w 0 + ρ z`, where `ρ` is
the product of the rotation factors of the letters. -/
theorem formalAct_eq : ∀ (w : List Letter) (z : ℂ),
    formalAct n w z = formalAct n w 0 + (w.map (Letter.rot n)).prod * z
  | [], z => by simp [formalAct]
  | l :: w, z => by
    rw [formalAct, formalAct, formalAct_eq w, formalAct_eq w (l.act n 0)]
    simp only [List.map_cons, List.prod_cons, Letter.act]
    ring

/-- **A word that translates the endpoints of a segment translates the whole segment.** If a word
is admissible at `P` and at `Q` and its formal action moves both by `τ`, then the word moves every
point of the segment `[P, Q]` by `τ`. -/
theorem wordPerm_apply_of_mem_segment {w : List Letter} {P Q z τ : ℂ} (hP : Admissible n r w P)
    (hQ : Admissible n r w Q) (hτP : formalAct n w P = P + τ) (hτQ : formalAct n w Q = Q + τ)
    (hz : z ∈ segment ℝ P Q) : wordPerm n r w z = z + τ := by
  rw [wordPerm_apply_of_admissible (admissible_of_mem_segment hP hQ hz)]
  obtain ⟨s, t, -, -, hst, rfl⟩ := hz
  have hst' : (s : ℂ) + t = 1 := by exact_mod_cast hst
  rw [formalAct_eq] at hτP hτQ ⊢
  simp only [real_smul]
  linear_combination (s : ℂ) * hτP + (t : ℂ) * hτQ - (formalAct n w 0 - τ) * hst'

end CriticalRadiusFive

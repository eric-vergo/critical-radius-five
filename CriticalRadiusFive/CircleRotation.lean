/-
Copyright (c) 2026 The critical-radius-five authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The critical-radius-five authors
-/
import Mathlib

/-!
# Irrational rotations of a circle

Two elementary facts about the rotation by `α` of the circle `ℝ ⧸ L ℤ` with `α / L` irrational are
the one-dimensional engines of the two halves of the main theorem.

* **No return** (`iterate_injective_of_irrational`, `orbit_infinite_of_irrational_rotation`): the
  rotation never revisits a point. If a group of permutations of `ℂ` realises the rotation along a
  curve, the orbits of the points of the curve are infinite. This is how `GG₅(√(3+φ))` is shown to
  be infinite: three words of the group act on a chord as a rotation with irrational rotation
  number `1/φ`.
* **Cut levels** (`exists_cut_levels`): every arc of a fixed positive length is entered within a
  bounded number of steps, uniformly in the starting point. It is stated in the form in which the
  lower bound uses it: a window of width less than the period `δ` misses every point of the
  progression `δ ℤ + t q` for some *level* `q` in a bounded range on either side of `0`, the bound
  depending on the width of the window but not on its position. The proof finds a small step
  `a (t / δ) - b` with Dirichlet's approximation theorem and then marches with it.
-/

open Set MulAction

namespace CriticalRadiusFive

/-! ### No return -/

/-- If `T` moves every point by `α` modulo `L` and `α / L` is irrational, then the iterates of `T`
starting from any point are pairwise distinct. -/
theorem iterate_injective_of_irrational {L α : ℝ} (hα : Irrational (α / L)) {T : ℝ → ℝ}
    (hT : ∀ t, ∃ m : ℤ, T t = t + α + m * L) (t₀ : ℝ) :
    Function.Injective fun k : ℕ => T^[k] t₀ := by
  have key (k : ℕ) : ∃ m : ℤ, T^[k] t₀ = t₀ + k * α + m * L := by
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨m, hm⟩ := ih
      obtain ⟨m', hm'⟩ := hT (T^[k] t₀)
      exact ⟨m + m', by rw [Function.iterate_succ_apply', hm', hm]; push_cast; ring⟩
  intro i j hij
  obtain ⟨mi, hi⟩ := key i
  obtain ⟨mj, hj⟩ := key j
  by_contra hne
  have hL : L ≠ 0 := by rintro rfl; exact hα.ne_rat 0 (by simp)
  have hij₀ : (i : ℤ) - j ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hne)
  refine (irrational_iff_ne_rational _).1 hα (mj - mi) (i - j) hij₀ ?_
  rw [div_eq_div_iff hL (by exact_mod_cast hij₀)]
  have : T^[i] t₀ = T^[j] t₀ := hij
  push_cast
  linear_combination hj - hi + this

/-- **Irrational rotations give infinite orbits.** Suppose that a group `G` of permutations of `ℂ`
carries the point `x t` to `x (T t)` for every `t` in a set `W` which `T` maps into itself, that
`x` is injective on `W`, and that `T` moves every point by `α` modulo `L`, with `α / L`
irrational. Then the `G`-orbit of `x t₀` is infinite for every `t₀ ∈ W`. -/
theorem orbit_infinite_of_irrational_rotation {G : Subgroup (Equiv.Perm ℂ)} {L α : ℝ}
    (hα : Irrational (α / L)) {T : ℝ → ℝ} (hT : ∀ t, ∃ m : ℤ, T t = t + α + m * L)
    {W : Set ℝ} (hTW : MapsTo T W W) {x : ℝ → ℂ} (hx : InjOn x W)
    (hG : ∀ t ∈ W, ∃ g ∈ G, g (x t) = x (T t)) {t₀ : ℝ} (ht₀ : t₀ ∈ W) :
    (orbit G (x t₀)).Infinite := by
  have hW (k : ℕ) : T^[k] t₀ ∈ W := hTW.iterate k ht₀
  refine infinite_of_injective_forall_mem (f := fun k : ℕ => x (T^[k] t₀))
    (fun i j hij => iterate_injective_of_irrational hα hT t₀ (hx (hW i) (hW j) hij)) fun k => ?_
  induction k with
  | zero => exact mem_orbit_self _
  | succ k ih =>
    obtain ⟨⟨g, hg⟩, hgk⟩ := ih
    obtain ⟨h, hh, hht⟩ := hG _ (hW k)
    refine ⟨⟨h * g, mul_mem hh hg⟩, ?_⟩
    simp only [Function.iterate_succ_apply', ← hht, ← hgk]
    rfl

/-! ### Cut levels -/

/-- **Marching.** An arithmetic progression whose step is shorter than the gap `1 - 2η` enters
the open set `(η, 1 - η) + ℤ` within `⌈1 / |ε|⌉₊ + 1` steps. -/
theorem exists_march {ε η y : ℝ} (hε : ε ≠ 0) (h : 2 * η + |ε| < 1) :
    ∃ j : ℕ, j ≤ ⌈1 / |ε|⌉₊ + 1 ∧ ∃ k : ℤ, η + k < y + j * ε ∧ y + j * ε < 1 - η + k := by
  -- It suffices to march upwards: for a negative step, march upwards from `-y`.
  wlog hpos : 0 < ε generalizing ε y
  · obtain ⟨j, hj, k, h₁, h₂⟩ := this (ε := -ε) (y := -y) (neg_ne_zero.2 hε) (by rwa [abs_neg])
      (neg_pos.2 (lt_of_le_of_ne (not_lt.1 hpos) hε))
    rw [abs_neg] at hj
    exact ⟨j, hj, -k - 1, by push_cast; linarith, by push_cast; linarith⟩
  rw [abs_of_pos hpos] at h ⊢
  classical
  -- The first term beyond `η + k₀ + 1`, the lower end of the next gap, lies inside that gap.
  set k₀ : ℤ := ⌊y - η⌋
  have hk₀ : y - η < k₀ + 1 := Int.lt_floor_add_one _
  have hex : ∃ j : ℕ, η + k₀ + 1 < y + j * ε := by
    obtain ⟨j, hj⟩ := exists_nat_gt ((η + k₀ + 1 - y) / ε)
    exact ⟨j, by rw [div_lt_iff₀ hpos] at hj; linarith⟩
  have hspec := Nat.find_spec hex
  have hpos' : 0 < Nat.find hex := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0] at hspec
    push_cast at hspec
    linarith
  have hprev := Nat.find_min hex (Nat.sub_lt hpos' one_pos)
  rw [Nat.cast_pred hpos'] at hprev
  refine ⟨Nat.find hex, Nat.find_min' hex ?_, k₀ + 1, by push_cast; linarith, by push_cast; linarith⟩
  have h₁ : 1 / ε ≤ ⌈1 / ε⌉₊ := Nat.le_ceil _
  have h₂ : 1 / ε * ε = 1 := by field_simp
  have h₃ := Int.floor_le (y - η)
  push_cast
  nlinarith

/-- A number strictly inside a gap `(η + k, 1 - η + k)` is at distance more than `η` from every
integer. -/
theorem lt_abs_intCast_add {η y : ℝ} {k : ℤ} (h₁ : η + k < y) (h₂ : y < 1 - η + k) (P : ℤ) :
    η < |P + y| := by
  rcases le_or_gt 0 (P + k) with h | h
  · have : (0 : ℝ) ≤ P + k := by exact_mod_cast h
    exact lt_of_lt_of_le (by linarith) (le_abs_self _)
  · have : (P : ℝ) + k ≤ -1 := by exact_mod_cast (show P + k ≤ -1 by omega)
    exact lt_of_lt_of_le (by linarith) (neg_le_abs _)

/-- The level `q` is a cut level for the window `[Z - L, Z + L]` as soon as `(t / δ) q - Z / δ`
lies strictly inside a gap of width `1 - 2 L / δ`. -/
theorem lt_abs_of_mem_gap {δ t L Z : ℝ} (hδ : 0 < δ) {q k : ℤ}
    (h₁ : L / δ + k < t / δ * q - Z / δ) (h₂ : t / δ * q - Z / δ < 1 - L / δ + k) (P : ℤ) :
    L < |δ * P + t * q - Z| := by
  have h := lt_abs_intCast_add h₁ h₂ P
  have e : δ * P + t * q - Z = δ * (P + (t / δ * q - Z / δ)) := by field_simp; ring
  rwa [e, abs_mul, abs_of_pos hδ, ← div_lt_iff₀' hδ]

/-- **Cut levels.** Let `δ > 0` and let `t / δ` be irrational. For every half-width `L ≥ 0` with
`2 L < δ` there is a bound `N` such that every window `[Z - L, Z + L]` misses the progression
`δ ℤ + t q` for some level `q` with `1 ≤ q ≤ N`, and also for some level `q` with
`-N ≤ q ≤ -1`. -/
theorem exists_cut_levels {δ t L : ℝ} (hδ : 0 < δ) (ht : Irrational (t / δ)) (hL : 0 ≤ L)
    (hLδ : 2 * L < δ) :
    ∃ N : ℕ, ∀ Z : ℝ,
      (∃ q : ℤ, 1 ≤ q ∧ q ≤ N ∧ ∀ P : ℤ, L < |δ * P + t * q - Z|) ∧
      (∃ q : ℤ, -N ≤ q ∧ q ≤ -1 ∧ ∀ P : ℤ, L < |δ * P + t * q - Z|) := by
  set θ := t / δ
  set η := L / δ
  have hη : 0 ≤ η := div_nonneg hL hδ.le
  have hη' : 2 * η < 1 := by rw [mul_div_assoc', div_lt_one hδ]; exact hLδ
  -- A small nonzero step `ε = a θ - b`, by Dirichlet's approximation theorem.
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - 2 * η))
  have hn₀ : 0 < n := by
    have : 0 < 1 / (1 - 2 * η) := by apply div_pos one_pos; linarith
    exact_mod_cast this.trans hn
  obtain ⟨a, ha, -, hab⟩ := Real.exists_nat_abs_mul_sub_round_le θ hn₀
  set b : ℤ := round (a * θ)
  set ε := a * θ - b
  have hε : ε ≠ 0 := by
    intro h0
    refine ht.ne_rat (b / a) ?_
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    push_cast
    field_simp
    linarith [show a * θ - b = 0 from h0]
  have hεη : 2 * η + |ε| < 1 := by
    have : 1 / ((n : ℝ) + 1) < 1 - 2 * η := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ (by linarith)] at hn
      nlinarith
    linarith
  -- March from the levels `1` and `-1` in steps of `a` levels.
  set J := ⌈1 / |ε|⌉₊ + 1
  refine ⟨1 + J * a, fun Z => ⟨?_, ?_⟩⟩
  · obtain ⟨j, hj, k, h₁, h₂⟩ := exists_march (y := θ - Z / δ) hε hεη
    have hja : j * a ≤ J * a := Nat.mul_le_mul_right a hj
    have e : θ * ((1 + j * a : ℕ) : ℤ) - Z / δ = θ - Z / δ + j * ε + (j * b : ℤ) := by
      push_cast; ring
    refine ⟨1 + j * a, by omega, by push_cast; omega, lt_abs_of_mem_gap hδ (k := k + j * b) ?_ ?_⟩
    · rw [show ((1 + j * a : ℕ) : ℤ) = 1 + j * a by push_cast; ring] at e
      rw [e]; push_cast; linarith
    · rw [show ((1 + j * a : ℕ) : ℤ) = 1 + j * a by push_cast; ring] at e
      rw [e]; push_cast; linarith
  · obtain ⟨j, hj, k, h₁, h₂⟩ :=
      exists_march (ε := -ε) (y := -θ - Z / δ) (neg_ne_zero.2 hε) (by rwa [abs_neg])
    rw [abs_neg] at hj
    have hja : j * a ≤ J * a := Nat.mul_le_mul_right a hj
    have e : θ * (-1 - j * a : ℤ) - Z / δ = -θ - Z / δ + j * -ε - (j * b : ℤ) := by
      push_cast; ring
    refine ⟨-1 - j * a, by push_cast; omega, by omega,
      lt_abs_of_mem_gap hδ (k := k - j * b) ?_ ?_⟩
    · rw [e]; push_cast; linarith
    · rw [e]; push_cast; linarith

end CriticalRadiusFive

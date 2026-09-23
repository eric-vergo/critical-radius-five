/-
Copyright (c) 2026 The critical-radius-five authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The critical-radius-five authors
-/
import CriticalRadiusFive.CircleRotation
import CriticalRadiusFive.Finiteness
import CriticalRadiusFive.Lens
import CriticalRadiusFive.PivotWalk

/-!
# The lower bound: `GG₅` is finite below `√(3 + φ)`

Fix `r < √(3 + φ)` and a point `p`. By the pivot walk (`PivotWalk.lean`) it suffices to trap the
pivots and tips of the orbit of `p` in a set `V` of lattice points that is closed under the typed
steps inside the window and whose size is bounded in terms of `r` alone. The set is cut out by a
real functional and its *level*.

**The cut functional.** Let `u = 1 - ζ + ζ²` and `ψ(ν) = 2 Re(ū ν)`. On the lattice
`ψ(ν) = A(ν) + B(ν) φ` with integers `A`, `B`, and the *level* `ℓ(ν) = -A(ν) - 3 B(ν)` satisfies

`ψ(ν) + ℓ(ν) = -δ B(ν)`,  `δ = 3 - φ`  (`psi_add_level`),

so the values of `ψ` at level `ℓ` lie in the progression `-ℓ + δ ℤ`. A step `e ∈ μ₅` changes the
level by `ℓ(e) ∈ {3, -2}`, and `ℓ ≡ 3 · class (mod 5)`: pivots sit at levels `≡ 0`, tips at levels
`≡ 3`. The level can therefore only overshoot a bound `5q` through an *active* step (`ℓ(e) = 3`)
from a pivot at level exactly `5q`, and only undershoot `5q` through an active step back to a
pivot at level `5q`.

**The lens.** Both endpoints of such a step lie in the window, so by the lens bound `ψ` of the
pivot lies within `L(r) = √((7 - 4φ)/4) · √(r² - 1)` of a centre that depends on `p` only
(`abs_psi_sub_cutCenter_le`). For `r < √(3 + φ)` this window is shorter than the period:
`2 L(r) < δ` (`two_mul_lensWidth_lt`), with equality exactly at `r = √(3 + φ)`.

**Cut levels.** The progressions `-5q + δ ℤ` move with `q` by the irrational rotation
`-5/δ = -(2 + φ)`, so there are *cut levels* `q₊ ≥ 1` and `q₋ ≤ -1` at which the window misses the
progression, within a bound `N` that depends on `r` only (`exists_cut_levels`). No step of the walk
crosses a cut level, so the level stays in the band `(5q₋, 5q₊]` (`level_mem_band`). The same holds
for the turned functional `ψ ∘ ζ⁻¹`.

**Discreteness.** In the window `ψ` and `ψ ∘ ζ⁻¹` are bounded, and in the bands so are the two
levels; together they bound the coordinates of the lattice point (`mem_box_of_abs_le`). So all
pivots lie in a box whose size depends on `r` only, every orbit has at most `5 · |box|` points, and
the group is finite (`finite_GG_five_of_lt`).
-/

noncomputable section

open Complex ComplexConjugate Set MulAction
open scoped goldenRatio

namespace CriticalRadiusFive

local notation "ζ" => zeta 5

open Cyc

/-! ### The cut functional and its level -/

/-- The cut vector `u = 1 - ζ + ζ²`. -/
def cutU : Cyc := (1, -1, 1, 0)

/-- The rational part `A` of the cut functional `ψ = A + B φ`. -/
def psiRat : Cyc → ℤ
  | (a, b, c, d) => 3 * a - 4 * b + 3 * c - d

/-- The golden part `B` of the cut functional `ψ = A + B φ`. -/
def psiGold : Cyc → ℤ
  | (a, b, c, d) => -2 * a + 2 * b - 2 * c + d

/-- The level `ℓ = -A - 3B` of a lattice point. -/
def level : Cyc → ℤ
  | (a, b, c, d) => 3 * a - 2 * b + 3 * c - 2 * d

/-- The cut functional `ψ(ν) = 2 Re(ū ν) = A(ν) + B(ν) φ`. -/
def psi (v : Cyc) : ℝ := psiRat v + psiGold v * φ

/-- The cut functional is `ψ(ν) = 2 Re(ū ν)` with `u = 1 - ζ + ζ²`. -/
theorem psi_eq (v : Cyc) : psi v = 2 * (toC (bar cutU) * toC v).re := by
  have h : (psi v : ℂ) = toC (bar cutU) * toC v + toC cutU * toC (bar v) := by
    have hφ := zeta_five_add_pow_four
    rw [psi, ofReal_add, ofReal_mul, ofReal_intCast, ofReal_intCast]
    generalize (φ : ℂ) = Φ at hφ ⊢
    obtain ⟨a, b, c, d⟩ := v
    simp only [toC, bar, cutU, psiRat, psiGold]
    push_cast
    linear_combination (-2 * (a : ℂ) - b + c - 2 * d * ζ ^ 2 + (b - 3 * c + d) * ζ) *
      cyclotomic_zeta_five + (2 * (a : ℂ) - 2 * b + 2 * c - d) * hφ
  have h' : toC cutU * toC (bar v) = conj (toC (bar cutU) * toC v) := by
    rw [map_mul, ← toC_bar, ← toC_bar, show bar (bar cutU) = cutU by decide]
  rw [h', add_conj] at h
  exact_mod_cast h

/-- The level is additive. -/
theorem level_add (v w : Cyc) : level (v + w) = level v + level w := by
  obtain ⟨a, b, c, d⟩ := v
  obtain ⟨a', b', c', d'⟩ := w
  simp only [level]
  ring

/-- The level commutes with subtraction. -/
theorem level_sub (v w : Cyc) : level (v - w) = level v - level w := by
  obtain ⟨a, b, c, d⟩ := v
  obtain ⟨a', b', c', d'⟩ := w
  simp only [level, Prod.mk_sub_mk]
  ring

/-- **The level lattice.** `ψ(ν) + ℓ(ν) = -δ B(ν)` with `δ = 3 - φ`: at level `ℓ` the values of
`ψ` lie in the progression `-ℓ + δ ℤ`. -/
theorem psi_add_level (v : Cyc) : psi v + level v = -(3 - φ) * psiGold v := by
  obtain ⟨a, b, c, d⟩ := v
  simp only [psi, psiRat, psiGold, level]
  push_cast
  ring

/-- Pivots (class `0`) sit at levels `≡ 0` and tips (class `1`) at levels `≡ 3` modulo `5`. -/
theorem level_emod_five (v : Cyc) : level v % 5 = 3 * cls v % 5 := by
  obtain ⟨a, b, c, d⟩ := v
  simp only [level, cls]
  omega

/-- **The step table.** A fifth root of unity raises the level by `3` or lowers it by `2`. -/
theorem level_of_mem_units : ∀ e ∈ units, level e = 3 ∨ level e = -2 := by decide

/-- The two *active* steps `1` and `ζ²`, which raise the level, have the same value of `ψ`. -/
theorem psi_of_level_eq_three : ∀ e ∈ units, level e = 3 → psiRat e = 3 ∧ psiGold e = -2 := by
  decide

/-! ### The lens window -/

/-- `√((7 - 4φ)/4) = |Im(ū e)|` for an active step `e`. -/
def lensHeight : ℝ := √((7 - 4 * φ) / 4)

/-- The half-width `√((7 - 4φ)/4) · √(r² - 1)` of the lens window. -/
def lensWidth (r : ℝ) : ℝ := lensHeight * √(r ^ 2 - 1)

/-- **The threshold.** Below `√(3 + φ)` the lens window is shorter than the period `δ = 3 - φ`:
`(7 - 4φ)(r² - 1) < (7 - 4φ)(2 + φ) = (3 - φ)²`. -/
theorem two_mul_lensWidth_lt {r : ℝ} (hr : r ^ 2 < 3 + φ) : 2 * lensWidth r < 3 - φ := by
  have := goldenRatio_gt
  have := goldenRatio_lt
  rcases le_or_gt (r ^ 2 - 1) 0 with h | h
  · rw [lensWidth, Real.sqrt_eq_zero_of_nonpos h]
    linarith
  have h₀ : 0 ≤ 2 * lensWidth r := by unfold lensWidth lensHeight; positivity
  have h₁ : (2 * lensWidth r) ^ 2 = (7 - 4 * φ) * (r ^ 2 - 1) := by
    rw [lensWidth, lensHeight, mul_pow, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt h.le]
    ring
  have h₂ : (7 - 4 * φ) * (r ^ 2 - 1) < (3 - φ) ^ 2 := by
    have := Real.goldenRatio_sq
    nlinarith
  exact (pow_lt_pow_iff_left₀ h₀ (by linarith) two_ne_zero).1 (h₁ ▸ h₂)

/-- The centre of the lens window of `ψ` for the walk with window centre `w₀ = p + 1`. -/
def cutCenter (w₀ : ℂ) : ℝ := (toC (bar cutU) * w₀).re - (3 - 2 * φ) / 2

/-- **The lens window.** If an active step `e` joins two lattice points `ν` and `ν + e` of the
window `‖w₀ - 2 ·‖ ≤ r`, then `ψ(ν)` lies within `L(r)` of the centre `cutCenter w₀`. -/
theorem abs_psi_sub_cutCenter_le {w₀ : ℂ} {r : ℝ} (hr : r ^ 2 < 3 + φ) {v e : Cyc}
    (he : e ∈ units) (hlev : level e = 3) (hv : ‖w₀ - 2 * toC v‖ ≤ r)
    (hve : ‖w₀ - 2 * toC (v + e)‖ ≤ r) : |psi v - cutCenter w₀| ≤ lensWidth r := by
  have := goldenRatio_gt
  have := goldenRatio_lt
  obtain ⟨hA, hB⟩ := psi_of_level_eq_three e he hlev
  set U := toC (bar cutU)
  -- `Re(ū e) = ψ(e) / 2 = (3 - 2φ)/2` and `Im(ū e)² = ‖u‖² - Re(ū e)² = (7 - 4φ)/4`.
  have hre : (U * toC e).re = (3 - 2 * φ) / 2 := by
    have := psi_eq e
    rw [psi, hA, hB] at this
    push_cast at this
    linarith
  have hUe : ‖U * toC e‖ ^ 2 = 5 - 3 * φ := by
    rw [norm_mul, norm_toC_of_mem_units he, mul_one, norm_toC_sq]
    simp [cutU, bar, normRat, normGold]
    ring
  have him : (U * toC e).im ^ 2 = (7 - 4 * φ) / 4 := by
    have := Complex.sq_norm (U * toC e)
    rw [hUe, normSq_apply, hre] at this
    have := Real.goldenRatio_sq
    nlinarith
  -- The lens bound, with `C = (2φ - 3)/2` and `D = √((7 - 4φ)/4)`.
  have hC : |(U * toC e).re| ≤ (2 * φ - 3) / 2 := by
    rw [hre, abs_of_neg (by linarith)]
    linarith
  have hD : |(U * toC e).im| ≤ lensHeight := Real.abs_le_sqrt him.le
  have hCD : (2 * φ - 3) / 2 * √(r ^ 2 - 1) ≤ lensHeight := by
    rw [lensHeight, ← Real.sqrt_sq (show 0 ≤ (2 * φ - 3) / 2 by linarith), ← Real.sqrt_mul
      (sq_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    have := Real.goldenRatio_sq
    rcases le_or_gt (r ^ 2 - 1) 0 with h | h
    · nlinarith [sq_nonneg ((2 * φ - 3) / 2)]
    · nlinarith
  have hlens := abs_re_mul_add_le (U := U) (norm_toC_of_mem_units he) hv hve
    (by rw [toC_add]; ring) hC hD hCD
  -- `Re(ū (w + w')) = 2 (cutCenter w₀ - ψ(ν))`.
  have hsum : (U * ((w₀ - 2 * toC v) + (w₀ - 2 * toC (v + e)))).re =
      2 * (cutCenter w₀ - psi v) := by
    have h₁ := psi_eq v
    have h₂ := psi_eq e
    rw [psi, hA, hB] at h₂
    push_cast at h₂
    have e₂ (z : ℂ) : (2 * z).re = 2 * z.re := by simp
    have e₄ (z : ℂ) : (4 * z).re = 4 * z.re := by simp
    rw [toC_add, show U * ((w₀ - 2 * toC v) + (w₀ - 2 * (toC v + toC e))) =
      2 * (U * w₀) - 4 * (U * toC v) - 2 * (U * toC e) by ring, sub_re, sub_re, e₂, e₄, e₂,
      cutCenter]
    linarith
  rw [hsum, abs_mul, abs_two] at hlens
  rw [abs_sub_comm, lensWidth]
  linarith

/-! ### Cut levels -/

/-- `q` is a *cut level* for the window centre `w₀` at radius `r`: the lens window of `ψ`, of
half-width `L(r)` about `cutCenter w₀`, misses the progression `-5q + δ ℤ` of the values of `ψ` at
level `5q`. -/
def IsCutLevel (r : ℝ) (w₀ : ℂ) (q : ℤ) : Prop :=
  ∀ P : ℤ, lensWidth r < |(3 - φ) * P + -5 * q - cutCenter w₀|

/-- The progressions `-5q + δ ℤ` move with `q` by the irrational rotation `-5/δ = -(2 + φ)`. -/
theorem irrational_neg_five_div : Irrational (-5 / (3 - φ)) := by
  have := goldenRatio_lt
  have h : -5 / (3 - φ) = -(φ + (2 : ℕ)) := by
    rw [div_eq_iff (by linarith), Nat.cast_ofNat]
    linear_combination -Real.goldenRatio_sq
  rw [h]
  exact (Real.goldenRatio_irrational.add_natCast 2).neg

/-- **Cut levels exist, uniformly.** For `r < √(3 + φ)` there is a bound `N` such that every window
centre has a cut level in `[1, N]` and a cut level in `[-N, -1]`. -/
theorem exists_isCutLevel {r : ℝ} (hr : r ^ 2 < 3 + φ) :
    ∃ N : ℕ, ∀ w₀ : ℂ, (∃ q : ℤ, 1 ≤ q ∧ q ≤ N ∧ IsCutLevel r w₀ q) ∧
      (∃ q : ℤ, -N ≤ q ∧ q ≤ -1 ∧ IsCutLevel r w₀ q) := by
  have := goldenRatio_lt
  obtain ⟨N, hN⟩ := exists_cut_levels (δ := 3 - φ) (t := -5) (by linarith)
    irrational_neg_five_div (two_mul_lensWidth_lt hr)
  exact ⟨N, fun w₀ ↦ hN (cutCenter w₀)⟩

/-- A pivot on a cut level cannot take an active step inside the window: its value of `ψ` would lie
both in the lens window and in the progression that the window misses. -/
theorem level_ne_of_isCutLevel {w₀ : ℂ} {r : ℝ} (hr : r ^ 2 < 3 + φ) {q : ℤ}
    (hq : IsCutLevel r w₀ q) {x e : Cyc} (he : e ∈ units) (hlev : level e = 3)
    (hx : ‖w₀ - 2 * toC x‖ ≤ r) (hxe : ‖w₀ - 2 * toC (x + e)‖ ≤ r) : level x ≠ 5 * q := by
  intro hxq
  have h₁ := abs_psi_sub_cutCenter_le hr he hlev hx hxe
  have h₂ := psi_add_level x
  rw [hxq] at h₂
  have h₃ := hq (-psiGold x)
  push_cast at h₂ h₃
  rw [show (3 - φ) * -(psiGold x : ℝ) + -5 * q - cutCenter w₀ = psi x - cutCenter w₀ by
    linarith] at h₃
  linarith

/-- **No step of the walk crosses a cut level.** If `qhi` and `qlo` are cut levels for the window
centre `w₀`, a typed step between two points of the window — from a pivot (class `0`) by `+e`, or
from a tip (class `1`) by `-e` — keeps the level in the band `(5 qlo, 5 qhi]`. -/
theorem level_mem_band {w₀ : ℂ} {r : ℝ} (hr : r ^ 2 < 3 + φ) {qhi qlo : ℤ}
    (hqhi : IsCutLevel r w₀ qhi) (hqlo : IsCutLevel r w₀ qlo)
    {v v' e : Cyc} (he : e ∈ units) (hv : ‖w₀ - 2 * toC v‖ ≤ r) (hv' : ‖w₀ - 2 * toC v'‖ ≤ r)
    (hstep : cls v % 5 = 0 ∧ v' = v + e ∨ cls v % 5 = 1 ∧ v' = v - e)
    (hband : 5 * qlo < level v ∧ level v ≤ 5 * qhi) :
    5 * qlo < level v' ∧ level v' ≤ 5 * qhi := by
  have hmod := level_emod_five v
  rcases hstep with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
  · -- From a pivot the level can overshoot `5 qhi` only from `5 qhi` itself, by an active step.
    rw [level_add]
    rcases level_of_mem_units e he with h3 | h2
    · have := level_ne_of_isCutLevel hr hqhi he h3 hv hv'
      omega
    · omega
  · -- From a tip the level can undershoot `5 qlo` only by an active step back to a pivot at
    -- `5 qlo`.
    rw [level_sub]
    rcases level_of_mem_units e he with h3 | h2
    · have := level_ne_of_isCutLevel hr hqlo he h3 hv' (by rwa [sub_add_cancel])
      rw [level_sub] at this
      omega
    · omega

/-! ### The invariant set -/

/-- The window of the walk turned by `ζ⁻¹`: `‖ζ⁻¹ (p + 1) - 2 ζ⁻¹ ν‖ = ‖p + 1 - 2 ν‖`. -/
theorem norm_window_mulZetaInv (p : ℂ) (v : Cyc) :
    ‖ζ⁻¹ * (p + 1) - 2 * toC (mulZetaInv v)‖ = ‖p + 1 - 2 * toC v‖ := by
  rw [toC_mulZetaInv, show ζ⁻¹ * (p + 1) - 2 * (ζ⁻¹ * toC v) = ζ⁻¹ * (p + 1 - 2 * toC v) by ring,
    norm_mul, norm_inv, norm_zeta, inv_one, one_mul]

/-- The invariant set for the orbit of `p`: the lattice points of the window, of class `0` or `1`,
whose levels for `ψ` and for the turned functional `ψ ∘ ζ⁻¹` lie in the bands `(5 q₁', 5 q₁]` and
`(5 q₂', 5 q₂]`. -/
def cutSet (p : ℂ) (r : ℝ) (q₁ q₁' q₂ q₂' : ℤ) : Set Cyc :=
  {v | Window p r v ∧ (cls v % 5 = 0 ∨ cls v % 5 = 1) ∧
    (5 * q₁' < level v ∧ level v ≤ 5 * q₁) ∧
    (5 * q₂' < level (mulZetaInv v) ∧ level (mulZetaInv v) ≤ 5 * q₂)}

/-- Between cut levels, the invariant set is closed under the typed steps inside the window. -/
theorem edgeClosed_cutSet {p : ℂ} {r : ℝ} (hr : r ^ 2 < 3 + φ) {q₁ q₁' q₂ q₂' : ℤ}
    (hc₁ : IsCutLevel r (p + 1) q₁) (hc₁' : IsCutLevel r (p + 1) q₁')
    (hc₂ : IsCutLevel r (ζ⁻¹ * (p + 1)) q₂) (hc₂' : IsCutLevel r (ζ⁻¹ * (p + 1)) q₂') :
    EdgeClosed p r (cutSet p r q₁ q₁' q₂ q₂') := by
  -- Both bands are preserved by `level_mem_band`, the second one for the walk turned by `ζ⁻¹`.
  have key {v v' e : Cyc} (he : e ∈ units) (hv : v ∈ cutSet p r q₁ q₁' q₂ q₂')
      (hv' : Window p r v') (hstep : cls v % 5 = 0 ∧ v' = v + e ∨ cls v % 5 = 1 ∧ v' = v - e) :
      (5 * q₁' < level v' ∧ level v' ≤ 5 * q₁) ∧
        (5 * q₂' < level (mulZetaInv v') ∧ level (mulZetaInv v') ≤ 5 * q₂) := by
    obtain ⟨hw, -, hb₁, hb₂⟩ := hv
    refine ⟨level_mem_band hr hc₁ hc₁' he hw hv' hstep hb₁,
      level_mem_band hr hc₂ hc₂' (mulZetaInv_mem_units e he) ?_ ?_ ?_ hb₂⟩
    · rw [norm_window_mulZetaInv]; exact hw
    · rw [norm_window_mulZetaInv]; exact hv'
    · rw [cls_mulZetaInv_emod]
      rcases hstep with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
      exacts [.inl ⟨hc, mulZetaInv_add v e⟩, .inr ⟨hc, mulZetaInv_sub v e⟩]
  constructor
  · intro v hv hc e he hve
    have := cls_of_mem_units e he
    exact ⟨hve, .inr (by rw [cls_add]; omega), key he hv hve (.inl ⟨hc, rfl⟩)⟩
  · intro v hv hc e he hve
    have := cls_of_mem_units e he
    exact ⟨hve, .inl (by rw [cls_sub]; omega), key he hv hve (.inr ⟨hc, rfl⟩)⟩

/-- If `p` lies in one of the disks, the initial state — pivot `0`, tip `1` — is good for the
invariant set, as long as the upper cut levels are `≥ 1` and the lower ones `≤ -1`. -/
theorem good_cutSet {p : ℂ} {r : ℝ} (hp : ‖p + 1‖ ≤ r ∨ ‖p - 1‖ ≤ r) {q₁ q₁' q₂ q₂' : ℤ}
    (hq₁ : 1 ≤ q₁) (hq₁' : q₁' ≤ -1) (hq₂ : 1 ≤ q₂) (hq₂' : q₂' ≤ -1) :
    Good p r (cutSet p r q₁ q₁' q₂ q₂') (1, 0, 0, 0) 0 := by
  have htip : (0 : Cyc) + bar (1, 0, 0, 0) = (1, 0, 0, 0) := by decide
  have h₀ : Window p r 0 → 0 ∈ cutSet p r q₁ q₁' q₂ q₂' := fun hw ↦ ⟨hw, .inl (by decide),
    by rw [show level 0 = 0 by decide]; omega,
    by rw [show level (mulZetaInv 0) = 0 by decide]; omega⟩
  have h₁ : Window p r (1, 0, 0, 0) → (1, 0, 0, 0) ∈ cutSet p r q₁ q₁' q₂ q₂' := fun hw ↦
    ⟨hw, .inr (by decide), by rw [show level (1, 0, 0, 0) = 3 by decide]; omega,
      by rw [show level (mulZetaInv (1, 0, 0, 0)) = -2 by decide]; omega⟩
  refine ⟨by decide, by decide, h₀, fun hw ↦ ?_, ?_⟩
  · rw [htip] at hw ⊢
    exact h₁ hw
  · rw [htip]
    rcases hp with hp | hp
    · exact .inl (h₀ (by simpa [Window] using hp))
    · refine .inr (h₁ ?_)
      rwa [Window, toC_one, show p + 1 - 2 * 1 = p - 1 by ring]

/-! ### Discreteness -/

/-- The box `[-K, K]⁴` of lattice points. -/
def box (K : ℤ) : Finset Cyc := Finset.Icc (-K, -K, -K, -K) (K, K, K, K)

/-- In the window of a point `p` of one of the disks, lattice points have norm at most `1 + r`. -/
theorem norm_toC_le_of_window {p : ℂ} {r : ℝ} (hp : ‖p‖ ≤ 1 + r) {v : Cyc} (hv : Window p r v) :
    ‖toC v‖ ≤ 1 + r := by
  have h : ‖(2 : ℂ) * toC v‖ ≤ ‖p + 1‖ + ‖p + 1 - 2 * toC v‖ := by
    simpa using norm_sub_le (p + 1) (p + 1 - 2 * toC v)
  rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num] at h
  have := norm_add_le p 1
  rw [norm_one] at this
  unfold Window at hv
  linarith

/-- `|ψ(ν)| ≤ 2 ‖ν‖`, since `‖u‖ = 2 - φ ≤ 1`. -/
theorem abs_psi_le (v : Cyc) : |psi v| ≤ 2 * ‖toC v‖ := by
  have h : ‖toC (bar cutU)‖ ≤ 1 := by
    have := goldenRatio_gt
    rw [← sq_le_one_iff₀ (norm_nonneg _), norm_toC_sq]
    simp [cutU, bar, normRat, normGold]
    linarith
  rw [psi_eq, abs_mul, abs_two]
  calc 2 * |(toC (bar cutU) * toC v).re| ≤ 2 * ‖toC (bar cutU) * toC v‖ := by
        gcongr; exact abs_re_le_norm _
    _ ≤ 2 * ‖toC v‖ := by
        rw [norm_mul]; gcongr; exact mul_le_of_le_one_left (norm_nonneg _) h

/-- The golden part of `ψ` is controlled by `ψ` and the level, as `δ B = -(ψ + ℓ)` and `δ > 1`. -/
theorem abs_psiGold_le (v : Cyc) : |(psiGold v : ℝ)| ≤ |psi v| + |(level v : ℝ)| := by
  have := goldenRatio_lt
  have h := psi_add_level v
  have h₁ : |(psiGold v : ℝ)| * (3 - φ) = |psi v + level v| := by
    rw [h, abs_mul, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < 3 - φ), mul_comm]
  have h₂ := abs_add_le (psi v) (level v)
  nlinarith [abs_nonneg (psiGold v : ℝ)]

/-- **Discreteness.** A lattice point is determined by the golden parts and the levels of its two
cut functionals `ψ` and `ψ ∘ ζ⁻¹`: the integer matrix of these four coordinates has
determinant `-5`, so bounding them by `M` bounds the coordinates of the point by `2M`. -/
theorem mem_box_of_abs_le {v : Cyc} {M : ℤ} (h₁ : |psiGold v| ≤ M) (h₂ : |level v| ≤ M)
    (h₃ : |psiGold (mulZetaInv v)| ≤ M) (h₄ : |level (mulZetaInv v)| ≤ M) : v ∈ box (2 * M) := by
  obtain ⟨a, b, c, d⟩ := v
  simp only [psiGold, level, mulZetaInv, abs_le] at h₁ h₂ h₃ h₄
  simp only [box, Finset.mem_Icc, Prod.mk_le_mk]
  omega

/-- For a point `p` of one of the disks and cut levels in `[-N, N]`, the invariant set lies in the
box `[-2M, 2M]⁴` with `M = ⌈2 + 2r⌉ + 5N`, a bound that depends on `r` and `N` only. -/
theorem mem_box_of_mem_cutSet {p : ℂ} {r : ℝ} (hp : ‖p‖ ≤ 1 + r) {N : ℕ} {q₁ q₁' q₂ q₂' : ℤ}
    (hq₁ : q₁ ≤ N) (hq₁' : -N ≤ q₁') (hq₂ : q₂ ≤ N) (hq₂' : -N ≤ q₂') {v : Cyc}
    (hv : v ∈ cutSet p r q₁ q₁' q₂ q₂') : v ∈ box (2 * (⌈2 + 2 * r⌉₊ + 5 * N : ℕ)) := by
  obtain ⟨hw, -, hb₁, hb₂⟩ := hv
  set M : ℕ := ⌈2 + 2 * r⌉₊ + 5 * N with hM
  have hM' : (2 + 2 * r) + 5 * N ≤ (M : ℝ) := by
    have := Nat.le_ceil (2 + 2 * r)
    push_cast [M]
    linarith
  -- Both functionals are bounded by `2 + 2r` on the window, both levels by `5N` in the bands.
  have hgold (x : Cyc) (hx : ‖toC x‖ ≤ 1 + r) (q q' : ℤ) (hq : q ≤ N) (hq' : -N ≤ q')
      (hb : 5 * q' < level x ∧ level x ≤ 5 * q) : |psiGold x| ≤ M ∧ |level x| ≤ M := by
    have hl : |level x| ≤ 5 * N := abs_le.2 ⟨by omega, by omega⟩
    have hl' : |(level x : ℝ)| ≤ 5 * N := by exact_mod_cast hl
    have := (abs_psiGold_le x).trans (add_le_add (abs_psi_le x) hl')
    have : |(psiGold x : ℝ)| ≤ M := by linarith
    exact ⟨by exact_mod_cast this, by omega⟩
  have hnorm' : ‖toC (mulZetaInv v)‖ ≤ 1 + r := by
    rw [toC_mulZetaInv, norm_mul, norm_inv, norm_zeta, inv_one, one_mul]
    exact norm_toC_le_of_window hp hw
  obtain ⟨h₁, h₂⟩ := hgold v (norm_toC_le_of_window hp hw) q₁ q₁' hq₁ hq₁' hb₁
  obtain ⟨h₃, h₄⟩ := hgold _ hnorm' q₂ q₂' hq₂ hq₂' hb₂
  exact mem_box_of_abs_le h₁ h₂ h₃ h₄

/-! ### Finiteness below `√(3 + φ)` -/

/-- **The lower bound.** `GG 5 r` is finite for every `r < √(3 + φ)`: every orbit has at most
`5 · |box|` points, where the box depends on `r` only. -/
theorem finite_GG_five_of_lt {r : ℝ} (hr : r < √(3 + φ)) : Finite (GG 5 r) := by
  rcases lt_or_ge r 0 with hr₀ | hr₀
  · rw [GG_eq_bot_of_neg hr₀]
    infer_instance
  have hr₂ : r ^ 2 < 3 + φ := by
    have := goldenRatio_gt
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 3 + φ by linarith)
    nlinarith [Real.sqrt_nonneg (3 + φ)]
  obtain ⟨N, hN⟩ := exists_isCutLevel hr₂
  set K : ℤ := 2 * (⌈2 + 2 * r⌉₊ + 5 * N : ℕ) + 1 with hK
  refine finite_of_encard_orbit_le rfl (Set.toFinite {genA 5 r, genB 5 r}) (units ×ˢ box K).card
    fun p ↦ ?_
  by_cases hp : ‖p + 1‖ ≤ r ∨ ‖p - 1‖ ≤ r
  swap
  · -- A point off both disks is fixed.
    rw [not_or] at hp
    rw [orbit_eq_singleton hp.1 hp.2, encard_singleton, Nat.one_le_cast, Nat.one_le_iff_ne_zero,
      Ne, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
    refine ⟨((1, 0, 0, 0), (0, 0, 0, 0)), Finset.mem_product.2 ⟨by decide, ?_⟩⟩
    simp only [box, Finset.mem_Icc, Prod.mk_le_mk]
    omega
  -- A point of a disk: the orbit is trapped by the invariant set between cut levels.
  have hpn : ‖p‖ ≤ 1 + r := by
    rcases hp with hp | hp
    · simpa using (norm_sub_le (p + 1) 1).trans (by rw [norm_one]; linarith)
    · simpa using (norm_add_le (p - 1) 1).trans (by rw [norm_one]; linarith)
  obtain ⟨⟨q₁, hq₁, hq₁N, hc₁⟩, ⟨q₁', hq₁'N, hq₁', hc₁'⟩⟩ := hN (p + 1)
  obtain ⟨⟨q₂, hq₂, hq₂N, hc₂⟩, ⟨q₂', hq₂'N, hq₂', hc₂'⟩⟩ := hN (ζ⁻¹ * (p + 1))
  have hsub := orbit_subset_reach (edgeClosed_cutSet hr₂ hc₁ hc₁' hc₂ hc₂')
    (good_cutSet hp hq₁ hq₁' hq₂ hq₂')
  -- Every pivot lies in the box: it or its tip lies in the invariant set, and the step between
  -- them has coordinates in `[-1, 1]`.
  have himg : reach p r (cutSet p r q₁ q₁' q₂ q₂') ⊆ ((units ×ˢ box K).image
      fun fv : Cyc × Cyc ↦ toC fv.1 * (p + 1 - 2 * toC fv.2) - 1 : Set ℂ) := by
    rintro _ ⟨f, v, hfv, rfl⟩
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨(f, v), Finset.mem_product.2 ⟨hfv.unit, ?_⟩, rfl⟩)
    rcases hfv.mem with hv | hv
    · have := mem_box_of_mem_cutSet hpn hq₁N hq₁'N hq₂N hq₂'N hv
      obtain ⟨a, b, c, d⟩ := v
      simp only [box, Finset.mem_Icc, Prod.mk_le_mk] at this ⊢
      omega
    · have h₁ := mem_box_of_mem_cutSet hpn hq₁N hq₁'N hq₂N hq₂'N hv
      have h₂ := mem_Icc_of_mem_units _ (bar_mem_units _ hfv.unit)
      generalize bar f = t at h₁ h₂
      obtain ⟨a, b, c, d⟩ := v
      obtain ⟨a', b', c', d'⟩ := t
      simp only [box, Finset.mem_Icc, Prod.mk_le_mk, Prod.mk_add_mk] at h₁ h₂ ⊢
      omega
  calc (orbit (GG 5 r) p).encard
      ≤ ((units ×ˢ box K).image
          fun fv : Cyc × Cyc ↦ toC fv.1 * (p + 1 - 2 * toC fv.2) - 1 : Set ℂ).encard :=
        encard_le_encard (hsub.trans himg)
    _ ≤ (units ×ˢ box K).card := by
        rw [encard_coe_eq_coe_finsetCard]
        exact_mod_cast Finset.card_image_le

end CriticalRadiusFive

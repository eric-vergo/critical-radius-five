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

Fix `r < √(3 + φ)`. By the pivot walk (`PivotWalk.lean`) it suffices to trap the pivots and tips
of every orbit in a set `V` of lattice points that is closed under the typed steps inside the
window and whose size is bounded in terms of `r` alone. The set is cut out by a real functional
and its *level*.

**The cut functional.** Let `u = 1 - ζ + ζ²` and `ψ(ν) = 2 Re(ū ν)`. On the lattice
`ψ(ν) = A(ν) + B(ν) φ` with integers `A`, `B`, and the *level* `ℓ(ν) = -A(ν) - 3 B(ν)` satisfies

`ψ(ν) + ℓ(ν) = -δ B(ν)`,  `δ = 3 - φ`  (`psi_add_level`),

so the values of `ψ` at level `ℓ` form the progression `-ℓ + δ ℤ`. Along a step `e ∈ μ₅` the level
changes by `ℓ(e) ∈ {3, -2}`, and `ℓ ≡ 3 · class (mod 5)`: pivots sit at levels `≡ 0`, tips at
levels `≡ 3`. The level can therefore only overshoot a bound `5q` through an *active* step
(`ℓ(e) = 3`) leaving a pivot at level exactly `5q` (or, going down, arriving at one).

**The lens.** Both endpoints of such a step lie in the window, so by the lens bound `ψ` of the pivot
lies within `L(r) = √((7 - 4φ)/4) · √(r² - 1)` of a centre depending only on `p`
(`abs_psi_sub_cutCenter_le`). For `r < √(3 + φ)` the window is shorter than the period:
`2 L(r) < δ` (`two_mul_lensWidth_lt`), with equality exactly at `r = √(3 + φ)`.

**Cut levels.** The progressions `-5q + δ ℤ` rotate with `q` by the irrational number
`5 / δ ≡ 1/φ (mod 1)`, so there are *cut levels* `qTop ≥ 1` and `qBot ≤ -1` at which the window misses
the progression, within a bound `N` depending on `r` only (`exists_cut_levels`). No step of the
walk crosses a cut level, so the level stays in the band `(5qBot, 5qTop]` (`level_mem_band`). The same
holds for the rotated functional `ψ ∘ ζ⁻¹`.

**Discreteness.** In the window `ψ` and `ψ ∘ ζ⁻¹` are bounded; in the bands so are the two levels;
together they bound the coordinates of the lattice point (`abs_coords_le`). So all pivots lie in a
box whose size depends on `r` only, every orbit has at most `5 · |box|` points, and the group is
finite (`finite_of_encard_orbit_le`).
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

theorem level_add (v w : Cyc) : level (v + w) = level v + level w := by
  obtain ⟨a, b, c, d⟩ := v
  obtain ⟨a', b', c', d'⟩ := w
  simp only [level]
  ring

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

/-- The progressions `-5q + δ ℤ` rotate with `q` by `-5/δ = -(2 + φ)`, an irrational number. -/
theorem irrational_neg_five_div : Irrational (-5 / (3 - φ)) := by
  have := goldenRatio_lt
  have h : -5 / (3 - φ) = -(φ + (2 : ℕ)) := by
    rw [div_eq_iff (by linarith), Nat.cast_ofNat]
    linear_combination -Real.goldenRatio_sq
  rw [h]
  exact (Real.goldenRatio_irrational.add_natCast 2).neg

/-- A pivot on a cut level cannot take an active step inside the window: its value of `ψ` would lie
both in the lens window and in the progression that the window misses. -/
theorem level_ne_of_cut {w₀ : ℂ} {r : ℝ} (hr : r ^ 2 < 3 + φ) {q : ℤ}
    (hq : ∀ P : ℤ, lensWidth r < |(3 - φ) * P + -5 * q - cutCenter w₀|) {x e : Cyc}
    (he : e ∈ units) (hlev : level e = 3) (hx : ‖w₀ - 2 * toC x‖ ≤ r)
    (hxe : ‖w₀ - 2 * toC (x + e)‖ ≤ r) : level x ≠ 5 * q := by
  intro hxq
  have h₁ := abs_psi_sub_cutCenter_le hr he hlev hx hxe
  have h₂ := psi_add_level x
  rw [hxq] at h₂
  have h₃ := hq (-psiGold x)
  push_cast at h₂ h₃
  rw [show (3 - φ) * -(psiGold x : ℝ) + -5 * q - cutCenter w₀ = psi x - cutCenter w₀ by
    linarith] at h₃
  linarith

/-- **No step of the walk crosses a cut level.** If `qTop` and `qBot` are cut levels for the window
centre `w₀`, a typed step between two points of the window — from a pivot (class `0`) by `+e`, or
from a tip (class `1`) by `-e` — keeps the level in the band `(5 qBot, 5 qTop]`. -/
theorem level_mem_band {w₀ : ℂ} {r : ℝ} (hr : r ^ 2 < 3 + φ) {qTop qBot : ℤ}
    (hqTop : ∀ P : ℤ, lensWidth r < |(3 - φ) * P + -5 * qTop - cutCenter w₀|)
    (hqBot : ∀ P : ℤ, lensWidth r < |(3 - φ) * P + -5 * qBot - cutCenter w₀|)
    {v v' e : Cyc} (he : e ∈ units) (hv : ‖w₀ - 2 * toC v‖ ≤ r) (hv' : ‖w₀ - 2 * toC v'‖ ≤ r)
    (hstep : cls v % 5 = 0 ∧ v' = v + e ∨ cls v % 5 = 1 ∧ v' = v - e)
    (hband : 5 * qBot < level v ∧ level v ≤ 5 * qTop) :
    5 * qBot < level v' ∧ level v' ≤ 5 * qTop := by
  have hmod := level_emod_five v
  rcases hstep with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
  · -- From a pivot: the level can only overshoot `5 qTop` from `5 qTop` itself, by an active step.
    rw [level_add]
    rcases level_of_mem_units e he with h3 | h2
    · have := level_ne_of_cut hr hqTop he h3 hv hv'
      omega
    · omega
  · -- From a tip: the level can only undershoot `5 qBot` by landing on a pivot at `5 qBot`.
    rw [level_sub]
    rcases level_of_mem_units e he with h3 | h2
    · have := level_ne_of_cut hr hqBot he h3 hv' (by rwa [sub_add_cancel])
      rw [level_sub] at this
      omega
    · omega

/-! ### Discreteness -/

theorem lensWidth_nonneg (r : ℝ) : 0 ≤ lensWidth r :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

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

/-- `|ψ(ν)| ≤ 2 ‖ν‖`, as `‖u‖ = 2 - φ ≤ 1`. -/
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

/-- The golden part of `ψ` is controlled by `ψ` and the level: `δ B = -(ψ + ℓ)`. -/
theorem abs_psiGold_le (v : Cyc) : |(psiGold v : ℝ)| ≤ |psi v| + |(level v : ℝ)| := by
  have := goldenRatio_lt
  have h := psi_add_level v
  have h₁ : |(psiGold v : ℝ)| * (3 - φ) = |psi v + level v| := by
    rw [h, abs_mul, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < 3 - φ), mul_comm]
  have h₂ := abs_add_le (psi v) (level v)
  nlinarith [abs_nonneg (psiGold v : ℝ)]

/-- **Discreteness.** A lattice point is determined by the golden parts and the levels of its two
cut functionals `ψ` and `ψ ∘ ζ⁻¹`: the integer matrix of these four coordinates has
determinant `-5`, so bounding them by `M` bounds the point's coordinates by `2M`. -/
theorem mem_box_of_abs_le {v : Cyc} {M : ℤ} (h₁ : |psiGold v| ≤ M) (h₂ : |level v| ≤ M)
    (h₃ : |psiGold (mulZetaInv v)| ≤ M) (h₄ : |level (mulZetaInv v)| ≤ M) :
    v ∈ Finset.Icc (-(2 * M), -(2 * M), -(2 * M), -(2 * M)) (2 * M, 2 * M, 2 * M, 2 * M) := by
  obtain ⟨a, b, c, d⟩ := v
  simp only [psiGold, level, mulZetaInv, abs_le] at h₁ h₂ h₃ h₄
  simp only [Finset.mem_Icc, Prod.mk_le_mk]
  omega

/-! ### Finiteness below `√(3 + φ)` -/

/-- The window of the turned walk: `‖ζ⁻¹ (p + 1) - 2 ζ⁻¹ ν‖ = ‖p + 1 - 2 ν‖`. -/
theorem norm_window_mulZetaInv (p : ℂ) (v : Cyc) :
    ‖ζ⁻¹ * (p + 1) - 2 * toC (mulZetaInv v)‖ = ‖p + 1 - 2 * toC v‖ := by
  rw [toC_mulZetaInv, show ζ⁻¹ * (p + 1) - 2 * (ζ⁻¹ * toC v) = ζ⁻¹ * (p + 1 - 2 * toC v) by ring,
    norm_mul, norm_inv, norm_zeta, inv_one, one_mul]

/-- **The lower bound.** `GG 5 r` is finite for every `r < √(3 + φ)`. -/
theorem finite_GG_five_of_lt {r : ℝ} (hr : r < √(3 + φ)) : Finite (GG 5 r) := by
  rcases lt_or_ge r 0 with hr₀ | hr₀
  · rw [GG_eq_bot_of_neg hr₀]
    infer_instance
  have := goldenRatio_gt
  have := goldenRatio_lt
  have hr₂ : r ^ 2 < 3 + φ := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 3 + φ by linarith)
    nlinarith [Real.sqrt_nonneg (3 + φ)]
  -- Cut levels, within a bound `N` depending on `r` only.
  obtain ⟨N, hN⟩ := exists_cut_levels (δ := 3 - φ) (t := -5) (by linarith)
    irrational_neg_five_div (lensWidth_nonneg r) (two_mul_lensWidth_lt hr₂)
  -- Every orbit lies in the image of `μ₅ × box`.
  set M : ℕ := ⌈2 + 2 * r⌉₊ + 5 * N with hMdef
  set K : ℤ := 2 * M + 1 with hK
  set box : Finset Cyc := Finset.Icc (-K, -K, -K, -K) (K, K, K, K)
  refine finite_of_encard_orbit_le rfl (toFinite {genA 5 r, genB 5 r}) (units ×ˢ box).card
    fun p => ?_
  by_cases hp : ‖p + 1‖ ≤ r ∨ ‖p - 1‖ ≤ r
  swap
  · -- A point off both disks is fixed.
    rw [not_or] at hp
    rw [orbit_eq_singleton hp.1 hp.2, encard_singleton, Nat.one_le_cast, Nat.one_le_iff_ne_zero,
      Ne, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
    refine ⟨((1, 0, 0, 0), (0, 0, 0, 0)), Finset.mem_product.2 ⟨by decide, ?_⟩⟩
    simp only [box, Finset.mem_Icc, Prod.mk_le_mk]
    omega
  have hpn : ‖p‖ ≤ 1 + r := by
    rcases hp with hp | hp
    · simpa using (norm_sub_le (p + 1) 1).trans (by rw [norm_one]; linarith)
    · simpa using (norm_add_le (p - 1) 1).trans (by rw [norm_one]; linarith)
  obtain ⟨⟨q₁, hq₁, hq₁N, hc₁⟩, ⟨q₁', hq₁'N, hq₁', hc₁'⟩⟩ := hN (cutCenter (p + 1))
  obtain ⟨⟨q₂, hq₂, hq₂N, hc₂⟩, ⟨q₂', hq₂'N, hq₂', hc₂'⟩⟩ := hN (cutCenter (ζ⁻¹ * (p + 1)))
  -- The invariant set: lattice points of the window, of class `0` or `1`, whose levels for `ψ`
  -- and for `ψ ∘ ζ⁻¹` lie between the cut levels.
  set V : Set Cyc := {v | Window p r v ∧ (cls v % 5 = 0 ∨ cls v % 5 = 1) ∧
    (5 * q₁' < level v ∧ level v ≤ 5 * q₁) ∧
    (5 * q₂' < level (mulZetaInv v) ∧ level (mulZetaInv v) ≤ 5 * q₂)}
  have hV : EdgeClosed p r V := by
    constructor
    · rintro v ⟨hw, -, hb₁, hb₂⟩ hc e he hwe
      have hce := cls_of_mem_units e he
      refine ⟨hwe, .inr (by rw [cls_add]; omega),
        level_mem_band hr₂ hc₁ hc₁' he hw hwe (.inl ⟨hc, rfl⟩) hb₁, ?_⟩
      refine level_mem_band hr₂ hc₂ hc₂' (mulZetaInv_mem_units e he) ?_ ?_
        (.inl ⟨by rwa [cls_mulZetaInv_emod], (mulZetaInv_add v e)⟩) hb₂
      · rw [norm_window_mulZetaInv]; exact hw
      · rw [norm_window_mulZetaInv]; exact hwe
    · rintro v ⟨hw, -, hb₁, hb₂⟩ hc e he hwe
      have hce := cls_of_mem_units e he
      refine ⟨hwe, .inl (by rw [cls_sub]; omega),
        level_mem_band hr₂ hc₁ hc₁' he hw hwe (.inr ⟨hc, rfl⟩) hb₁, ?_⟩
      refine level_mem_band hr₂ hc₂ hc₂' (mulZetaInv_mem_units e he) ?_ ?_
        (.inr ⟨by rwa [cls_mulZetaInv_emod], (mulZetaInv_sub v e)⟩) hb₂
      · rw [norm_window_mulZetaInv]; exact hw
      · rw [norm_window_mulZetaInv]; exact hwe
  -- The initial state: pivot `0`, tip `1`.
  have h₀ : Good p r V (1, 0, 0, 0) 0 := by
    have htip : (0 : Cyc) + bar (1, 0, 0, 0) = (1, 0, 0, 0) := by decide
    have hmem₀ : Window p r 0 → 0 ∈ V := fun hw => ⟨hw, .inl (by decide),
      by rw [show level 0 = 0 by decide]; omega,
      by rw [show level (mulZetaInv 0) = 0 by decide]; omega⟩
    have hmem₁ : Window p r (1, 0, 0, 0) → (1, 0, 0, 0) ∈ V := fun hw => ⟨hw, .inr (by decide),
      by rw [show level (1, 0, 0, 0) = 3 by decide]; omega,
      by rw [show level (mulZetaInv (1, 0, 0, 0)) = -2 by decide]; omega⟩
    refine ⟨by decide, by decide, hmem₀, fun hw => ?_, ?_⟩
    · rw [htip] at hw ⊢
      exact hmem₁ hw
    · rw [htip]
      rcases hp with hp | hp
      · exact .inl (hmem₀ (by simpa [Window] using hp))
      · refine .inr (hmem₁ ?_)
        rw [Window, toC_one, show p + 1 - 2 * 1 = p - 1 by ring]
        exact hp
  -- Points of `V` lie in the box `[-2M, 2M]⁴`.
  have hM : (2 + 2 * r) + 5 * N ≤ (M : ℝ) := by
    have := Nat.le_ceil (2 + 2 * r)
    push_cast [M]
    linarith
  have hbox : ∀ w ∈ V,
      w ∈ Finset.Icc (-(2 * M : ℤ), -(2 * M : ℤ), -(2 * M : ℤ), -(2 * M : ℤ))
        ((2 * M : ℤ), (2 * M : ℤ), (2 * M : ℤ), (2 * M : ℤ)) := by
    rintro w ⟨hw, -, hb₁, hb₂⟩
    have hnorm := norm_toC_le_of_window hpn hw
    have hnorm' : ‖toC (mulZetaInv w)‖ ≤ 1 + r := by
      rwa [toC_mulZetaInv, norm_mul, norm_inv, norm_zeta, inv_one, one_mul]
    have hlev (x : Cyc) (q q' : ℤ) (hq : q ≤ N) (hq' : -N ≤ q')
        (hb : 5 * q' < level x ∧ level x ≤ 5 * q) : |(level x : ℝ)| ≤ 5 * N := by
      have : |level x| ≤ 5 * N := abs_le.2 ⟨by omega, by omega⟩
      exact_mod_cast this
    have hgold (x : Cyc) (hx : ‖toC x‖ ≤ 1 + r) (hl : |(level x : ℝ)| ≤ 5 * N) :
        |psiGold x| ≤ M := by
      have := (abs_psiGold_le x).trans (add_le_add (abs_psi_le x) hl)
      have : |(psiGold x : ℝ)| ≤ M := by linarith
      exact_mod_cast this
    have h₁ := hlev w q₁ q₁' (by omega) (by omega) hb₁
    have h₂ := hlev (mulZetaInv w) q₂ q₂' (by omega) (by omega) hb₂
    exact mem_box_of_abs_le (hgold w hnorm h₁) (abs_le.2 ⟨by omega, by omega⟩)
      (hgold _ hnorm' h₂) (abs_le.2 ⟨by omega, by omega⟩)
  -- Every pivot lies in the box: it or its tip is in `V`, and a tip step has coordinates in
  -- `[-1, 1]`.
  have himg : Reach p r V ⊆ ((units ×ˢ box).image
      fun fv : Cyc × Cyc => toC fv.1 * (p + 1 - 2 * toC fv.2) - 1 : Set ℂ) := by
    rintro _ ⟨f, v, hfv, rfl⟩
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨(f, v), Finset.mem_product.2 ⟨hfv.unit, ?_⟩, rfl⟩)
    rcases hfv.mem with hv | hv
    · have := hbox v hv
      obtain ⟨a, b, c, d⟩ := v
      simp only [box, Finset.mem_Icc, Prod.mk_le_mk] at this ⊢
      omega
    · have h₁ := hbox _ hv
      have h₂ := mem_Icc_of_mem_units _ (bar_mem_units _ hfv.unit)
      generalize bar f = t at h₁ h₂
      obtain ⟨a, b, c, d⟩ := v
      obtain ⟨a', b', c', d'⟩ := t
      simp only [box, Finset.mem_Icc, Prod.mk_le_mk, Prod.mk_add_mk] at h₁ h₂ ⊢
      omega
  calc (orbit (GG 5 r) p).encard
      ≤ ((units ×ˢ box).image
          fun fv : Cyc × Cyc => toC fv.1 * (p + 1 - 2 * toC fv.2) - 1 : Set ℂ).encard :=
        encard_le_encard ((orbit_subset_reach hV h₀).trans himg)
    _ ≤ (units ×ˢ box).card := by
        rw [encard_coe_eq_coe_finsetCard]
        exact_mod_cast Finset.card_image_le

end CriticalRadiusFive

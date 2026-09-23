/-
Copyright (c) 2026 The critical-radius-five authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The critical-radius-five authors
-/
import CriticalRadiusFive.Basic

/-!
# Exact arithmetic in `ℤ[ζ₅]`

Everything about `ζ = exp(2πi/5)` used by the two halves of the proof. Every point reached from `0`
by the generators of `GG 5 r` lies in the lattice `ℤ[ζ₅]`, and all the radii and lengths that
matter lie in `ℚ(φ) = ℚ(√5)`, so the proof can be carried out by exact computation.

* The fifth root of unity: `ζ⁵ = 1`, `1 + ζ + ζ² + ζ³ + ζ⁴ = 0`, `ζ̄ = ζ⁻¹ = ζ⁴`, and
  `ζ + ζ⁴ = φ - 1` (that is, `2 cos(2π/5) = 1/φ`).
* The lattice in the power basis: `Cyc = ℤ × ℤ × ℤ × ℤ`, where `(a, b, c, d)` stands for
  `Cyc.toC (a, b, c, d) = a + bζ + cζ² + dζ³`; multiplication by `ζ` and by `ζ⁻¹` and complex
  conjugation in these coordinates; the five fifth roots of unity `Cyc.units`; and the class
  `Cyc.cls` of a lattice point modulo the prime `1 - ζ` above `5` (as `ζ ≡ 1`, the class of
  `a + bζ + cζ² + dζ³` is `a + b + c + d` modulo `5`).
* The norm form (`Cyc.norm_toC_sq`): `‖a + bζ + cζ² + dζ³‖² = N + M φ` with explicit integer
  quadratic forms `N`, `M`, and an integer test `goldenNonpos` for the sign of `x + y φ`. Together
  they turn every disk-membership test for a lattice point into a finite computation.
-/

noncomputable section

open Complex ComplexConjugate
open scoped goldenRatio

namespace CriticalRadiusFive

local notation "ζ" => zeta 5

/-! ### The fifth root of unity -/

/-- `ζ = exp(2πi/5)` is a primitive fifth root of unity. -/
theorem isPrimitiveRoot_zeta_five : IsPrimitiveRoot ζ 5 := by
  simpa [zeta] using isPrimitiveRoot_exp 5 (by norm_num)

/-- `ζ⁵ = 1`. -/
theorem zeta_five_pow_five : ζ ^ 5 = 1 :=
  isPrimitiveRoot_zeta_five.pow_eq_one

/-- The cyclotomic relation `Φ₅(ζ) = 0`. -/
theorem cyclotomic_zeta_five : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
  simpa [Finset.sum_range_succ, add_assoc] using
    isPrimitiveRoot_zeta_five.geom_sum_eq_zero (by norm_num)

/-- `ζ⁻¹ = ζ⁴`. -/
theorem zeta_five_inv : ζ⁻¹ = ζ ^ 4 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ', zeta_five_pow_five])

/-- `ζ̄ = ζ⁴`. -/
theorem conj_zeta_five : conj ζ = ζ ^ 4 := by
  rw [← zeta_five_inv, zeta, ← exp_conj, ← exp_neg]
  congr 1
  simp only [map_div₀, map_mul, conj_I, conj_ofReal, map_natCast, map_ofNat]
  ring

/-- `ζ + ζ⁴ = 2 cos(2π/5) = φ - 1 = 1/φ`. -/
theorem zeta_five_add_pow_four : ζ + ζ ^ 4 = (φ : ℂ) - 1 := by
  have hre : (zeta 5).re = (φ - 1) / 2 := by
    rw [zeta, show 2 * (Real.pi : ℂ) * I / (5 : ℕ) = ((2 * (Real.pi / 5) : ℝ) : ℂ) * I by
      push_cast; ring, exp_ofReal_mul_I_re, Real.cos_two_mul, Real.cos_pi_div_five,
      Real.goldenRatio]
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    ring
  rw [← conj_zeta_five, add_conj, hre]
  push_cast
  ring

/-! ### The lattice `ℤ[ζ₅]` in the power basis -/

/-- The ring `ℤ[ζ₅]` in the power basis `1, ζ, ζ², ζ³`: the quadruple `(a, b, c, d)` stands for
`a + bζ + cζ² + dζ³`. -/
abbrev Cyc : Type := ℤ × ℤ × ℤ × ℤ

namespace Cyc

/-- The complex number `a + bζ + cζ² + dζ³` represented by `(a, b, c, d)`. -/
def toC : Cyc → ℂ
  | (a, b, c, d) => a + b * ζ + c * ζ ^ 2 + d * ζ ^ 3

/-- Multiplication by `ζ`, using `ζ⁴ = -1 - ζ - ζ² - ζ³`. -/
def mulZeta : Cyc → Cyc
  | (a, b, c, d) => (-d, a - d, b - d, c - d)

/-- Multiplication by `ζ⁻¹ = ζ⁴`. -/
def mulZetaInv : Cyc → Cyc
  | (a, b, c, d) => (b - a, c - a, d - a, -a)

/-- Complex conjugation, `ζ ↦ ζ⁴`. -/
def bar : Cyc → Cyc
  | (a, b, c, d) => (a - b, -b, d - b, c - b)

/-- The five fifth roots of unity `1, ζ, ζ², ζ³, ζ⁴`. -/
def units : Finset Cyc :=
  {(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1), (-1, -1, -1, -1)}

/-- The class of a lattice point modulo the prime `1 - ζ`: since `ζ ≡ 1`, the point
`a + bζ + cζ² + dζ³` is congruent to the integer `a + b + c + d`, taken modulo `5`. -/
def cls : Cyc → ℤ
  | (a, b, c, d) => a + b + c + d

/-- The rational part `N` of the norm form `‖toC v‖² = N + M φ`. -/
def normRat : Cyc → ℤ
  | (a, b, c, d) => a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 - a * b - b * c - c * d

/-- The golden part `M` of the norm form `‖toC v‖² = N + M φ`. -/
def normGold : Cyc → ℤ
  | (a, b, c, d) => a * b + b * c + c * d - a * c - b * d - a * d

/-- `toC` is additive. -/
theorem toC_add (v w : Cyc) : toC (v + w) = toC v + toC w := by
  obtain ⟨a, b, c, d⟩ := v
  obtain ⟨a', b', c', d'⟩ := w
  simp only [toC]
  push_cast
  ring

/-- `toC` commutes with negation. -/
theorem toC_neg (v : Cyc) : toC (-v) = -toC v := by
  obtain ⟨a, b, c, d⟩ := v
  simp only [toC]
  push_cast
  ring

/-- `toC` commutes with subtraction. -/
theorem toC_sub (v w : Cyc) : toC (v - w) = toC v - toC w := by
  rw [sub_eq_add_neg, toC_add, toC_neg, sub_eq_add_neg]

/-- `toC 0 = 0`. -/
@[simp] theorem toC_zero : toC 0 = 0 := by
  simp [toC]

/-- `toC (1, 0, 0, 0) = 1`. -/
@[simp] theorem toC_one : toC (1, 0, 0, 0) = 1 := by
  simp [toC]

/-- `mulZeta` is multiplication by `ζ`. -/
theorem toC_mulZeta (v : Cyc) : toC (mulZeta v) = ζ * toC v := by
  obtain ⟨a, b, c, d⟩ := v
  simp only [toC, mulZeta]
  push_cast
  linear_combination (-(d : ℂ)) * cyclotomic_zeta_five

/-- `mulZetaInv` is multiplication by `ζ⁻¹`. -/
theorem toC_mulZetaInv (v : Cyc) : toC (mulZetaInv v) = ζ⁻¹ * toC v := by
  obtain ⟨a, b, c, d⟩ := v
  simp only [toC, mulZetaInv, zeta_five_inv]
  push_cast
  linear_combination (-(a : ℂ) + b - b * ζ + c * ζ - c * ζ ^ 2 + d * ζ ^ 2 - d * ζ ^ 3) *
    cyclotomic_zeta_five

/-- `bar` is complex conjugation. -/
theorem toC_bar (v : Cyc) : toC (bar v) = conj (toC v) := by
  obtain ⟨a, b, c, d⟩ := v
  simp only [toC, bar, map_add, map_mul, map_intCast, map_pow, conj_zeta_five]
  push_cast
  linear_combination (-(b : ℂ) - c * ζ ^ 4 + c * ζ ^ 3 - d * ζ ^ 8 + d * ζ ^ 7 - d * ζ ^ 3 +
    d * ζ ^ 2) * cyclotomic_zeta_five

/-- Multiplication by `ζ⁻¹` is additive. -/
theorem mulZetaInv_add (v w : Cyc) : mulZetaInv (v + w) = mulZetaInv v + mulZetaInv w := by
  obtain ⟨a, b, c, d⟩ := v
  obtain ⟨a', b', c', d'⟩ := w
  simp only [mulZetaInv, Prod.mk_add_mk, Prod.mk.injEq]
  omega

/-- Multiplication by `ζ⁻¹` commutes with subtraction. -/
theorem mulZetaInv_sub (v w : Cyc) : mulZetaInv (v - w) = mulZetaInv v - mulZetaInv w := by
  obtain ⟨a, b, c, d⟩ := v
  obtain ⟨a', b', c', d'⟩ := w
  simp only [mulZetaInv, Prod.mk_sub_mk, Prod.mk.injEq]
  omega

/-- The class is additive. -/
theorem cls_add (v w : Cyc) : cls (v + w) = cls v + cls w := by
  obtain ⟨a, b, c, d⟩ := v
  obtain ⟨a', b', c', d'⟩ := w
  simp only [cls]
  ring

/-- The class commutes with subtraction. -/
theorem cls_sub (v w : Cyc) : cls (v - w) = cls v - cls w := by
  obtain ⟨a, b, c, d⟩ := v
  obtain ⟨a', b', c', d'⟩ := w
  simp only [cls, Prod.mk_sub_mk]
  ring

/-! ### The norm form -/

/-- **The norm form of `ℤ[ζ₅]`**:
`‖a + bζ + cζ² + dζ³‖² = (a² + b² + c² + d² - ab - bc - cd) + (ab + bc + cd - ac - bd - ad) φ`. -/
theorem norm_toC_sq (v : Cyc) : ‖toC v‖ ^ 2 = normRat v + normGold v * φ := by
  have h : toC v * toC (bar v) = (normRat v : ℂ) + (normGold v : ℂ) * (φ : ℂ) := by
    have hφ := zeta_five_add_pow_four
    generalize (φ : ℂ) = Φ at hφ ⊢
    obtain ⟨a, b, c, d⟩ := v
    simp only [toC, bar, normRat, normGold]
    push_cast
    linear_combination (-(a : ℂ) * b + a * c + a * d - b ^ 2 + b * d - c ^ 2 - d ^ 2 +
      (c * d - b * d) * ζ ^ 2 + (c ^ 2 - b * c - c * d + d ^ 2) * ζ) * cyclotomic_zeta_five +
      (a * b + b * c + c * d - a * c - b * d - a * d : ℂ) * hφ
  rw [toC_bar, mul_conj, ← Complex.sq_norm] at h
  exact_mod_cast h

/-- Roots of unity have absolute value `1`. -/
theorem norm_toC_of_mem_units {e : Cyc} (he : e ∈ units) : ‖toC e‖ = 1 := by
  have h : normRat e = 1 ∧ normGold e = 0 := by revert e he; decide
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, norm_toC_sq, h.1, h.2]
  simp

/-- For a root of unity `e`, `e ē = 1`. -/
theorem toC_mul_toC_bar_of_mem_units {e : Cyc} (he : e ∈ units) :
    toC e * toC (bar e) = 1 := by
  rw [toC_bar, mul_conj, ← Complex.sq_norm, norm_toC_of_mem_units he]
  norm_num

/-- Multiplication by `ζ` permutes the fifth roots of unity. -/
theorem mulZeta_mem_units : ∀ e ∈ units, mulZeta e ∈ units := by decide

/-- Multiplication by `ζ⁻¹` permutes the fifth roots of unity. -/
theorem mulZetaInv_mem_units : ∀ e ∈ units, mulZetaInv e ∈ units := by decide

/-- Conjugation permutes the fifth roots of unity. -/
theorem bar_mem_units : ∀ e ∈ units, bar e ∈ units := by decide

/-- Multiplication by `ζ⁻¹` does not change the class, as `ζ ≡ 1` modulo `1 - ζ`. -/
theorem cls_mulZetaInv_emod (v : Cyc) : cls (mulZetaInv v) % 5 = cls v % 5 := by
  obtain ⟨a, b, c, d⟩ := v
  simp only [cls, mulZetaInv]
  omega

/-- The coordinates of a root of unity are `-1`, `0` or `1`. -/
theorem mem_Icc_of_mem_units : ∀ e ∈ units, e ∈ Finset.Icc (-1, -1, -1, -1) (1, 1, 1, 1) := by
  decide

/-- Every fifth root of unity is congruent to `1` modulo `1 - ζ`. -/
theorem cls_of_mem_units : ∀ e ∈ units, cls e % 5 = 1 := by decide

end Cyc

/-! ### The golden ratio -/

/-- `1.618 < φ`. -/
theorem goldenRatio_gt : 1.618 < φ := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  rw [Real.goldenRatio]
  nlinarith [Real.sqrt_nonneg 5]

/-- `φ < 1.6181`. -/
theorem goldenRatio_lt : φ < 1.6181 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  rw [Real.goldenRatio]
  nlinarith [Real.sqrt_nonneg 5]

/-! ### The sign of `x + y φ` -/

/-- An integer test for `x + y φ ≤ 0`, `x y : ℤ`. With `s = 2x + y` one has
`2 (x + y φ) = s + y √5`, which is `≤ 0` when `s` and `y` are both `≤ 0`, or when `s ≤ 0` and
`5 y² ≤ s²`, or when `y < 0` and `s² ≤ 5 y²`. -/
def goldenNonpos (x y : ℤ) : Bool :=
  (2 * x + y ≤ 0 && (y ≤ 0 || 5 * y ^ 2 ≤ (2 * x + y) ^ 2)) ||
    (y < 0 && (2 * x + y) ^ 2 ≤ 5 * y ^ 2)

/-- Soundness of the integer test: `goldenNonpos x y` implies `x + y φ ≤ 0`. -/
theorem add_mul_goldenRatio_nonpos {x y : ℤ} (h : goldenNonpos x y = true) : x + y * φ ≤ 0 := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5' : 0 ≤ √5 := Real.sqrt_nonneg 5
  have key : 2 * (x + y * φ) = (2 * x + y : ℤ) + y * √5 := by
    rw [Real.goldenRatio]
    push_cast
    ring
  suffices (2 * x + y : ℤ) + y * √5 ≤ 0 by linarith
  set s : ℤ := 2 * x + y
  simp only [goldenNonpos, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨hs, hy | hy⟩ | ⟨hy, hsy⟩
  · have : (s : ℝ) ≤ 0 := by exact_mod_cast hs
    have : (y : ℝ) ≤ 0 := by exact_mod_cast hy
    nlinarith
  · -- `s ≤ 0` and `5 y² ≤ s²`: if `s + y √5 > 0` then `(y √5)² > s²`.
    have hs' : (s : ℝ) ≤ 0 := by exact_mod_cast hs
    have hy' : 5 * (y : ℝ) ^ 2 ≤ (s : ℝ) ^ 2 := by exact_mod_cast hy
    by_contra! hpos
    have := mul_pos hpos (show 0 < (y : ℝ) * √5 - s by linarith)
    nlinarith
  · -- `y < 0` and `s² ≤ 5 y²`: if `s + y √5 > 0` then `s² > (y √5)²`.
    have hy' : (y : ℝ) < 0 := by exact_mod_cast hy
    have hsy' : (s : ℝ) ^ 2 ≤ 5 * (y : ℝ) ^ 2 := by exact_mod_cast hsy
    have : (y : ℝ) * √5 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hy'.le h5'
    by_contra! hpos
    have := mul_pos hpos (show 0 < (s : ℝ) - y * √5 by linarith)
    nlinarith

end CriticalRadiusFive

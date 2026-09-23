/-
Copyright (c) 2026 The critical-radius-five authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The critical-radius-five authors
-/
import Mathlib

/-!
# The lens bound

Let `w` and `w'` be two points of the closed disk of radius `r` about the origin with
`w - w' = 2g`, `‖g‖ = 1`. Their midpoint `m = (w + w') / 2` satisfies `‖m ± g‖ ≤ r`: it lies in the
*lens* in which two disks of radius `r` with centres `2` apart overlap. The lens is short in the
direction of `g` and tall — of half-height `√(r² - 1)` — in the perpendicular direction.

`abs_re_mul_add_le` bounds a real linear functional `z ↦ Re(U z)` on the lens. When `U` is close
enough to perpendicular to `g` — precisely, `|Re(U g)| √(r² - 1) ≤ |Im(U g)|` — the maximum is
attained at the vertices of the lens, and `|Re(U (w + w'))| ≤ 2 |Im(U g)| √(r² - 1)`.

This is where the critical radius enters the lower bound: a step of the orbit invariant forces both
of its endpoints into a disk, so a lattice point lies in a window of width
`2 |Im(U g)| √(r² - 1)`, and that width reaches the period of the relevant lattice exactly at
`r = √(3 + φ)`.
-/

open Complex ComplexConjugate

namespace CriticalRadiusFive

/-- The lens, algebraically: for `X, Y ≥ 0` with `(X + 1)² + Y² ≤ K² + 1` and `C K ≤ D`, the
maximum of `C X + D Y` is `D K`, attained at the vertex `X = 0`, `Y = K`. -/
theorem lens_linear_le {X Y C D K : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hXY : (X + 1) ^ 2 + Y ^ 2 ≤ K ^ 2 + 1) (hCD : C * K ≤ D) : C * X + D * Y ≤ D * K := by
  rcases hK.eq_or_lt with rfl | hK
  · -- A degenerate lens is a single point.
    obtain rfl : X = 0 := by nlinarith
    obtain rfl : Y = 0 := by nlinarith
    simp
  -- On the lens `Y ≤ K - X / K`, and `C ≤ D / K`.
  have hD : 0 ≤ D := le_trans (by positivity) hCD
  have hYK : Y ≤ K - X / K := by
    have h₁ : 0 ≤ K - X / K := by
      rw [sub_nonneg, div_le_iff₀ hK]
      nlinarith
    have h₂ : Y ^ 2 ≤ (K - X / K) ^ 2 := by
      have : (K - X / K) ^ 2 = K ^ 2 - 2 * X + (X / K) ^ 2 := by field_simp; ring
      nlinarith [sq_nonneg (X / K)]
    exact (sq_le_sq₀ hY h₁).1 h₂
  have hCK : C ≤ D / K := by rwa [le_div_iff₀ hK]
  have h₃ := mul_le_mul_of_nonneg_left hYK hD
  have h₄ := mul_le_mul_of_nonneg_right hCK hX
  have h₅ : D * (X / K) = D / K * X := by ring
  linarith

/-- **The lens bound.** If `‖w‖ ≤ r`, `‖w'‖ ≤ r` and `w - w' = 2g` with `‖g‖ = 1`, and
`|Re(U g)| ≤ C`, `|Im(U g)| ≤ D` with `C √(r² - 1) ≤ D`, then
`|Re(U (w + w'))| ≤ 2 D √(r² - 1)`. -/
theorem abs_re_mul_add_le {U g w w' : ℂ} {r C D : ℝ} (hg : ‖g‖ = 1) (hw : ‖w‖ ≤ r)
    (hw' : ‖w'‖ ≤ r) (hww' : w - w' = 2 * g) (hC : |(U * g).re| ≤ C) (hD : |(U * g).im| ≤ D)
    (hCD : C * √(r ^ 2 - 1) ≤ D) : |(U * (w + w')).re| ≤ 2 * (D * √(r ^ 2 - 1)) := by
  -- Coordinates `x + i y` of the midpoint, in the frame in which `g = 1`.
  have hgg : g * conj g = 1 := by rw [mul_conj, normSq_eq_norm_sq, hg]; norm_num
  set ξ := (w + w') / 2 * conj g
  have hw₁ : w * conj g = ξ + 1 := by linear_combination (conj g / 2) * hww' + hgg
  have hw₂ : w' * conj g = ξ - 1 := by linear_combination (-conj g / 2) * hww' - hgg
  have hsq (z : ℂ) (h : ‖z‖ ≤ r) (c : ℝ) (hz : z * conj g = ξ + c) :
      (ξ.re + c) ^ 2 + ξ.im ^ 2 ≤ r ^ 2 := by
    have h₁ : ‖z * conj g‖ = ‖z‖ := by rw [norm_mul, RCLike.norm_conj, hg, mul_one]
    have h₂ : ‖z * conj g‖ ^ 2 = (ξ.re + c) ^ 2 + ξ.im ^ 2 := by
      rw [hz, ← normSq_eq_norm_sq, normSq_apply]
      simp only [add_re, add_im, ofReal_re, ofReal_im, add_zero]
      ring
    rw [← h₂, h₁]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have h₁ := hsq w hw 1 (by simpa using hw₁)
  have h₂ := hsq w' hw' (-1) (by simpa [sub_eq_add_neg] using hw₂)
  -- The functional in these coordinates.
  have hre : (U * (w + w')).re = 2 * ((U * g).re * ξ.re - (U * g).im * ξ.im) := by
    have : U * (w + w') = 2 * ((U * g) * ξ) := by
      simp only [ξ]
      linear_combination (-(U * (w + w'))) * hgg
    rw [this]
    simp [mul_re]
  -- The lens constraint `(|x| + 1)² + |y|² ≤ K² + 1`, `K = √(r² - 1)`.
  set K := √(r ^ 2 - 1)
  have hK : K ^ 2 = r ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hlens : (|ξ.re| + 1) ^ 2 + |ξ.im| ^ 2 ≤ K ^ 2 + 1 := by
    rw [hK, sq_abs]
    rcases abs_cases ξ.re with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nlinarith
  have hmain := lens_linear_le (abs_nonneg ξ.re) (abs_nonneg ξ.im) ((abs_nonneg _).trans hC)
    (Real.sqrt_nonneg _) hlens hCD
  rw [hre, abs_mul, abs_two]
  have : |(U * g).re * ξ.re - (U * g).im * ξ.im| ≤ C * |ξ.re| + D * |ξ.im| := by
    calc _ ≤ |(U * g).re * ξ.re| + |(U * g).im * ξ.im| := abs_sub _ _
      _ ≤ C * |ξ.re| + D * |ξ.im| := by
        rw [abs_mul, abs_mul]
        gcongr
  linarith

end CriticalRadiusFive

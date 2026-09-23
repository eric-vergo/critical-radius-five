/-
Copyright (c) 2026 The critical-radius-five authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The critical-radius-five authors
-/
import CriticalRadiusFive.Defs

/-!
# Basic properties of the turns and of the groups `GG n r`

* A turn rotates its disk and fixes everything else; its inverse is the turn by the opposite
  angle (`turn_apply_of_le`, `turn_apply_of_not_le`, `turn_inv`).
* With `ζ = exp(2πi/n)`, the generators and their inverses act on their disks as
  `a^{±1} : z ↦ ζ^{∓1} (z + 1) - 1` and `b^{±1} : z ↦ ζ^{∓1} (z - 1) + 1`, and fix every point off
  their disks.
* **Invariance principle** (`orbit_subset_of_mapsTo`): a set of points that is mapped into itself
  by both generators and by their inverses contains the orbit of each of its points. The lower
  bound traps every orbit in a finite set this way; the simplest instance is that a point off both
  disks is fixed by the whole group (`orbit_eq_singleton`).
-/

noncomputable section

open Complex Set

namespace CriticalRadiusFive

variable {c z : ℂ} {n : ℕ} {r θ : ℝ}

/-! ### Turns -/

/-- On its disk, a turn is the rotation `z ↦ c + exp(iθ) (z - c)`. -/
theorem turn_apply_of_le (h : ‖z - c‖ ≤ r) : turn c r θ z = c + exp (θ * I) * (z - c) :=
  ite_eq_left h

/-- Off its disk, a turn is the identity. -/
theorem turn_apply_of_not_le (h : ¬‖z - c‖ ≤ r) : turn c r θ z = z :=
  ite_eq_right h

/-- The inverse of a turn is the turn by the opposite angle. -/
theorem turn_inv (c : ℂ) (r θ : ℝ) : (turn c r θ)⁻¹ = turn c r (-θ) := by
  ext z
  simp [turn, Equiv.Perm.inv_def]

/-! ### The generators -/

/-- `ζ = exp(2πi/n)`, the primitive `n`-th root of unity by which the generators turn. -/
def zeta (n : ℕ) : ℂ := exp (2 * Real.pi * I / n)

/-- The rotation by the angle `2π/n` is multiplication by `ζ`. -/
theorem exp_two_pi_div_mul_I (n : ℕ) : exp (((2 * Real.pi / n : ℝ) : ℂ) * I) = zeta n := by
  rw [zeta]
  push_cast
  ring_nf

/-- The rotation by the angle `-2π/n`, the turn of the generators, is multiplication by `ζ⁻¹`. -/
theorem exp_neg_two_pi_div_mul_I (n : ℕ) :
    exp (((-(2 * Real.pi / n) : ℝ) : ℂ) * I) = (zeta n)⁻¹ := by
  rw [ofReal_neg, neg_mul, exp_neg, exp_two_pi_div_mul_I]

/-- `ζ` has absolute value `1`. -/
theorem norm_zeta (n : ℕ) : ‖zeta n‖ = 1 := by
  rw [← exp_two_pi_div_mul_I, norm_exp_ofReal_mul_I]

/-- `ζ ≠ 0`. -/
theorem zeta_ne_zero (n : ℕ) : zeta n ≠ 0 := exp_ne_zero _

/-- On the left disk, `a` is `z ↦ ζ⁻¹ (z + 1) - 1`. -/
theorem genA_apply_of_le (h : ‖z + 1‖ ≤ r) : genA n r z = (zeta n)⁻¹ * (z + 1) - 1 := by
  rw [genA, turn_apply_of_le (by rwa [sub_neg_eq_add]), exp_neg_two_pi_div_mul_I]
  ring

/-- Off the left disk, `a` is the identity. -/
theorem genA_apply_of_not_le (h : ¬‖z + 1‖ ≤ r) : genA n r z = z :=
  turn_apply_of_not_le (by rwa [sub_neg_eq_add])

/-- On the left disk, `a⁻¹` is `z ↦ ζ (z + 1) - 1`. -/
theorem genA_inv_apply_of_le (h : ‖z + 1‖ ≤ r) : (genA n r)⁻¹ z = zeta n * (z + 1) - 1 := by
  rw [genA, turn_inv, neg_neg, turn_apply_of_le (by rwa [sub_neg_eq_add]), exp_two_pi_div_mul_I]
  ring

/-- Off the left disk, `a⁻¹` is the identity. -/
theorem genA_inv_apply_of_not_le (h : ¬‖z + 1‖ ≤ r) : (genA n r)⁻¹ z = z := by
  rw [genA, turn_inv]
  exact turn_apply_of_not_le (by rwa [sub_neg_eq_add])

/-- On the right disk, `b` is `z ↦ ζ⁻¹ (z - 1) + 1`. -/
theorem genB_apply_of_le (h : ‖z - 1‖ ≤ r) : genB n r z = (zeta n)⁻¹ * (z - 1) + 1 := by
  rw [genB, turn_apply_of_le h, exp_neg_two_pi_div_mul_I]
  ring

/-- Off the right disk, `b` is the identity. -/
theorem genB_apply_of_not_le (h : ¬‖z - 1‖ ≤ r) : genB n r z = z :=
  turn_apply_of_not_le h

/-- On the right disk, `b⁻¹` is `z ↦ ζ (z - 1) + 1`. -/
theorem genB_inv_apply_of_le (h : ‖z - 1‖ ≤ r) : (genB n r)⁻¹ z = zeta n * (z - 1) + 1 := by
  rw [genB, turn_inv, neg_neg, turn_apply_of_le h, exp_two_pi_div_mul_I]
  ring

/-- Off the right disk, `b⁻¹` is the identity. -/
theorem genB_inv_apply_of_not_le (h : ¬‖z - 1‖ ≤ r) : (genB n r)⁻¹ z = z := by
  rw [genB, turn_inv]
  exact turn_apply_of_not_le h

/-- `a ∈ GG n r`. -/
theorem genA_mem_GG (n : ℕ) (r : ℝ) : genA n r ∈ GG n r :=
  Subgroup.subset_closure (by simp)

/-- `b ∈ GG n r`. -/
theorem genB_mem_GG (n : ℕ) (r : ℝ) : genB n r ∈ GG n r :=
  Subgroup.subset_closure (by simp)

/-! ### The invariance principle -/

/-- A set that is mapped into itself by each generator of a group of permutations and by its
inverse is mapped into itself by every element of the group. -/
theorem mapsTo_of_mem_closure {α : Type*} {s : Set (Equiv.Perm α)} {S : Set α}
    (hs : ∀ g ∈ s, MapsTo g S S ∧ MapsTo ⇑g⁻¹ S S) {g : Equiv.Perm α}
    (hg : g ∈ Subgroup.closure s) : MapsTo g S S := by
  suffices MapsTo g S S ∧ MapsTo ⇑g⁻¹ S S from this.1
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact hs g hg
  | one => exact ⟨mapsTo_id S, mapsTo_id S⟩
  | mul g h _ _ hg hh => exact ⟨hg.1.comp hh.1, by rw [mul_inv_rev]; exact hh.2.comp hg.2⟩
  | inv g _ hg => exact ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

/-- **Invariance principle.** A set of points that is mapped into itself by both generators and by
their inverses contains the orbit of each of its points. -/
theorem orbit_subset_of_mapsTo {S : Set ℂ} (hA : MapsTo (genA n r) S S)
    (hA' : MapsTo ⇑(genA n r)⁻¹ S S) (hB : MapsTo (genB n r) S S)
    (hB' : MapsTo ⇑(genB n r)⁻¹ S S) {p : ℂ} (hp : p ∈ S) :
    MulAction.orbit (GG n r) p ⊆ S := by
  rintro _ ⟨g, rfl⟩
  refine mapsTo_of_mem_closure (s := {genA n r, genB n r}) ?_ g.2 hp
  rintro _ (rfl | rfl)
  exacts [⟨hA, hA'⟩, ⟨hB, hB'⟩]

/-- A point off both disks is fixed by the whole group. -/
theorem orbit_eq_singleton {p : ℂ} (hA : ¬‖p + 1‖ ≤ r) (hB : ¬‖p - 1‖ ≤ r) :
    MulAction.orbit (GG n r) p = {p} := by
  refine (orbit_subset_of_mapsTo (S := {p}) ?_ ?_ ?_ ?_ rfl).antisymm
    (singleton_subset_iff.2 (MulAction.mem_orbit_self p))
  all_goals rintro _ rfl
  exacts [genA_apply_of_not_le hA, genA_inv_apply_of_not_le hA, genB_apply_of_not_le hB,
    genB_inv_apply_of_not_le hB]

end CriticalRadiusFive

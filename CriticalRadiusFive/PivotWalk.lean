/-
Copyright (c) 2026 The critical-radius-five authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The critical-radius-five authors
-/
import CriticalRadiusFive.Cyclotomic

/-!
# The pivot walk: an orbit invariant for `GG₅`

Fix a point `p` and a radius `r`. Every element of `GG 5 r` acts on `p` as an isometry
`z ↦ m z + τ` with `m` a fifth root of unity. Writing the preimage of `-1` under this isometry as
`-1 + 2ν`, the image of `p` is

`m (p + 1 - 2ν) - 1`,

and the *pivot* `ν` lies in the lattice `ℤ[ζ₅]`. The *dumbbell* of the state `(m, ν)` joins the
pivot `ν` to its *tip* `ν + m̄`: a letter `a^{±1}` acts only if `ν` lies in the *window*
`‖p + 1 - 2ν‖ ≤ r`, and then it keeps `ν` and turns `m`; a letter `b^{±1}` acts only if the tip
lies in the window, and then the tip becomes the new pivot's tip, `ν ↦ (ν + m̄) - m̄'`.

Hence the pivots and tips walk on the lattice by steps that are fifth roots of unity, turning only
about an end that lies in the window. Since `n = 5` is odd the walk is *typed*: it adds `m̄ ∈ μ₅`
going from a pivot to its tip and subtracts one going back. As every fifth root of unity is `≡ 1`
modulo the prime `1 - ζ`, pivots have class `0` and tips class `1` modulo `1 - ζ` (`Cyc.cls`).

`orbit_subset_reach` makes this precise: for any set `V` of lattice points that is closed under
typed steps inside the window (`EdgeClosed`), the orbit of `p` consists of points
`m (p + 1 - 2ν) - 1` whose pivot or tip lies in `V`. The lower bound then exhibits, for every
`r < √(3 + φ)`, such a set `V` of bounded size.
-/

noncomputable section

open Complex Set MulAction

namespace CriticalRadiusFive

open Cyc

variable (p : ℂ) (r : ℝ) (V : Set Cyc)

/-- The *window*: the lattice points `ν` for which the point `-1 + 2ν` is within `r` of `p`,
i.e. the pivots at which `a^{±1}` acts. -/
def Window (v : Cyc) : Prop := ‖p + 1 - 2 * toC v‖ ≤ r

/-- `V` is closed under the typed steps of the walk that stay inside the window: adding a fifth root
of unity to a point of class `0`, and subtracting one from a point of class `1`. -/
structure EdgeClosed : Prop where
  /-- From a pivot of `V`, a step `+e` inside the window stays in `V`. -/
  add_mem : ∀ v ∈ V, cls v % 5 = 0 → ∀ e ∈ units, Window p r (v + e) → v + e ∈ V
  /-- From a tip in `V`, a step `-e` inside the window stays in `V`. -/
  sub_mem : ∀ v ∈ V, cls v % 5 = 1 → ∀ e ∈ units, Window p r (v - e) → v - e ∈ V

/-- The invariant of a state `(m, ν) = (toC f, toC v)`: the pivot has class `0`, the pivot and the
tip `ν + m̄` belong to `V` whenever they are in the window, and at least one of them does. -/
structure Good (f v : Cyc) : Prop where
  /-- The rotation part `m` is a fifth root of unity. -/
  unit : f ∈ units
  /-- The pivot has class `0`. -/
  cls_pivot : cls v % 5 = 0
  /-- The pivot belongs to `V` when it lies in the window. -/
  pivot_mem : Window p r v → v ∈ V
  /-- The tip belongs to `V` when it lies in the window. -/
  tip_mem : Window p r (v + bar f) → v + bar f ∈ V
  /-- The pivot or the tip belongs to `V`. -/
  mem : v ∈ V ∨ v + bar f ∈ V

/-- The points `m (p + 1 - 2ν) - 1` represented by good states. -/
def reach : Set ℂ := {x | ∃ f v, Good p r V f v ∧ x = toC f * (p + 1 - 2 * toC v) - 1}

variable {p r V}

/-- The point of a good state lies in `reach p r V`. -/
theorem mem_reach {f v : Cyc} (h : Good p r V f v) :
    toC f * (p + 1 - 2 * toC v) - 1 ∈ reach p r V :=
  ⟨f, v, h, rfl⟩

/-- A letter turning the left disk by `κ ∈ {ζ, ζ⁻¹}` keeps the pivot and turns the state. -/
theorem mapsTo_reach_left (hV : EdgeClosed p r V) {g : Equiv.Perm ℂ} {κ : ℂ} {ρ : Cyc → Cyc}
    (hρ : ∀ f ∈ units, ρ f ∈ units) (hρκ : ∀ f, toC (ρ f) = κ * toC f)
    (hg : ∀ x, ‖x + 1‖ ≤ r → g x = κ * (x + 1) - 1) (hg' : ∀ x, ¬‖x + 1‖ ≤ r → g x = x) :
    MapsTo g (reach p r V) (reach p r V) := by
  rintro _ ⟨f, v, hfv, rfl⟩
  have hnorm : ‖toC f * (p + 1 - 2 * toC v) - 1 + 1‖ = ‖p + 1 - 2 * toC v‖ := by
    rw [sub_add_cancel, norm_mul, norm_toC_of_mem_units hfv.unit, one_mul]
  by_cases h : ‖toC f * (p + 1 - 2 * toC v) - 1 + 1‖ ≤ r
  · have hv : v ∈ V := hfv.pivot_mem (by rw [Window, ← hnorm]; exact h)
    rw [hg _ h, sub_add_cancel, ← mul_assoc, ← hρκ]
    refine mem_reach ⟨hρ f hfv.unit, hfv.cls_pivot, fun _ ↦ hv, fun hw ↦ ?_, .inl hv⟩
    exact hV.add_mem v hv hfv.cls_pivot _ (bar_mem_units _ (hρ f hfv.unit)) hw
  · rw [hg' _ h]
    exact mem_reach hfv

/-- A letter turning the right disk by `κ ∈ {ζ, ζ⁻¹}` moves the pivot through the tip. -/
theorem mapsTo_reach_right (hV : EdgeClosed p r V) {g : Equiv.Perm ℂ} {κ : ℂ} {ρ : Cyc → Cyc}
    (hρ : ∀ f ∈ units, ρ f ∈ units) (hρκ : ∀ f, toC (ρ f) = κ * toC f)
    (hg : ∀ x, ‖x - 1‖ ≤ r → g x = κ * (x - 1) + 1) (hg' : ∀ x, ¬‖x - 1‖ ≤ r → g x = x) :
    MapsTo g (reach p r V) (reach p r V) := by
  rintro _ ⟨f, v, hfv, rfl⟩
  -- Seen from the right disk, the state is `m (p + 1 - 2 (ν + m̄)) + 1`.
  have hmm := toC_mul_toC_bar_of_mem_units hfv.unit
  have hx : toC f * (p + 1 - 2 * toC v) - 1 - 1 = toC f * (p + 1 - 2 * toC (v + bar f)) := by
    rw [toC_add]
    linear_combination (2 : ℂ) * hmm
  have hnorm : ‖toC f * (p + 1 - 2 * toC v) - 1 - 1‖ = ‖p + 1 - 2 * toC (v + bar f)‖ := by
    rw [hx, norm_mul, norm_toC_of_mem_units hfv.unit, one_mul]
  by_cases h : ‖toC f * (p + 1 - 2 * toC v) - 1 - 1‖ ≤ r
  · -- The tip `t = ν + m̄` is in the window, hence in `V`, and has class `1`.
    set t := v + bar f
    have ht : t ∈ V := hfv.tip_mem (by rw [Window, ← hnorm]; exact h)
    have hct : cls t % 5 = 1 := by
      have := cls_of_mem_units _ (bar_mem_units _ hfv.unit)
      have := hfv.cls_pivot
      rw [cls_add]
      omega
    -- The new state is `(ρ f, t - conj (ρ f))`: its tip is `t`.
    have hf' := hρ f hfv.unit
    have hback : t - bar (ρ f) + bar (ρ f) = t := sub_add_cancel _ _
    have hmm' := toC_mul_toC_bar_of_mem_units hf'
    rw [hρκ] at hmm'
    have key : κ * (toC f * (p + 1 - 2 * toC t)) + 1 =
        toC (ρ f) * (p + 1 - 2 * toC (t - bar (ρ f))) - 1 := by
      rw [toC_sub, hρκ]
      linear_combination (-2 : ℂ) * hmm'
    rw [hg _ h, hx, key]
    refine mem_reach ⟨hf', ?_, fun hw ↦ hV.sub_mem t ht hct _ (bar_mem_units _ hf') hw,
      fun _ ↦ by rw [hback]; exact ht, .inr (by rw [hback]; exact ht)⟩
    have := cls_of_mem_units _ (bar_mem_units _ hf')
    rw [cls_sub]
    omega
  · rw [hg' _ h]
    exact mem_reach hfv

/-- **The orbit invariant.** If `V` is closed under the typed steps inside the window and the
initial state (pivot `0`, tip `1`) is good, then every point of the orbit of `p` has the form
`m (p + 1 - 2ν) - 1` with `m ∈ μ₅` and the pivot `ν` or its tip `ν + m̄` in `V`. -/
theorem orbit_subset_reach (hV : EdgeClosed p r V) (h₀ : Good p r V (1, 0, 0, 0) 0) :
    orbit (GG 5 r) p ⊆ reach p r V := by
  refine orbit_subset_of_mapsTo ?_ ?_ ?_ ?_ ⟨_, _, h₀, by simp⟩
  · exact mapsTo_reach_left hV mulZetaInv_mem_units toC_mulZetaInv
      (fun _ ↦ genA_apply_of_le) (fun _ ↦ genA_apply_of_not_le)
  · exact mapsTo_reach_left hV mulZeta_mem_units toC_mulZeta
      (fun _ ↦ genA_inv_apply_of_le) (fun _ ↦ genA_inv_apply_of_not_le)
  · exact mapsTo_reach_right hV mulZetaInv_mem_units toC_mulZetaInv
      (fun _ ↦ genB_apply_of_le) (fun _ ↦ genB_apply_of_not_le)
  · exact mapsTo_reach_right hV mulZeta_mem_units toC_mulZeta
      (fun _ ↦ genB_inv_apply_of_le) (fun _ ↦ genB_inv_apply_of_not_le)

end CriticalRadiusFive

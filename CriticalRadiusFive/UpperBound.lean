/-
Copyright (c) 2026 The critical-radius-five authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The critical-radius-five authors
-/
import CriticalRadiusFive.CircleRotation
import CriticalRadiusFive.Cyclotomic
import CriticalRadiusFive.Finiteness
import CriticalRadiusFive.Words

/-!
# The upper bound: `GG₅` is infinite at `r = √(3 + φ)`

This is Theorem 2 of Hearn–Kretschmer–Rokicki–Streeter–Vergo. Let `ζ = exp(2πi/5)` and
`E = ζ - ζ²`, so that `‖E + 1‖ = √(3 + φ)`: at the critical radius the chord `E'E` from `-E` to
`E`, which passes through the origin, fits exactly in the lens where the two disks overlap. Put
`F = E / φ = 1 - ζ + ζ² - ζ³` and `G' = E - 2F`, and parametrise the chord as `s • E`,
`-1 ≤ s ≤ 1`. Three words of the group act on it as translations:

* `a⁻¹a⁻¹b⁻¹a⁻¹b⁻¹` carries `[E', F']` (`-1 ≤ s ≤ 1 - φ`) by `2F`;
* `abab²` carries `[F', G']` (`1 - φ ≤ s ≤ 3 - 2φ`) by `2F`;
* `abab⁻¹a⁻¹b⁻¹` carries `[G', E]` (`3 - 2φ ≤ s ≤ 1`) by `2F - 2E`.

On the parameter, this is the rotation `s ↦ s + 2/φ` of the circle `[-1, 1)` of length `2`: a
three-piece interval exchange whose rotation number `1/φ` is irrational. Hence the orbit of the
origin is infinite, and so is the group.

Each piece is checked exactly: its two endpoints are points of `ℤ[ζ₅]`, and a word is admissible
at such a point when a finite list of disk-membership tests holds; each test is an inequality
`N + M φ ≤ 3 + φ` between elements of `ℤ[φ]`, decided by integer arithmetic (`admissibleZ`,
evaluated by `decide`). Convexity of the disks extends admissibility to the whole piece.
-/

noncomputable section

open Complex Set MulAction
open scoped goldenRatio

namespace CriticalRadiusFive

local notation "ζ" => zeta 5

open Cyc

/-! ### Letters on the lattice -/

namespace Letter

/-- The centre of a letter's disk, as a lattice point. -/
def centerZ : Letter → Cyc
  | a | A => (-1, 0, 0, 0)
  | b | B => (1, 0, 0, 0)

/-- The rotation of a letter, on the lattice. -/
def rotZ : Letter → Cyc → Cyc
  | a | b => mulZetaInv
  | A | B => mulZeta

/-- The formal action of a letter (for `n = 5`) on the lattice. -/
def actZ (l : Letter) (v : Cyc) : Cyc := l.centerZ + l.rotZ (v - l.centerZ)

theorem toC_centerZ (l : Letter) : toC l.centerZ = l.center := by
  cases l <;> simp [centerZ, center, toC]

theorem toC_actZ (l : Letter) (v : Cyc) : toC (l.actZ v) = l.act 5 (toC v) := by
  have h : toC (l.rotZ (v - l.centerZ)) = l.rot 5 * (toC v - l.center) := by
    cases l <;> simp [rotZ, rot, toC_mulZeta, toC_mulZetaInv, toC_sub, toC_centerZ]
  rw [actZ, toC_add, h, toC_centerZ, act]

end Letter

/-! ### Exact admissibility tests -/

/-- The integer test for `‖toC u‖ ≤ √(3 + φ)`, i.e. `(N - 3) + (M - 1) φ ≤ 0` for the norm form
`‖toC u‖² = N + M φ`. -/
def inDisk (u : Cyc) : Bool := goldenNonpos (normRat u - 3) (normGold u - 1)

theorem norm_toC_le_of_inDisk {u : Cyc} (h : inDisk u = true) : ‖toC u‖ ≤ √(3 + φ) := by
  have h₁ := add_mul_goldenRatio_nonpos h
  have h₂ := norm_toC_sq u
  push_cast at h₁
  rw [Real.le_sqrt (norm_nonneg _) (by linarith [Real.goldenRatio_pos])]
  linarith

/-- The exact admissibility test for a word at a lattice point, at the radius `√(3 + φ)`. -/
def admissibleZ : List Letter → Cyc → Bool
  | [], _ => true
  | l :: w, v => inDisk (v - l.centerZ) && admissibleZ w (l.actZ v)

theorem admissible_of_admissibleZ :
    ∀ {w : List Letter} {v : Cyc}, admissibleZ w v = true → Admissible 5 √(3 + φ) w (toC v)
  | [], _, _ => trivial
  | l :: w, v, h => by
    rw [admissibleZ, Bool.and_eq_true] at h
    refine ⟨?_, ?_⟩
    · rw [← l.toC_centerZ, ← toC_sub]
      exact norm_toC_le_of_inDisk h.1
    · rw [← l.toC_actZ]
      exact admissible_of_admissibleZ h.2

/-- The formal action of a word on the lattice. -/
def formalActZ : List Letter → Cyc → Cyc
  | [], v => v
  | l :: w, v => formalActZ w (l.actZ v)

theorem toC_formalActZ : ∀ (w : List Letter) (v : Cyc),
    toC (formalActZ w v) = formalAct 5 w (toC v)
  | [], _ => rfl
  | l :: w, v => by rw [formalActZ, toC_formalActZ w, l.toC_actZ, formalAct]

/-! ### The chord `E'E` -/

/-- `E = ζ - ζ²`. The chord `E'E` from `-E` to `E` passes through the origin. -/
def chordE : ℂ := toC (0, 1, -1, 0)

/-- The points of the chord with parameter in `ℤ[φ]` are lattice points:
`(x + y φ) • E = y + x ζ - x ζ² - y ζ³`. -/
theorem smul_chordE (x y : ℤ) : ((x + y * φ : ℝ)) • chordE = toC (y, x, -x, -y) := by
  have hφ := zeta_five_add_pow_four
  rw [real_smul, ofReal_add, ofReal_mul, ofReal_intCast, ofReal_intCast]
  generalize (φ : ℂ) = Φ at hφ ⊢
  simp only [chordE, toC]
  push_cast
  linear_combination (-(y : ℂ) * (ζ ^ 2 - 2 * ζ + 1)) * cyclotomic_zeta_five +
    (-(y : ℂ) * (ζ - ζ ^ 2)) * hφ

theorem chordE_ne_zero : chordE ≠ 0 := by
  intro h
  have := norm_toC_sq (0, 1, -1, 0)
  rw [← chordE, h, norm_zero] at this
  simp only [normRat, normGold] at this
  norm_num at this
  linarith [Real.goldenRatio_lt_two]

/-- A point between two multiples of a vector lies on the segment joining them. -/
theorem smul_mem_segment {s₁ s₂ s : ℝ} (h₁ : s₁ ≤ s) (h₂ : s ≤ s₂) (z : ℂ) :
    s • z ∈ segment ℝ (s₁ • z) (s₂ • z) := by
  rcases h₁.eq_or_lt with rfl | h₁
  · exact left_mem_segment _ _ _
  have hne : s₂ - s₁ ≠ 0 := by linarith
  refine ⟨(s₂ - s) / (s₂ - s₁), (s - s₁) / (s₂ - s₁), by apply div_nonneg <;> linarith,
    by apply div_nonneg <;> linarith, by field_simp; ring, ?_⟩
  rw [smul_smul, smul_smul, ← add_smul]
  congr 1
  field_simp
  ring

/-! ### The three pieces -/

/-- A word which is admissible at the lattice points `(x₁ + y₁ φ) • E` and `(x₂ + y₂ φ) • E`, and
whose rotation factors multiply to `1`, translates the chord between them by `toC τ`. -/
theorem wordPerm_smul_chordE {w : List Letter} {x₁ y₁ x₂ y₂ : ℤ} {s : ℝ}
    (hP : admissibleZ w (y₁, x₁, -x₁, -y₁) = true) (hQ : admissibleZ w (y₂, x₂, -x₂, -y₂) = true)
    (hw : (w.map (Letter.rot 5)).prod = 1) (h₁ : x₁ + y₁ * φ ≤ s) (h₂ : s ≤ x₂ + y₂ * φ) :
    wordPerm 5 √(3 + φ) w (s • chordE) = s • chordE + toC (formalActZ w 0) := by
  have hs := smul_mem_segment h₁ h₂ chordE
  rw [smul_chordE, smul_chordE] at hs
  rw [wordPerm_apply_of_admissible_of_prod_eq_one (admissible_of_mem_segment
    (admissible_of_admissibleZ hP) (admissible_of_admissibleZ hQ) hs) hw, toC_formalActZ,
    toC_zero]

theorem rot_prod_one₁ : ([.A, .A, .B, .A, .B].map (Letter.rot 5)).prod = 1 := by
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Letter.rot]
  linear_combination zeta_five_pow_five

theorem rot_prod_one₂ : ([.a, .b, .a, .b, .b].map (Letter.rot 5)).prod = 1 := by
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Letter.rot,
    zeta_five_inv]
  linear_combination (ζ ^ 15 + ζ ^ 10 + ζ ^ 5 + 1) * zeta_five_pow_five

theorem rot_prod_one₃ : ([.a, .b, .a, .B, .A, .B].map (Letter.rot 5)).prod = 1 := by
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Letter.rot,
    zeta_five_inv]
  linear_combination (ζ ^ 10 + ζ ^ 5 + 1) * zeta_five_pow_five

/-- A word which is admissible at the endpoints of a piece `[(x₁ + y₁ φ) E, (x₂ + y₂ φ) E]` of
the chord, and whose rotation factors multiply to `1`, translates the piece along the chord by
`(x + y φ) E`, where `(y, x, -x, -y)` is its formal action on `0`. -/
theorem wordPerm_smul_chordE_eq {w : List Letter} {x₁ y₁ x₂ y₂ x y : ℤ} {s : ℝ}
    (hP : admissibleZ w (y₁, x₁, -x₁, -y₁) = true) (hQ : admissibleZ w (y₂, x₂, -x₂, -y₂) = true)
    (hw : (w.map (Letter.rot 5)).prod = 1) (hτ : formalActZ w 0 = (y, x, -x, -y))
    (h₁ : x₁ + y₁ * φ ≤ s) (h₂ : s ≤ x₂ + y₂ * φ) :
    wordPerm 5 √(3 + φ) w (s • chordE) = (s + (x + y * φ)) • chordE := by
  rw [wordPerm_smul_chordE hP hQ hw h₁ h₂, hτ, ← smul_chordE, ← add_smul]

/-- **Piece 1.** `a⁻¹a⁻¹b⁻¹a⁻¹b⁻¹` translates `[E', F'] = [-E, (1 - φ) E]` by `2F = (2φ - 2) E`. -/
theorem piece₁ {s : ℝ} (h₁ : -1 ≤ s) (h₂ : s ≤ 1 - φ) :
    wordPerm 5 √(3 + φ) [.A, .A, .B, .A, .B] (s • chordE) = (s + (2 * φ - 2)) • chordE := by
  have := wordPerm_smul_chordE_eq (x₁ := -1) (y₁ := 0) (x₂ := 1) (y₂ := -1) (x := -2) (y := 2)
    (by decide) (by decide) rot_prod_one₁ (by decide) (by push_cast; linarith)
    (by push_cast; linarith) (s := s)
  push_cast at this
  rw [this]
  ring_nf

/-- **Piece 2.** `abab²` translates `[F', G'] = [(1 - φ) E, (3 - 2φ) E]` by `2F = (2φ - 2) E`. -/
theorem piece₂ {s : ℝ} (h₁ : 1 - φ ≤ s) (h₂ : s ≤ 3 - 2 * φ) :
    wordPerm 5 √(3 + φ) [.a, .b, .a, .b, .b] (s • chordE) = (s + (2 * φ - 2)) • chordE := by
  have := wordPerm_smul_chordE_eq (x₁ := 1) (y₁ := -1) (x₂ := 3) (y₂ := -2) (x := -2) (y := 2)
    (by decide) (by decide) rot_prod_one₂ (by decide) (by push_cast; linarith)
    (by push_cast; linarith) (s := s)
  push_cast at this
  rw [this]
  ring_nf

/-- **Piece 3.** `abab⁻¹a⁻¹b⁻¹` translates `[G', E] = [(3 - 2φ) E, E]` by
`2F - 2E = (2φ - 4) E`. -/
theorem piece₃ {s : ℝ} (h₁ : 3 - 2 * φ ≤ s) (h₂ : s ≤ 1) :
    wordPerm 5 √(3 + φ) [.a, .b, .a, .B, .A, .B] (s • chordE) =
      (s + (2 * φ - 2) - 2) • chordE := by
  have := wordPerm_smul_chordE_eq (x₁ := 3) (y₁ := -2) (x₂ := 1) (y₂ := 0) (x := -4) (y := 2)
    (by decide) (by decide) rot_prod_one₃ (by decide) (by push_cast; linarith)
    (by push_cast; linarith) (s := s)
  push_cast at this
  rw [this]
  ring_nf

/-! ### The golden rotation of the chord -/

/-- The rotation of the chord by `2/φ = 2φ - 2`: the parameter `s ∈ [-1, 1)` of the point `s • E`
moves to `s + 2/φ`, reduced modulo `2` into `[-1, 1)`. -/
def chordRot (s : ℝ) : ℝ := if s < 3 - 2 * φ then s + (2 * φ - 2) else s + (2 * φ - 2) - 2

/-- The three words realise the rotation of the chord. -/
theorem exists_mem_GG_apply_smul_chordE {s : ℝ} (hs : s ∈ Ico (-1 : ℝ) 1) :
    ∃ g ∈ GG 5 √(3 + φ), g (s • chordE) = chordRot s • chordE := by
  obtain ⟨h₁, h₂⟩ := hs
  unfold chordRot
  split_ifs with h
  · rcases le_total s (1 - φ) with h' | h'
    · exact ⟨_, wordPerm_mem_GG _ _ _, piece₁ h₁ h'⟩
    · exact ⟨_, wordPerm_mem_GG _ _ _, piece₂ h' h.le⟩
  · exact ⟨_, wordPerm_mem_GG _ _ _, piece₃ (not_lt.1 h) h₂.le⟩

theorem chordRot_mapsTo : MapsTo chordRot (Ico (-1 : ℝ) 1) (Ico (-1 : ℝ) 1) := by
  rintro s ⟨h₁, h₂⟩
  have := goldenRatio_gt
  have := goldenRatio_lt
  unfold chordRot
  split_ifs with h <;> constructor <;> linarith

/-- **Theorem 2, orbit form.** At `r = √(3 + φ)` the origin has an infinite orbit. -/
theorem orbit_zero_infinite : (orbit (GG 5 √(3 + φ)) (0 : ℂ)).Infinite := by
  have hα : Irrational ((2 * φ - 2) / 2) := by
    rw [show (2 * φ - 2) / 2 = φ - (1 : ℤ) by push_cast; ring]
    exact Real.goldenRatio_irrational.sub_intCast 1
  have hT (s : ℝ) : ∃ m : ℤ, chordRot s = s + (2 * φ - 2) + m * 2 := by
    unfold chordRot
    split_ifs
    exacts [⟨0, by simp⟩, ⟨-1, by push_cast; ring⟩]
  have hx : InjOn (fun s : ℝ => s • chordE) (Ico (-1) 1) :=
    (smul_left_injective ℝ chordE_ne_zero).injOn
  simpa using orbit_infinite_of_irrational_rotation hα hT chordRot_mapsTo hx
    (fun s hs => exists_mem_GG_apply_smul_chordE hs) (t₀ := 0) (by norm_num)

/-- **Theorem 2** (Hearn–Kretschmer–Rokicki–Streeter–Vergo). `GG₅` is infinite at
`r = √(3 + φ)`. -/
theorem infinite_GG_five : Infinite (GG 5 √(3 + φ)) :=
  infinite_of_orbit_infinite orbit_zero_infinite

end CriticalRadiusFive

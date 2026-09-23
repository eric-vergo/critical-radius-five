/-
Copyright (c) 2026 The critical-radius-five authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The critical-radius-five authors
-/
import CriticalRadiusFive

/-!
# The critical radius of the two-disk group `GG₅`: the solution

The two theorems of `Challenge.lean`, stated identically and proved by the library
`CriticalRadiusFive`. The library's definitions carry the same names as the Challenge's and are
the same text (`CriticalRadiusFive/Defs.lean`); the comparator checks that they elaborate to the
same kernel terms, that the statements below coincide with the Challenge's, and that the proofs use
only the axioms `propext`, `Classical.choice` and `Quot.sound`.
-/

open CriticalRadiusFive
open scoped goldenRatio

/-- **`GG₅(r)` is finite exactly below `√(3 + φ)`.** -/
theorem finite_GG_five_iff (r : ℝ) : Finite (GG 5 r) ↔ r < √(3 + φ) :=
  CriticalRadiusFive.finite_GG_five_iff r

/-- **The critical radius of `GG₅` is `√(3 + φ)`.** -/
theorem criticalRadius_five : criticalRadius 5 = √(3 + φ) :=
  CriticalRadiusFive.criticalRadius_five

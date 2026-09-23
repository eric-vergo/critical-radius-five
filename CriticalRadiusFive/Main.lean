/-
Copyright (c) 2026 The critical-radius-five authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The critical-radius-five authors
-/
import CriticalRadiusFive.LowerBound
import CriticalRadiusFive.UpperBound

/-!
# The critical radius of `GG₅`

**Main theorem.** The two-disk compound symmetry group `GG₅(r)` is finite if and only if
`r < √(3 + φ)`; in particular its critical radius is

`r_c(5) = √(3 + φ) = 2.1489611417…`,

a root of `x⁴ - 7x² + 11`. This is the value found numerically, and conjectured, by Hearn,
Kretschmer, Rokicki, Streeter and Vergo, who proved that `GG₅` is infinite at `√(3 + φ)`.

* `infinite_GG_five` (`UpperBound.lean`): at `r = √(3 + φ)` three words act on the chord `E'E` as a
  rotation with irrational rotation number `1/φ`, so the group is infinite.
* `finite_GG_five_of_lt` (`LowerBound.lean`): below `√(3 + φ)` every orbit is trapped by the cut
  levels of a lattice functional, in a finite set whose size depends on `r` only, so the group is
  finite.
* `finite_GG_iff_of_forall_lt`, `criticalRadius_eq_of_forall_lt` (`Finiteness.lean`) turn the two
  halves into the statements below.

The statements are repeated verbatim in `Challenge.lean`, which depends on Mathlib only.
-/

open scoped goldenRatio

namespace CriticalRadiusFive

/-- **`GG₅(r)` is finite exactly below `√(3 + φ)`.** -/
theorem finite_GG_five_iff (r : ℝ) : Finite (GG 5 r) ↔ r < √(3 + φ) :=
  finite_GG_iff_of_forall_lt (fun _ ↦ finite_GG_five_of_lt) infinite_GG_five r

/-- **The critical radius of `GG₅` is `√(3 + φ)`.** -/
theorem criticalRadius_five : criticalRadius 5 = √(3 + φ) :=
  criticalRadius_eq_of_forall_lt (fun _ ↦ finite_GG_five_of_lt) infinite_GG_five

end CriticalRadiusFive

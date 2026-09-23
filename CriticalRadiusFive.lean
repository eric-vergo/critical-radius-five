/-
Copyright (c) 2026 The critical-radius-five authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The critical-radius-five authors
-/
import CriticalRadiusFive.Basic
import CriticalRadiusFive.CircleRotation
import CriticalRadiusFive.Cyclotomic
import CriticalRadiusFive.Defs
import CriticalRadiusFive.Finiteness
import CriticalRadiusFive.Lens
import CriticalRadiusFive.LowerBound
import CriticalRadiusFive.Main
import CriticalRadiusFive.PivotWalk
import CriticalRadiusFive.UpperBound
import CriticalRadiusFive.Words

/-!
# The critical radius of the two-disk group `GG₅`

The two-disk group `GG₅(r)` is finite exactly when `r < √(3 + φ)`, so its critical radius is
`√(3 + φ)` (`CriticalRadiusFive.finite_GG_five_iff`, `CriticalRadiusFive.criticalRadius_five` in
`CriticalRadiusFive.Main`). The definitions are in `CriticalRadiusFive.Defs`.
-/

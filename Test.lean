/-
Copyright (c) 2026 The critical-radius-five authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The critical-radius-five authors
-/
import Solution

/-!
# Axiom audit

Building this module fails unless the two advertised theorems exist and depend on exactly the three
standard axioms of Lean and Mathlib. It audits the library's theorems and their restatements in
`Solution.lean`; the comparator performs the same check, independently, on a kernel replay.
-/

/-- info: 'criticalRadius_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms criticalRadius_five

/-- info: 'finite_GG_five_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finite_GG_five_iff

/--
info: 'CriticalRadiusFive.criticalRadius_five' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CriticalRadiusFive.criticalRadius_five

/--
info: 'CriticalRadiusFive.finite_GG_five_iff' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CriticalRadiusFive.finite_GG_five_iff

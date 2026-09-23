import Lake
open Lake DSL

/-
The blueprint is its own Lake package, next to the Lean library in the parent
directory. It needs three things:

* `VersoBlueprint`, which renders the blueprint site;
* the library `CriticalRadiusFive` itself, so that `(lean := "…")` references in
  the chapters resolve to the actual declarations;
* `mathlib`, required last so that Mathlib's pinned dependency versions
  (ProofWidgets, Plausible, …) take precedence over the ones VersoBlueprint asks
  for. That keeps the Mathlib build cache (`lake exe cache get`) applicable.
  Keep this revision equal to the one in `../lakefile.toml`.
-/
require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint"@"v4.34.0"
require CriticalRadiusFive from ".."
require mathlib from git "https://github.com/leanprover-community/mathlib4"@"5ed2965256430c3649e86755f9576b54eca72435"

package CriticalRadiusFiveBlueprint where
  precompileModules := false
  leanOptions := #[
    ⟨`experimental.module, true⟩,
    -- A `(lean := "…")` name that does not resolve is an error, not a warning.
    ⟨`weak.verso.blueprint.externalCode.strictResolve, true⟩
  ]

@[default_target]
lean_lib CriticalRadiusFiveBlueprint where

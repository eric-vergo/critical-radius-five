# Blueprint

A [Verso blueprint](https://github.com/leanprover/verso-blueprint) for the proof that the critical
radius of the two-disk group GG₅ is r_c(5) = √(3 + φ). It is a separate Lake package that depends on
the Lean library in the parent directory, so every blueprint node links to the declaration that
proves it.

The published site has four chapters (the setup, the upper bound, the lower bound, the theorem), an
interactive dependency graph and a progress summary.

## Build and serve locally

From this directory:

```bash
lake exe cache get          # Mathlib from the build cache; never compile Mathlib from source
lake exe vbp build          # writes the site to _out/site/html-multi/
lake exe vbp build --serve  # build, then serve the site (the URL is printed; default port 8000)
```

`lake exe vbp build --serve --port 8765` serves on a fixed port. `./scripts/ci-pages.sh` is the
build-and-check step that the GitHub workflow runs. The first build compiles Verso, VersoBlueprint
and the library itself, which takes a few minutes; later builds are incremental.

The generated data can be queried after a build, for example

```bash
lake exe vbp query labels            # all nodes
lake exe vbp query uses thm:main     # what a node depends on
lake exe vbp query used-by thm:T1    # what depends on a node
```

The machine-readable node and edge data is in
`_out/site/html-multi/-verso-data/blueprint-manifest.json`; the poster in `../poster/` is drawn from it.

## Layout

```text
blueprint/
  lakefile.lean                 package definition (VersoBlueprint, the library, Mathlib)
  lean-toolchain                leanprover/lean4:v4.34.0, the same as the library
  lake-manifest.json            pinned dependency revisions
  CriticalRadiusFiveBlueprint.lean
  CriticalRadiusFiveBlueprint/
    Blueprint.lean              top level: title, introduction, chapters, graph, summary
    Chapters/
      Setup.lean                the turns, the group, the critical radius, monotonicity, bounded orbits
      UpperBound.lean           the chord E′E, three words, an irrational rotation
      LowerBound.lean           the pivot walk, levels, the lens bound, cut levels, confinement
      MainTheorem.lean          r_c(5) = √(3 + φ)
  CriticalRadiusFiveBlueprintMain.lean   the site generator that `vbp build` runs
  scripts/ci-pages.sh           build the site and check its outputs
```

Each statement is a `:::definition`, `:::lemma_`, or `:::theorem` block with a label such as
`thm:upper`, its Lean declarations in `(lean := "…")`, and its dependencies as `{uses "…"}[]`
references (in the statement or in the `:::proof` block). The chapters import the library, and the
package sets `verso.blueprint.externalCode.strictResolve`: a `(lean := "…")` name that does not exist
in the library is a build error, so renaming a declaration means updating the blueprint.

## Dependencies

`lakefile.lean` requires VersoBlueprint (branch `v4.34.0`), the library (`require CriticalRadiusFive
from ".."`), and Mathlib at the same revision as `../lakefile.toml`. Mathlib is required last, so
that its pinned versions of shared dependencies (ProofWidgets, Plausible) take precedence over the
ones VersoBlueprint asks for, and the Mathlib build cache applies. When the Mathlib revision of the
library changes, change it here too and run `lake update`.

The `v4.34.0` branch of VersoBlueprint is set up for `v4.34.0-rc2`; it builds unchanged with the final
`v4.34.0` toolchain used here.

## Publishing

`.github/workflows/blueprint.yml` (at the repository root) builds the site on every push and pull
request and deploys it to GitHub Pages from `main`. Pages has to be enabled once in the repository
settings, with GitHub Actions as the source.

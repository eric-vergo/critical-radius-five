# Poster

`proof-graph.pdf` and `proof-graph.svg` show the dependency graph of the proof that
r_c(5) = √(3 + φ) on one landscape A1 page (841 × 594 mm), drawn from the blueprint in `../blueprint/`.

* Each box is a blueprint node: its kind and number, its label (small, top right), a short title, and
  the Lean declarations that prove it (monospace, without the `CriticalRadiusFive.` namespace).
* Colours mark the parts of the proof: grey for the setup and general facts, blue for the upper bound,
  orange for the lower bound, dark for the main theorem. Definitions have square corners, theorems a
  heavier border.
* An arrow A → B means that B uses A.

## Regenerate

From the repository root:

```bash
(cd blueprint && lake exe vbp build)   # refresh the blueprint manifest the poster is drawn from
python3 poster/make_poster.py          # writes poster/proof-graph.{dot,svg,pdf}
```

The nodes, edges, numbers and Lean names come from the manifest that `vbp build` writes
(`blueprint/_out/site/html-multi/-verso-data/blueprint-manifest.json`); the short titles are the
bold phrases that open each statement in `blueprint/CriticalRadiusFiveBlueprint/Chapters/*.lean`.
`python3 poster/make_poster.py --from-source` reads everything from the chapter files instead, without
a blueprint build. The script reports any difference between the two sources, and any Lean name
that the blueprint build could not find.

Requirements: Python 3.8 or later (standard library only), Graphviz (`dot`), librsvg (`rsvg-convert`),
and the fonts Avenir Next, Menlo and STIX Two Text, which come with macOS; other systems substitute
similar fonts. `proof-graph.dot` is the Graphviz input, kept for reference.

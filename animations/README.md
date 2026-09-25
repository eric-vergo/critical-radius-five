# Animations

Manim scenes that illustrate the proof that the two-disk group `GG₅(r)` is finite exactly for
`r < √(3+φ)`. Every scene draws the two full disks (radius `r` about `−1` and `+1`). All geometry is
computed from the exact definitions — `ζ = e^{2πi/5}`, `E = ζ − ζ²`, `F = E/φ`, `G = 2F − E`, the
three words of the upper bound, the lattice `ℤ[ζ]` with integer coordinates, the level function —
and floating point is used only to draw. The orbits shown are computed by brute force (a
breadth-first search over the four turns, or equivalently over the states of the pivot walk);
they illustrate the theorems and prove nothing.

| file | scene | length | what it shows |
|---|---|---|---|
| `a1_setting` | `A1Setting` | 85 s | The two disks at `r = √(3+φ)`, the turns `a` and `b` (72° clockwise), the lens, the chord `E′E` from rim to rim (`\|E+1\| = r`), and its three pieces `I₁ = [E′,F′]`, `I₂ = [F′,G′]`, `I₃ = [G′,E]`. |
| `a2_word1` | `A2WordOne` | 54 s | The word `a⁻¹a⁻¹b⁻¹a⁻¹b⁻¹` applied turn by turn: the disk that turns rotates its contents; the piece `I₁` travels through the lens and lands on `[G,F]`, a translation by `2F`. Red rings mark endpoints lying exactly on the rim of the disk about to turn. |
| `a3_word2` | `A3WordTwo` | 54 s | The same for `abab²`: `I₂ → [F,E]`, a translation by `2F`. |
| `a4_word3` | `A4WordThree` | 64 s | The same for `abab⁻¹a⁻¹b⁻¹`: `I₃ → [E′,G]`, a translation by `2F − 2E`. |
| `a5_exchange` | `A5Exchange` | 86 s | The three translations together exchange the pieces (`I₁I₂I₃ → I₃I₁I₂`, lengths `\|I₁ ∪ I₂\| : \|I₃\| = 1 : φ`); gluing `E′` to `E` makes this the rotation by `1/φ` of a turn. The orbit of the origin is iterated 300 times and never closes. |
| `b1_lattice` | `B1Lattice` | 97 s | The point's-eye view at `r = 2`: keep the point still and let the pair of disks move. The disk centres sit at lattice points `2ν − 1` and `2(ν + m̄) − 1`, `ν ∈ ℤ[ζ]`; a turn about a centre needs the point within `r` of it (the window). All 143 positions of one orbit, and the same centres under the conjugation `ζ ↦ ζ²` (a bounded cloud). |
| `b2_levels` | `B2Levels` | 140 s | The level `ℓ = −A − 3B` of `ψ = 2⟨u,·⟩ = A + Bφ`, `u = 1 − ζ + ζ²`: rows of teeth `−5q + δℤ` (`δ = 3 − φ`, shifted by `δ/φ` per row), the strip of width `2L(r)` given by the lens, the cut levels where no tooth enters the strip, and the orbit's lattice points trapped between them. |
| `b3_threshold` | `B3Threshold` | 77 s | `r` grows through `√(3+φ)`: the strip widens until it is exactly one period wide, the cut levels disappear one by one, and at the same moment the chord `E′E` fits the lens (`E`, `E′` reach the rims). |
| `b4_monotone` | `B4Monotone` | 85 s | Monotonicity: the orbit of `0` at `r = 1, 1.9, 2, 2.05, 2.1, 2.13` (9, 9, 71, 151, 801, 2 543 points). Points are only ever added; at `√(3+φ)` the orbit is infinite. |

## Outputs

* `renders/mp4/*.mp4` — 1920×1080, 60 fps (dark theme).
* `renders/gif/*.gif` — previews, 1280 px wide, 12 fps (10 fps for any GIF that would exceed 25 MB).
  `a5_exchange_readme.gif`, shown in the top-level README, is the same GIF from 6.9 s on, its first
  informative frame (the opening seconds show only the title).
* `renders/stills/dark/*.png` — the final frame of each scene (dark theme).
* `renders/stills/light/*.png` — the same frames in the light theme; `crop_figures.py` crops them into
  `../paper/figures/` for the paper.

## Rendering

Requirements: [Manim Community](https://www.manim.community/) 0.21 with a LaTeX installation
(for `MathTex`), and `ffmpeg`.

```sh
# everything: videos, GIFs, stills in both themes, and the paper's figures
MANIM=/path/to/manim ./render.sh

# only some scenes
MANIM=/path/to/manim ./render.sh B2Levels B3Threshold

# a single scene by hand (dark theme, 1080p60); GG5_THEME=light selects the light theme
manim -qh scenes/b2_levels.py B2Levels
```

`render.sh` runs from this directory; manim's working files go to `build/` (not committed).

## Code

* `lib/geometry.py` — the exact setting: `ζ`, `φ`, `√(3+φ)`, the chord and its pieces, the turns,
  words acting on segments, `ℤ[ζ]` in the basis `1, w, w², w³` (`w = e^{πi/5}`), the functionals,
  levels and classes, the lens window, cut levels, and orbits through the pivot walk.
* `lib/style.py` — the two themes, colours, typography, small drawing helpers, and the reading
  time: after any text appears, everything stays still for 2 s + 0.35 s per word + 1 s per
  equation (`hold`), and the last frame of a scene for at least 4 s.
* `lib/anim.py` — turning a disk and its contents.
* `scenes/*.py` — one file per scene (the three word scenes share one file).

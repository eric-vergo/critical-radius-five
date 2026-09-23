# Paper

`main.tex` — *The critical radius of the five-fold two-disk puzzle*: a short, self-contained account
of the proof that `GG₅(r)` is finite exactly when `r < √(3+φ)`, with an appendix that maps every
step to its Lean declaration. `main.pdf` is the compiled version.

Build (pdfLaTeX; run twice for the cross-references):

```sh
pdflatex main && pdflatex main
```

Packages used (all part of TeX Live): `newpx` (with `newtx`, `txfonts`, `fontaxes`, `kastrup`),
`inconsolata`, `microtype`, `mathtools`, `amsthm`, `thmtools`, `caption`, `subcaption`, `booktabs`,
`tabularx`, `enumitem`, `xcolor`, `hyperref`, `cleveref`, `fancyvrb`, `newunicodechar`, `geometry`.

The figures in `figures/` are crops of the final frames of the animations (light theme); they are
produced by `../animations/render.sh` (see `../animations/crop_figures.py`).

Items still to be supplied are typeset in red: the authors, the date, and the confirmation of the
comparator run.

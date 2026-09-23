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
`tabularx`, `longtable`, `enumitem`, `xcolor`, `hyperref`, `cleveref`, `fancyvrb`, `newunicodechar`,
`geometry`; and pdfTeX's `glyphtounicode.tex`, which gives the PDF a text layer in which `√` and `°`
copy and search as themselves.

The figures in `figures/` are crops of the final frames of the animations (light theme); they are
produced by `../animations/render.sh` (see `../animations/crop_figures.py`).

Two items remain for the authors; both are typeset in red on the title page of `main.pdf`:

- the authors, with affiliations and emails: `\author{…}` in `main.tex`, and `pdfauthor` in the
  `\hypersetup` line below it;
- the date: `\date{…}`.

Once both are filled in, the `\placeholder` macro can be deleted.

`check_lean_names.py` lists the Lean names cited in `main.tex` (`\leanname{…}`) that the library
does not declare; run it from the repository root after the library changes:

```sh
python3 paper/check_lean_names.py
```

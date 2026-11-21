# MET-28-a · Black's Spheres Vindicated

- **Family:** MET-28 — Is the identity of indiscernibles true?
- **Type:** principal
- **Discipline:** Metaphysics
- **Estimated length:** 3 pages
- **Formalized:** yes, see `lean/Philosophy/MET/MET_28.lean`

## Main result

No, for absolute and relative discernibility: Black's two spheres are a genuine counterexample. The principle holds only in its weak form, since the spheres are weakly discernible.

## Files

- [`MET-28-a.pdf`](MET-28-a.pdf): compiled manuscript
- `main.tex` (and any further `.tex` files), `situationist-preprint.cls`: sources
- `gen/` (where present): the program that generates the computed tables, with its own README

## Build

```
latexmk -pdf main.tex
```

## Citation

See [`MET-28-a.bib`](MET-28-a.bib).

## Changelog

- 2026-10-07: Formalization showed that the counterexample holds for absolute and relative discernibility but not for weak discernibility: the two spheres are weakly discernible. Statement of the main theorem restricted accordingly.
- 2026-10-06: initial version.

# REL-15-a · A Uniqueness Theorem for Maximal Greatness

- **Family:** REL-15 — Could there be more than one god?
- **Type:** principal
- **Discipline:** Philosophy of Religion
- **Estimated length:** 2 pages
- **Formalized:** yes, see `lean/Philosophy/REL/REL_15.lean`

## Main result

No. Given that maximal greatness entails omnipotence, there is at most one maximally great being, since an omnipotent being could thwart any other.

## Files

- [`REL-15-a.pdf`](REL-15-a.pdf): compiled manuscript
- `main.tex` (and any further `.tex` files), `situationist-preprint.cls`: sources
- `gen/` (where present): the program that generates the computed tables, with its own README

## Build

```
latexmk -pdf main.tex
```

## Citation

See [`REL-15-a.bib`](REL-15-a.bib).

## Changelog

- 2026-10-07: Formalization revealed an implicit premise: that maximal greatness entails omnipotence. The premise is now stated explicitly as Assumption 2.1. The proof is otherwise unchanged.
- 2026-10-06: initial version.

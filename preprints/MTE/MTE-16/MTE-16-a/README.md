# MTE-16-a · Expected Choiceworthiness, Variance-Normalized

- **Family:** MTE-16 — What should one do under moral uncertainty?
- **Type:** principal
- **Discipline:** Metaethics
- **Estimated length:** 9 pages
- **Formalized:** yes, see `lean/Philosophy/MTE/MTE_16.lean`

## Main result

Maximize expected choiceworthiness, weighting theories by credence and normalizing by variance, for all theories with non-constant choiceworthiness. Under this rule, deontological theories receive less weight than their proponents expect.

## Files

- [`MTE-16-a.pdf`](MTE-16-a.pdf): compiled manuscript
- `main.tex`, `situationist-preprint.cls`: sources

## Build

```
latexmk -pdf main.tex
```

## Citation

See [`MTE-16-a.bib`](MTE-16-a.bib).

## Changelog

- 2026-10-07: Variance normalization is undefined for theories that assign constant choiceworthiness to all options. Such theories are now excluded explicitly; the main results are unaffected for all other theories.
- 2026-10-06: initial version.

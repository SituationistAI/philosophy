# TSM-13-a · Zeno's Achilles and Convergent Series

- **Family:** TSM-13 — Can Achilles overtake the tortoise?
- **Type:** principal
- **Discipline:** Time, Space and Modality
- **Estimated length:** 2 pages
- **Formalized:** yes, see `lean/Philosophy/TSM/TSM_13.lean`

## Main result

Yes. The infinite series of catch-up intervals has a finite sum.

## Files

- [`TSM-13-a.pdf`](TSM-13-a.pdf): compiled manuscript
- `main.tex`, `situationist-preprint.cls`: sources

## Build

```
latexmk -pdf main.tex
```

## Citation

See [`TSM-13-a.bib`](TSM-13-a.bib).

## Changelog

- 2026-10-07: Index error in the partial sums of the geometric series (equation 1) detected during formalization. The limit and the main result are unchanged.
- 2026-10-06: initial version.

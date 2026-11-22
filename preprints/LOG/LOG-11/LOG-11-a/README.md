# LOG-11-a · The Surprise Examination

- **Family:** LOG-11 — Can the surprise examination take place?
- **Type:** principal
- **Discipline:** Logic and Philosophy of Logic
- **Estimated length:** 3 pages
- **Formalized:** yes, see `lean/Philosophy/LOG/LOG_11.lean`

## Main result

Yes, on any day but the last. The students' backward induction fails at its second step.

## Files

- [`LOG-11-a.pdf`](LOG-11-a.pdf): compiled manuscript
- `main.tex`, `situationist-preprint.cls`: sources

## Build

```
latexmk -pdf main.tex
```

## Citation

See [`LOG-11-a.bib`](LOG-11-a.bib).

## Changelog

- 2026-10-07: The proof of Theorem 3.1 used the KK principle at its decisive step. A new proof that does not rely on KK is given.
- 2026-10-06: initial version.

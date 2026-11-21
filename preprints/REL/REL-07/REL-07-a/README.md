# REL-07-a · Hume's Maxim Quantified

- **Family:** REL-07 — Can testimony justify belief in miracles?
- **Type:** principal
- **Discipline:** Philosophy of Religion
- **Estimated length:** 3 pages
- **Formalized:** yes, see `lean/Philosophy/REL/REL_07.lean`

## Main result

Yes. Formalized in Bayesian terms, Hume's maxim can be met by a sufficient number of testimonies that are independent conditional on the truth of the report, under any prior that does not assign miracles probability zero.

## Files

- [`REL-07-a.pdf`](REL-07-a.pdf): compiled manuscript
- `main.tex` (and any further `.tex` files), `situationist-preprint.cls`: sources
- `gen/` (where present): the program that generates the computed tables, with its own README

## Build

```
latexmk -pdf main.tex
```

## Citation

See [`REL-07-a.bib`](REL-07-a.bib).

## Changelog

- 2026-10-07: The independence assumption on testimonies is replaced by independence conditional on the truth of the reported event. The threshold formula in Proposition 2.3 is corrected; the qualitative conclusion is unchanged.
- 2026-10-06: initial version.

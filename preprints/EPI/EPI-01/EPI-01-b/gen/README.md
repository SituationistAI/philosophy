# Generator for EPI-01-b

`python3 generate.py` (Python 3, standard library only) reads the hand-curated
case table `cases.py` and writes `catalogue.tex`, `variants.tex`,
`profiles.tex`, `thresholds.tex`, `classes.tex`, `matrix.tex`, `combos.tex`,
`rivals.tex`, `departures.tex`, `census.tex` and `stats.tex` in this directory;
`../main.tex` includes them with `\input{gen/...}`.

Every theorem of Section 4 of the manuscript is checked with `assert` on every
catalogued case, on every generated variant, and on every model of the bounded
census of Appendix E; the script halts if any check fails. Output is
deterministic (no randomness). Run time is a few seconds.

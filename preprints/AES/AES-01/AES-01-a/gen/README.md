# Generator for AES-01-a

`python3 generate.py` (Python 3, standard library only) reads the hand-curated
catalogue of episodes in `cases.py` and the documented histories in
`timelines.py`, and writes `catalogue.tex`, `variants.tex`, `census.tex`,
`histories.tex`, `timelines.tex`, `rivals.tex`, `thresholds.tex` and
`stats.tex` in this directory; `../main.tex` includes them with
`\input{gen/...}`.

The theorems of Section 3 of the manuscript are checked with `assert` on every
catalogued episode, on every systematic variant, on all 252 encoded states
(Appendix C), on all histories of artworld events of length three, four and
five (Appendix D), and on the documented histories (Appendix E); the script
halts if any check fails. Output is deterministic. Run time is a few seconds.

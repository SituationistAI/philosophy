# Generator for EXI-10-b

`python3 generate.py` (Python 3, standard library only) reads the
hand-curated study table `studies.py`, computes each study's bearing on the
mismatch thesis (a) and the function thesis (b) of EXI-10 by the fixed rules
stated in `generate.py` and in the preface of the appendix, and writes
`annotated.tex`, `summary.tex`, `clauses.tex`, `codes.tex`, the
cross-tabulations `xt_*.tex` and `stats.tex`, which `../main.tex` includes.
Output is deterministic.

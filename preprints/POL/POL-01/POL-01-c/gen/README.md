# Generator for POL-01-c

`python3 generate.py` (Python 3, standard library only) solves the 24 exchange
economies listed in `ECONOMIES` and writes `tab_economies.tex`,
`tab_summary.tex` and `summary.tex` in this directory; `../main.tex` includes
the first two with `\input{gen/...}`. Equilibrium prices from given holdings are
exact rationals (`fractions`); quantities involving fractional powers are
computed with the `decimal` module at 60 significant digits. Every check is an
`assert`: the script halts if any check fails. Output is deterministic. Run time
is about half a minute.

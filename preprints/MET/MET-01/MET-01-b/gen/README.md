# Generator for MET-01-b

`python3 generate.py` (Python 3, standard library only) writes the tables
`tab_a.tex` ... `tab_f.tex` and `summary.tex` in this directory; `../main.tex`
includes them with `\input{gen/...}`. Output is deterministic (exact rational
arithmetic with `fractions`; the pseudo-random perturbations of Volume E use
`random.Random(20261006)`). Every check is an `assert`: the script halts if any
bound fails. Run time is a few seconds.

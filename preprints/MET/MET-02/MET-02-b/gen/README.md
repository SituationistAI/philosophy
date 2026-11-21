# Generator for MET-02-b

`python3 generate.py` (Python 3, standard library only) writes the tables
`tab_a1.tex` ... `tab_k.tex` and `summary.tex` (counts used in the text) in
this directory; `../volumes.tex` includes them with `\input{gen/...}`.

All charges, anomaly coefficients, dimension exponents and boosts are exact
rationals (`fractions`). Every check is an `assert`; the script halts if any
fails and prints summary statistics and the number of checks otherwise.
Output is deterministic. Run time is under a second.

The data tables (Standard Model multiplets, SI quantities and relations, laws,
Pi problems, inventory candidates with their recorded features) are at the top
of each volume's section in `generate.py`.

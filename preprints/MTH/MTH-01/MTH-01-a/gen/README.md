# Generator for MTH-01-a

`python3 generate.py` (Python 3, standard library only) writes `tab_a.tex` ... `tab_e.tex` and
`summary.tex` in this directory; `../main.tex` includes them with `\input{gen/...}`.

The script contains two hand-curated tables: the register of mathematical structures with their
carrier cardinalities and direct presuppositions, and the table of laws (equation, variables,
structures, reference, derivation sources, overrides of the nominalization status). Everything
else (closures, cardinalities, number commitments, statuses by rule, cross-tabulations,
presupposition chains) is computed. Output is deterministic. Every claim the manuscript makes
about the tables is an `assert`; the script halts if one fails. Run time is under a second.

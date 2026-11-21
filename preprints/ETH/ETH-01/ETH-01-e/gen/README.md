# Generator for ETH-01-e

`python3 generate.py` (Python 3, standard library only) writes `vol04.tex`,
`skeleton.tex` and `stats.tex`; `../main.tex` includes them. `errata_engine.py`
is identical to the copy in REL-01-h/gen. Deterministic
(`random.Random(20261008)`). The skeleton of Volume IV (pp. 1,161-1,559),
the real bibliography and the pages reserved for errata E1-E6 are fixed in
`generate.py`; every entry lies in its chapter's page range (asserted).

# Generator for REL-01-h

`python3 generate.py` (Python 3, standard library only) writes `vol03.tex` ...
`vol11.tex`, `skeleton.tex` and `stats.tex` in this directory; `../main.tex`
includes them with `\input{gen/...}`. `errata_engine.py` holds the shared
machinery (also copied, identically, to ETH-01-e/gen). Output is deterministic
(`random.Random(20261007)`).

The data in `generate.py` fix the skeleton of Volumes III-XI (chapter titles,
page ranges, numbered items, Volume X lemma ranges 1-3361 with Lemma 2417 in
Chapter 5 on p. 3803), the real bibliography, and the pages reserved for the
hand-written substantive corrigenda S1-S18. Every generated entry lies in its
chapter's page range (asserted), and every cross-reference names an item of
the skeleton.

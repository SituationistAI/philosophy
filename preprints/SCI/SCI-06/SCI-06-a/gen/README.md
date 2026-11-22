# Generator for SCI-06-a, Part II (translation manuals)

Hand-curated data:

- `data1.py` ... `data5.py`: the translation manuals for ten revolutions
  (CHEM, ASTR, MECH, HEAT, QUAN, BIOL, PHYS, OPTI, MIAS, HERE): terms of the
  predecessor theory with their role, type-level image in the successor
  (a string, a list for partial denotation, or None), token readings with
  their referents, and the inferences of the predecessor with verdicts
  H / R / X / U;
- `renderings1.py` ... `renderings3.py`: the translation of each inference
  (verdicts H, R, X) or, for verdict U, an interpretation;
- `evidence.py`: the evidential claims behind each criterion recorded as
  favouring the successor.

`generate.py` computes translation statuses, weights, scores, the translation
index, the comparability index, the untranslatable cluster, the neutral core,
the indices under scoring schemes S1--S4 and the outcome on the five shared
criteria, and asserts checks C1--C9 (see its docstring and the preface of
Part II). It writes `manuals.tex`, `inferences.tex`, `evidence.tex`,
`summary.tex` and `stats.tex`.

Regenerate (Python 3, standard library only, deterministic, under a second):

    cd content/preprints/SCI/SCI-06/SCI-06-a/gen && python3 generate.py

then compile from the repository root with
`NOLEAN=1 python3 tools/produce.py SCI-06-a`. A failed check raises an
AssertionError naming the check, the revolution and the entry.

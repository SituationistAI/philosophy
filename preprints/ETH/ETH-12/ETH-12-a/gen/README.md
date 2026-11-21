# Generator for ETH-12-a, Appendices A-C

`generate.py` implements the criterion of right action of Section 3
(Definitions 3.1-3.15, Principle P1) with the calibration of Assumption 3.7,
and writes:

- `concordance.tex`, `rules.tex`: the concordance of virtues (Appendix A), with
  goods and modes computed from the sphere tags by the rules of Table A.1;
- `cases.tex`: the 19 classic cases and the 11 parametrized schemas (Appendix B),
  with the verdicts of the criterion, of a simple consequentialist rule and of a
  simple deontological rule;
- `misperception.tex`: the misperception variants of the classic cases;
- `graphs.tex`, `codify.tex`: the dependency-graph checks and the 120 v-rule
  codes (Appendix C);
- `stats.tex`: macros with the counts quoted in the text.

Every theorem checked is an assertion; a failure raises AssertionError naming
the check and the case. Python 3, standard library only, exact rational
arithmetic, deterministic, a few seconds.

Regenerate:

    cd content/preprints/ETH/ETH-12/ETH-12-a/gen && python3 generate.py

then compile from the repository root with

    NOLEAN=1 python3 tools/produce.py ETH-12-a

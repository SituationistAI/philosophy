# Generator for PID-01-a, Appendix A

`generate.py` enumerates every case structure within the bound stated in the
appendix (at most 3 times after the original, at most 2 stages per time, at
most 4 stages after the original, at most 2 parents per stage, at most one
stage realized in a thing of another kind), up to isomorphism, computes the
verdict of the PID-01 criterion and of four rival criteria on every stage, and
asserts the eight checks listed in the appendix preface. It writes

- `cases.tex`: the longtable rows included by `main.tex`;
- `stats.tex`: macros with the summary statistics and the identifiers of the
  cases discussed in the text.

Regenerate (Python 3, standard library only; deterministic; a few seconds):

    cd content/preprints/PID/PID-01/PID-01-a/gen && python3 generate.py

then compile with `NOLEAN=1 python3 tools/produce.py PID-01-a` from the
repository root. A failed check raises an AssertionError naming the check and
the case.

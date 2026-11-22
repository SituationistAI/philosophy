# Generator for the computed part of TSM-01-a

Regenerate the tables (Python 3, standard library only; deterministic; a few seconds):

    cd content/preprints/TSM/TSM-01/TSM-01-a/gen && python3 generate.py

Outputs, included by `main.tex`:

- `frames_detail.tex` — Appendix A: every branching frame (finite rooted tree under earlier-than) with at most 10 moments, one per isomorphism class (1205), with per-moment settledness data over all 2^n valuations.
- `histories.tex` — Appendix B: every history of every frame with at most 9 moments, with profile and settling moment.
- `frames_eleven.tex` — Appendix C: one summary line for each of the 1842 frames with 11 moments.
- `stats.tex` — Table 1 (summary by number of moments).
- `numbers.tex` — macros with headline counts used in the prose.
- `index.txt` — plain-text index of all frames (not included in the PDF).

All checks (monotonicity of settledness, bivalence relative to a history and the openness criterion, non-increasing profiles, the moment-relative A-assignment facts, automorphism group orders, and an independent labelled-tree cross-check of exhaustiveness for n <= 10) are Python `assert`s: the script aborts if any fails.

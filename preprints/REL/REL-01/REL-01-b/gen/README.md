# Computed part of REL-01-b

`generate.py` (Python 3, standard library only) enumerates every Kripke frame with at most four
worlds up to isomorphism (3,160 frames), classifies each by the frame conditions T, B, 4, 5, D, U, U+
and C, and decides by brute force over all valuations whether the schemas S1--S6 of the manuscript are
valid on it, in propositional form and in quantified form over a constant domain of two beings. It
aborts if any schema's verdict differs from the first-order condition the manuscript proves equivalent
to it, or if the quantified and propositional verdicts differ.

Regenerate (about ten seconds), from this directory:

    python3 generate.py

Outputs: `frames.tex` (the listing of Appendix A), `systems.tex`, `counts.tex`, `stats.tex`.

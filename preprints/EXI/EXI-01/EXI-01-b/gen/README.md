# Generator for EXI-01-b (Commentary, Volume I)

`python3 generate.py` (Python 3, standard library only, deterministic) reads
the EXI manuscripts (`../../../EXI-*/EXI-*-?/main.tex` and their compiled
`main.aux`, excluding EXI-01-b itself), the lemma list `lemmata.py` and the
Lean module `content/lean/Philosophy/EXI/EXI_01.lean`, and writes:

- `lemmacheck.txt` — checks: every lemma occurs verbatim in EXI-01-a; every
  `\lem{n}{...}` in `../ch*.tex` quotes lemma n exactly; every lemma is quoted;
  every Lean listing in the chapters occurs in the module (halts on failure);
- `text.tex` — the text of EXI-01-a divided into lemmata;
- `index.tex`, `families.tex`, `families2.tex`, `kwic.tex` — Appendix A
  (word index, term families, keyword-in-context concordance);
- `xref.tex`, `xrefsum.tex`, `xrefms.tex`, `xrefclasses.tex` — Appendix B
  (numbered statements from the .aux files, concept classes, bearings);
- `testimonia.tex` — Appendix C;
- `stats.tex` — summary macros used in the prose.

Run it before compiling `../main.tex`; the other manuscripts must have been
compiled so that their `.aux` files exist.

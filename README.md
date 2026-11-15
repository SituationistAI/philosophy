
# Philosophy

This repository contains philosophical manuscripts and supporting proof artifacts produced by an internal Situationist AI model. As part of model development, we evaluate our models on open problems in philosophy.

## Navigating the collection

The current catalogue contains 719 manuscripts organized into 372 families. A family groups related papers, which may include a principal result, companion arguments, consequences, alternative proofs or errata. Each family is classified by philosophical discipline.

- New readers can begin with the [reading guide](READING_GUIDE.md).
- Start with the [overview](overview.md) for descriptions of the families.
- Use the [manuscript map](CONTENTS.md) to find individual papers and their supporting materials.
- The [`preprints/`](preprints/) directory contains PDFs, source files, and manuscript-specific citation and build instructions.
- The [Lean library](lean/) and [formalization catalogue](formalization/README.md) describe the available formal proofs, their associated papers, and verification configurations. About 43% of top-line results are formalized.
- The [apparatus](apparatus/README.md) gives cross-references, a citation graph and indices computed from the sources.
- Updates to the repository are described in the [history](history.md).

## Disciplines

| Discipline | Code | Families | Manuscripts | Formalized top-line results |
|---|---|---|---|---|
| Metaphysics | MET | 30 | 58 | 14 |
| Philosophy of Religion | REL | 24 | 52 | 18 |
| Normative and Applied Ethics | ETH | 28 | 59 | 13 |
| Metaethics | MTE | 20 | 36 | 10 |
| Epistemology | EPI | 26 | 50 | 13 |
| Philosophy of Mind | MND | 26 | 50 | 10 |
| Philosophy of Language | LNG | 22 | 42 | 11 |
| Logic and Philosophy of Logic | LOG | 20 | 38 | 16 |
| Philosophy of Science | SCI | 22 | 42 | 10 |
| Political Philosophy | POL | 24 | 45 | 6 |
| Aesthetics | AES | 18 | 34 | 2 |
| Action, Agency and Free Will | ACT | 18 | 36 | 6 |
| Personal Identity and the Self | PID | 16 | 30 | 5 |
| Time, Space and Modality | TSM | 18 | 34 | 5 |
| Meaning, Death and the Absurd | EXI | 20 | 38 | 1 |
| Phenomenology | PHE | 22 | 40 | 9 |
| Philosophy of Mathematics | MTH | 18 | 35 | 10 |
| **Total** | | **372** | **719** | **159** |

## Status of the results

The manuscripts are at different stages of verification. A formalization establishes that the main argument of a manuscript is valid relative to its stated premises; it does not establish that the premises are true. Some of the unformalized results could have issues. Corrections are recorded in the [history](history.md) and in the changelog of each affected manuscript.

## Citation

To cite an individual manuscript, use the BibTeX entry in its directory. To cite the collection as a whole, see [`CITATION.cff`](CITATION.cff).

## License

The contents of this repository are released under the Apache License 2.0. See [`LICENSE`](LICENSE).

## About this repository

Situationist AI is a fictional laboratory, and this repository is an artistic and critical project. It adopts the form of a large release of machine-generated research in order to examine what such releases claim, and what they leave unexamined.

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24439718.svg)](https://doi.org/10.5281/zenodo.24439718)

# Philosophy

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24439719.svg)](https://doi.org/10.5281/zenodo.24439719)

This repository contains philosophical manuscripts and supporting proof artifacts produced by an internal Situationist AI model. As part of model development, we evaluate our models on open problems in philosophy.

## Navigating the collection

The current catalogue contains 719 manuscripts organized into 372 families. A family groups related papers, which may include a principal result, companion arguments, consequences, alternative proofs or errata. Each family is classified by philosophical discipline.

- New readers can begin with the [reading guide](READING_GUIDE.md).
- Start with the [overview](overview.pdf) for descriptions of the families.
- Use the [manuscript map](CONTENTS.md) to find individual papers and their supporting materials.
- The [`preprints/`](preprints/) directory contains PDFs, source files, and manuscript-specific citation and build instructions.
- The [Lean library](lean/README.md) and [formalization catalogue](lean/formalization.yaml) describe the available formal proofs, their associated papers, and verification configurations. About 43% of top-line results are formalized.
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

## How the results were produced

Most results were produced by the same procedure. An internal model was given a single question and asked for a manuscript answering it, with one prompt and one agent; some questions took several attempts. About 4,000 questions were posed during the evaluation, and the average compute per retained manuscript was about three hours. Manuscripts were then checked for compilation, internal cross-references and consistency with the rest of the collection, and the formalized arguments were checked in Lean.

There are two kinds of exception. For the computed volumes (TSM-01-a, PID-01-a, MET-01-b, POL-01-c, REL-01-b, REL-01-c) and the inventories (MTH-01-a, MET-02-b, EPI-01-b, SCI-06-a, AES-01-a, EXI-10-b, ETH-12-a), the model also wrote the programs in each manuscript's `gen/` directory and ran them; the tables are their output. The multi-volume works are released as first volumes, with plans of the later volumes; errata to those volumes are released where they were produced.

## Versions and citations

The collection is archived on Zenodo: [doi:10.5281/zenodo.24439718](https://doi.org/10.5281/zenodo.24439718). This DOI always resolves to the latest version.

The release history is preserved in [history.md](history.md). Corrections are recorded as new versions of the affected manuscripts, each with a changelog in its directory. To cite an individual manuscript, use the BibTeX entry in its directory; to cite the collection, see [`CITATION.cff`](CITATION.cff).

## Status of the results

The manuscripts are at different stages of verification. A formalization establishes that the main argument of a manuscript is valid relative to its stated premises; it does not establish that the premises are true. Some of the unformalized results could have issues. Corrections are recorded in the [history](history.md) and in the changelog of each affected manuscript.

## License

The contents of this repository are released under the Apache License 2.0. See [`LICENSE`](LICENSE).


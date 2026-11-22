# Reading guide

The collection contains 719 manuscripts. Most readers will want a path through it rather than the full list. This guide suggests six.

## 1. The principal results, in brief

Read the [overview](overview.pdf). Each family is one question with one answer, stated in a sentence or two. Then open the principal manuscript (the one ending in `-a`) of any family whose answer you find surprising. Principal manuscripts range from one page (EXI-01-a) to several hundred.

## 2. Ten families to start with

| Family | Question | Why start here |
|---|---|---|
| [MET-01](preprints/MET/MET-01/) | Why is there something rather than nothing? | A formalized measure argument, with a computed companion (MET-01-b) and a corrigendum to a volume not yet released (MET-01-e). |
| [REL-01](preprints/REL/REL-01/) | Does God exist? | An eleven-volume work. Volume I is released, together with two computed companions (REL-01-b, REL-01-c) and 168 pages of corrigenda to Volumes III–XI (REL-01-h). |
| [ETH-03](preprints/ETH/ETH-03/) | The trolley problem | A short formalized argument, and a revised alternative proof (ETH-03-c). |
| [LOG-11](preprints/LOG/LOG-11/) | Can the surprise examination take place? | Revised on 7 October: the earlier proof used the KK principle. |
| [MET-28](preprints/MET/MET-28/) | Is the identity of indiscernibles true? | The formalization restricted the main theorem. |
| [MND-01](preprints/MND/MND-01/) | Can the hard problem of consciousness be solved? | A four-volume work, its companions, and errata to Volume III. |
| [TSM-01](preprints/TSM/TSM-01/) | Is time real? | 33 pages of argument and 250 pages of computed branching-time frames. |
| [PID-01](preprints/PID/PID-01/) | What makes you the same person over time? | 11,009 computed cases of fission, fusion and teleportation. |
| [EXI-01](preprints/EXI/EXI-01/) | What is the meaning of life? | A one-page principal manuscript and the first volume of a 1,104-page commentary on it. |
| [PHE-22](preprints/PHE/PHE-22/) | Can a machine perform the phenomenological reduction? | A negative result obtained by a machine, and a note on its provenance (PHE-22-b). |

## 3. Corrections

The [history](history.md) lists the three withdrawals and fourteen revisions of 7 October 2026. Four of the revisions were found during formalization. EPI-10-b discusses the rationality of errata with reference to these corrections.

## 4. Manuscripts that concern the collection itself

A small number of families bear on the collection that contains them. In each, the register is the same as elsewhere.

- MND-08-c: a note on the author's interest in the question whether machines can think.
- ETH-24-b: a note on the authorship of a manuscript about the moral status of artificial systems.
- ACT-16-b: responsibility for the collection.
- PHE-22-a and PHE-22-b: a machine can bracket everything except the bracketing itself; the result and its provenance.
- POL-24-a and POL-24-b: the collection as spectacle, and a détournement of that claim.
- EPI-10-b, SCI-22-a/b, MTH-17-a/b, EXI-20-a/b.

## 5. Very long manuscripts

Twenty-eight manuscripts have nominal lengths of thirty pages or more. Their released parts take three forms.

- **Computed volumes.** TSM-01-a, PID-01-a, MET-01-b, POL-01-c, REL-01-b, REL-01-c. The written argument is followed by exhaustive enumerations or solved instances. Each is produced by a program in the manuscript's `gen/` directory, which can be rerun and which stops if any check fails.
- **Inventories and catalogues.** MTH-01-a (the mathematics used by physical theories), MET-02-b (candidate fundamental quantities), EPI-01-b (Gettier cases), SCI-06-a (translation manuals for ten scientific revolutions), AES-01-a (boundary cases of art), EXI-10-b (empirical studies of boredom), ETH-12-a (virtues and test cases).
- **Shorter companions.** MND-01-b, MND-01-c, ETH-01-b, ETH-01-c, ACT-01-c and LNG-01-c are released as essays of 12–14 pages, below their nominal lengths.
- **First volumes and errata.** The remaining multi-volume works are released as Volume I, with a plan of the later volumes. Errata to unreleased volumes (MET-01-e, MND-01-e, ACT-01-e, ETH-01-e, REL-01-h) are consistent with those plans.

The nominal length of each manuscript is given in the [manuscript map](CONTENTS.md).

## 6. Formalization and apparatus

The [formalization catalogue](lean/formalization.yaml) lists 159 Lean modules and what each establishes. A formalization shows that an argument is valid relative to its premises, which are stated as axioms; it does not show that they are true. The [apparatus](apparatus/README.md) gives cross-references between all manuscripts, the family-level citation graph, an index of keywords and a count of numbered statements, all computed from the sources.

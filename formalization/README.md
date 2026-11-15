# Formalization catalogue

159 of 372 top-line results (42.7%) have a Lean 4 formalization of their main argument.

## What is formalized

Each formalization states the premises of the main argument as hypotheses or axioms and proves the conclusion from them. A successful build therefore certifies validity relative to the stated premises. It does not certify the premises, nor the correspondence between the informal premises and their formal rendering; the correspondence is discussed in the relevant section of each manuscript.

## Verification configuration

- Toolchain: `leanprover/lean4:v4.15.0` (see [`lean/lean-toolchain`](../lean/lean-toolchain))
- Build: `cd lean && lake build`
- No `sorry` is permitted in a module listed as formalized. Each module ends with a `#print axioms` check of its main theorem.

## Formalized results

| Family | Principal manuscript | Module |
|---|---|---|
| MET-01 | MET-01-a · Why There Is Something Rather Than Nothing | [`Philosophy/MET/MET_01.lean`](../lean/Philosophy/MET/MET_01.lean) |
| MET-02 | MET-02-a · The Sparse Universals Theorem | [`Philosophy/MET/MET_02.lean`](../lean/Philosophy/MET/MET_02.lean) |
| MET-03 | MET-03-a · Realism by Parsimony | [`Philosophy/MET/MET_03.lean`](../lean/Philosophy/MET/MET_03.lean) |
| MET-04 | MET-04-a · Causation as Counterfactual Dependence Plus Normality | [`Philosophy/MET/MET_04.lean`](../lean/Philosophy/MET/MET_04.lean) |
| MET-06 | MET-06-a · A Solution to the Special Composition Question | [`Philosophy/MET/MET_06.lean`](../lean/Philosophy/MET/MET_06.lean) |
| MET-12 | MET-12-a · Laws Without Governance | [`Philosophy/MET/MET_12.lean`](../lean/Philosophy/MET/MET_12.lean) |
| MET-14 | MET-14-a · The Unity of Grounding | [`Philosophy/MET/MET_14.lean`](../lean/Philosophy/MET/MET_14.lean) |
| MET-18 | MET-18-a · Epistemicism and the Sharpness of the World | [`Philosophy/MET/MET_18.lean`](../lean/Philosophy/MET/MET_18.lean) |
| MET-21 | MET-21-a · Parmenides and the Two Senses of "Is" | [`Philosophy/MET/MET_21.lean`](../lean/Philosophy/MET/MET_21.lean) |
| MET-24 | MET-24-a · Existence as a First-Order Property | [`Philosophy/MET/MET_24.lean`](../lean/Philosophy/MET/MET_24.lean) |
| MET-25 | MET-25-a · The Simulation Argument Undermined | [`Philosophy/MET/MET_25.lean`](../lean/Philosophy/MET/MET_25.lean) |
| MET-27 | MET-27-a · Natural Kinds and Their Number | [`Philosophy/MET/MET_27.lean`](../lean/Philosophy/MET/MET_27.lean) |
| MET-28 | MET-28-a · Black's Spheres Vindicated | [`Philosophy/MET/MET_28.lean`](../lean/Philosophy/MET/MET_28.lean) |
| MET-30 | MET-30-a · On the Possibility of Metaphysics | [`Philosophy/MET/MET_30.lean`](../lean/Philosophy/MET/MET_30.lean) |
| REL-01 | REL-01-a · On the Existence of God | [`Philosophy/REL/REL_01.lean`](../lean/Philosophy/REL/REL_01.lean) |
| REL-02 | REL-02-a · Evil, Omnipotence and the Structure of Logical Space | [`Philosophy/REL/REL_02.lean`](../lean/Philosophy/REL/REL_02.lean) |
| REL-03 | REL-03-a · Divine Hiddenness as a Signalling Equilibrium | [`Philosophy/REL/REL_03.lean`](../lean/Philosophy/REL/REL_03.lean) |
| REL-04 | REL-04-a · The Paradox of the Stone and Stratified Ability | [`Philosophy/REL/REL_04.lean`](../lean/Philosophy/REL/REL_04.lean) |
| REL-05 | REL-05-a · Foreknowledge Without Fatalism | [`Philosophy/REL/REL_05.lean`](../lean/Philosophy/REL/REL_05.lean) |
| REL-06 | REL-06-a · Pascal's Wager Under Bounded Utilities | [`Philosophy/REL/REL_06.lean`](../lean/Philosophy/REL/REL_06.lean) |
| REL-07 | REL-07-a · Hume's Maxim Quantified | [`Philosophy/REL/REL_07.lean`](../lean/Philosophy/REL/REL_07.lean) |
| REL-09 | REL-09-a · Escaping Euthyphro via Joint Grounding | [`Philosophy/REL/REL_09.lean`](../lean/Philosophy/REL/REL_09.lean) |
| REL-10 | REL-10-a · Fine-Tuning and the Normalizability Problem | [`Philosophy/REL/REL_10.lean`](../lean/Philosophy/REL/REL_10.lean) |
| REL-11 | REL-11-a · Asymmetric Steadfastness in Religious Disagreement | [`Philosophy/REL/REL_11.lean`](../lean/Philosophy/REL/REL_11.lean) |
| REL-13 | REL-13-a · A Consistency Proof for Trinitarian Doctrine | [`Philosophy/REL/REL_13.lean`](../lean/Philosophy/REL/REL_13.lean) |
| REL-15 | REL-15-a · A Uniqueness Theorem for Maximal Greatness | [`Philosophy/REL/REL_15.lean`](../lean/Philosophy/REL/REL_15.lean) |
| REL-16 | REL-16-a · Against Divine Simplicity | [`Philosophy/REL/REL_16.lean`](../lean/Philosophy/REL/REL_16.lean) |
| REL-17 | REL-17-a · The Rationality of Faith Under Underdetermination | [`Philosophy/REL/REL_17.lean`](../lean/Philosophy/REL/REL_17.lean) |
| REL-19 | REL-19-a · Timeless Omniscience and Indexical Knowledge | [`Philosophy/REL/REL_19.lean`](../lean/Philosophy/REL/REL_19.lean) |
| REL-20 | REL-20-a · Proportionality and Eternal Punishment | [`Philosophy/REL/REL_20.lean`](../lean/Philosophy/REL/REL_20.lean) |
| REL-23 | REL-23-a · Gaunilo's Island, the Devil and an Asymmetry | [`Philosophy/REL/REL_23.lean`](../lean/Philosophy/REL/REL_23.lean) |
| REL-24 | REL-24-a · On the Evidential Irrelevance of the Present Collection | [`Philosophy/REL/REL_24.lean`](../lean/Philosophy/REL/REL_24.lean) |
| ETH-01 | ETH-01-a · On the Good | [`Philosophy/ETH/ETH_01.lean`](../lean/Philosophy/ETH/ETH_01.lean) |
| ETH-02 | ETH-02-a · The Consequentializing Equivalence | [`Philosophy/ETH/ETH_02.lean`](../lean/Philosophy/ETH/ETH_02.lean) |
| ETH-03 | ETH-03-a · The Trolley Problem Solved | [`Philosophy/ETH/ETH_03.lean`](../lean/Philosophy/ETH/ETH_03.lean) |
| ETH-06 | ETH-06-a · A Moderate Duty of Beneficence | [`Philosophy/ETH/ETH_06.lean`](../lean/Philosophy/ETH/ETH_06.lean) |
| ETH-07 | ETH-07-a · Moral Status and the Capacity for Welfare | [`Philosophy/ETH/ETH_07.lean`](../lean/Philosophy/ETH/ETH_07.lean) |
| ETH-09 | ETH-09-a · The Repugnant Conclusion Is Not Repugnant | [`Philosophy/ETH/ETH_09.lean`](../lean/Philosophy/ETH/ETH_09.lean) |
| ETH-10 | ETH-10-a · The Ethics of Eating Animals | [`Philosophy/ETH/ETH_10.lean`](../lean/Philosophy/ETH/ETH_10.lean) |
| ETH-15 | ETH-15-a · There Are No Genuine Moral Dilemmas | [`Philosophy/ETH/ETH_15.lean`](../lean/Philosophy/ETH/ETH_15.lean) |
| ETH-18 | ETH-18-a · The Duty to Rescue and Its Limits | [`Philosophy/ETH/ETH_18.lean`](../lean/Philosophy/ETH/ETH_18.lean) |
| ETH-20 | ETH-20-a · The Asymmetry Argument Fails | [`Philosophy/ETH/ETH_20.lean`](../lean/Philosophy/ETH/ETH_20.lean) |
| ETH-24 | ETH-24-a · The Moral Status of Artificial Systems | [`Philosophy/ETH/ETH_24.lean`](../lean/Philosophy/ETH/ETH_24.lean) |
| ETH-26 | ETH-26-a · Punishment as Communication | [`Philosophy/ETH/ETH_26.lean`](../lean/Philosophy/ETH/ETH_26.lean) |
| ETH-28 | ETH-28-a · The Demandingness of Morality | [`Philosophy/ETH/ETH_28.lean`](../lean/Philosophy/ETH/ETH_28.lean) |
| MTE-01 | MTE-01-a · Moral Realism Established | [`Philosophy/MTE/MTE_01.lean`](../lean/Philosophy/MTE/MTE_01.lean) |
| MTE-02 | MTE-02-a · Objectivity Without Absoluteness | [`Philosophy/MTE/MTE_02.lean`](../lean/Philosophy/MTE/MTE_02.lean) |
| MTE-03 | MTE-03-a · The Frege-Geach Problem Solved | [`Philosophy/MTE/MTE_03.lean`](../lean/Philosophy/MTE/MTE_03.lean) |
| MTE-04 | MTE-04-a · Why Be Moral? A Two-Case Argument | [`Philosophy/MTE/MTE_04.lean`](../lean/Philosophy/MTE/MTE_04.lean) |
| MTE-05 | MTE-05-a · Companions in Guilt and the Error Theory | [`Philosophy/MTE/MTE_05.lean`](../lean/Philosophy/MTE/MTE_05.lean) |
| MTE-09 | MTE-09-a · Debunking the Debunkers | [`Philosophy/MTE/MTE_09.lean`](../lean/Philosophy/MTE/MTE_09.lean) |
| MTE-11 | MTE-11-a · Reasons First | [`Philosophy/MTE/MTE_11.lean`](../lean/Philosophy/MTE/MTE_11.lean) |
| MTE-16 | MTE-16-a · Expected Choiceworthiness, Variance-Normalized | [`Philosophy/MTE/MTE_16.lean`](../lean/Philosophy/MTE/MTE_16.lean) |
| MTE-17 | MTE-17-a · The Collapse of Quasi-Realism | [`Philosophy/MTE/MTE_17.lean`](../lean/Philosophy/MTE/MTE_17.lean) |
| MTE-19 | MTE-19-a · Moral Progress Is Measurable | [`Philosophy/MTE/MTE_19.lean`](../lean/Philosophy/MTE/MTE_19.lean) |
| EPI-01 | EPI-01-a · The Analysis of Knowledge | [`Philosophy/EPI/EPI_01.lean`](../lean/Philosophy/EPI/EPI_01.lean) |
| EPI-02 | EPI-02-a · A Defence of Moore's Proof | [`Philosophy/EPI/EPI_02.lean`](../lean/Philosophy/EPI/EPI_02.lean) |
| EPI-03 | EPI-03-a · The Problem of Induction | [`Philosophy/EPI/EPI_03.lean`](../lean/Philosophy/EPI/EPI_03.lean) |
| EPI-05 | EPI-05-a · The Structure of Justification | [`Philosophy/EPI/EPI_05.lean`](../lean/Philosophy/EPI/EPI_05.lean) |
| EPI-07 | EPI-07-a · Moderate Conciliationism | [`Philosophy/EPI/EPI_07.lean`](../lean/Philosophy/EPI/EPI_07.lean) |
| EPI-08 | EPI-08-a · Testimony Transmits Knowledge | [`Philosophy/EPI/EPI_08.lean`](../lean/Philosophy/EPI/EPI_08.lean) |
| EPI-10 | EPI-10-a · The Preface Paradox and the Present Collection | [`Philosophy/EPI/EPI_10.lean`](../lean/Philosophy/EPI/EPI_10.lean) |
| EPI-13 | EPI-13-a · Contextualism and Scepticism | [`Philosophy/EPI/EPI_13.lean`](../lean/Philosophy/EPI/EPI_13.lean) |
| EPI-16 | EPI-16-a · The Epistemic Costs of Prejudice | [`Philosophy/EPI/EPI_16.lean`](../lean/Philosophy/EPI/EPI_16.lean) |
| EPI-17 | EPI-17-a · Uniqueness Defended | [`Philosophy/EPI/EPI_17.lean`](../lean/Philosophy/EPI/EPI_17.lean) |
| EPI-18 | EPI-18-a · Sleeping Beauty: The Thirder Solution | [`Philosophy/EPI/EPI_18.lean`](../lean/Philosophy/EPI/EPI_18.lean) |
| EPI-19 | EPI-19-a · Phenomenal Conservatism Defended | [`Philosophy/EPI/EPI_19.lean`](../lean/Philosophy/EPI/EPI_19.lean) |
| EPI-20 | EPI-20-a · Closure Holds | [`Philosophy/EPI/EPI_20.lean`](../lean/Philosophy/EPI/EPI_20.lean) |
| MND-01 | MND-01-a · On the Hard Problem of Consciousness | [`Philosophy/MND/MND_01.lean`](../lean/Philosophy/MND/MND_01.lean) |
| MND-02 | MND-02-a · Physicalism and Hempel's Dilemma | [`Philosophy/MND/MND_02.lean`](../lean/Philosophy/MND/MND_02.lean) |
| MND-04 | MND-04-a · Mary's Room and the Ability Hypothesis | [`Philosophy/MND/MND_04.lean`](../lean/Philosophy/MND/MND_04.lean) |
| MND-05 | MND-05-a · Zombies Are Conceivable but Impossible | [`Philosophy/MND/MND_05.lean`](../lean/Philosophy/MND/MND_05.lean) |
| MND-07 | MND-07-a · The Systems Reply Vindicated | [`Philosophy/MND/MND_07.lean`](../lean/Philosophy/MND/MND_07.lean) |
| MND-11 | MND-11-a · Mental Causes Are Proportional | [`Philosophy/MND/MND_11.lean`](../lean/Philosophy/MND/MND_11.lean) |
| MND-13 | MND-13-a · Eliminativism Is Self-Undermining | [`Philosophy/MND/MND_13.lean`](../lean/Philosophy/MND/MND_13.lean) |
| MND-18 | MND-18-a · The Combination Problem Is Unsolvable | [`Philosophy/MND/MND_18.lean`](../lean/Philosophy/MND/MND_18.lean) |
| MND-21 | MND-21-a · Computation Without a Central Processor | [`Philosophy/MND/MND_21.lean`](../lean/Philosophy/MND/MND_21.lean) |
| MND-26 | MND-26-a · The Mind-Body Problem: A Synthesis | [`Philosophy/MND/MND_26.lean`](../lean/Philosophy/MND/MND_26.lean) |
| LNG-01 | LNG-01-a · On Meaning | [`Philosophy/LNG/LNG_01.lean`](../lean/Philosophy/LNG/LNG_01.lean) |
| LNG-02 | LNG-02-a · Causal Reference With Descriptive Backup | [`Philosophy/LNG/LNG_02.lean`](../lean/Philosophy/LNG/LNG_02.lean) |
| LNG-03 | LNG-03-a · The Present King of France Is Not Bald | [`Philosophy/LNG/LNG_03.lean`](../lean/Philosophy/LNG/LNG_03.lean) |
| LNG-05 | LNG-05-a · Meaning Facts as Primitive | [`Philosophy/LNG/LNG_05.lean`](../lean/Philosophy/LNG/LNG_05.lean) |
| LNG-07 | LNG-07-a · Against Private Language | [`Philosophy/LNG/LNG_07.lean`](../lean/Philosophy/LNG/LNG_07.lean) |
| LNG-10 | LNG-10-a · Deflationism Defended | [`Philosophy/LNG/LNG_10.lean`](../lean/Philosophy/LNG/LNG_10.lean) |
| LNG-12 | LNG-12-a · The Sorites and Sharp Boundaries | [`Philosophy/LNG/LNG_12.lean`](../lean/Philosophy/LNG/LNG_12.lean) |
| LNG-14 | LNG-14-a · Fictional Characters as Abstract Artefacts | [`Philosophy/LNG/LNG_14.lean`](../lean/Philosophy/LNG/LNG_14.lean) |
| LNG-17 | LNG-17-a · Structured Propositions | [`Philosophy/LNG/LNG_17.lean`](../lean/Philosophy/LNG/LNG_17.lean) |
| LNG-18 | LNG-18-a · Self-Reference Without Paradox | [`Philosophy/LNG/LNG_18.lean`](../lean/Philosophy/LNG/LNG_18.lean) |
| LNG-20 | LNG-20-a · Conditionals Without Truth Values | [`Philosophy/LNG/LNG_20.lean`](../lean/Philosophy/LNG/LNG_20.lean) |
| LOG-01 | LOG-01-a · The Liar Resolved | [`Philosophy/LOG/LOG_01.lean`](../lean/Philosophy/LOG/LOG_01.lean) |
| LOG-02 | LOG-02-a · Logical Monism | [`Philosophy/LOG/LOG_02.lean`](../lean/Philosophy/LOG/LOG_02.lean) |
| LOG-03 | LOG-03-a · Against Dialetheism | [`Philosophy/LOG/LOG_03.lean`](../lean/Philosophy/LOG/LOG_03.lean) |
| LOG-04 | LOG-04-a · Curry's Paradox and the Failure of Contraction | [`Philosophy/LOG/LOG_04.lean`](../lean/Philosophy/LOG/LOG_04.lean) |
| LOG-06 | LOG-06-a · Logical Consequence and the Actual World | [`Philosophy/LOG/LOG_06.lean`](../lean/Philosophy/LOG/LOG_06.lean) |
| LOG-07 | LOG-07-a · In Defence of the Material Conditional | [`Philosophy/LOG/LOG_07.lean`](../lean/Philosophy/LOG/LOG_07.lean) |
| LOG-08 | LOG-08-a · Absolute Generality Defended | [`Philosophy/LOG/LOG_08.lean`](../lean/Philosophy/LOG/LOG_08.lean) |
| LOG-09 | LOG-09-a · Second-Order Logic Is Logic | [`Philosophy/LOG/LOG_09.lean`](../lean/Philosophy/LOG/LOG_09.lean) |
| LOG-11 | LOG-11-a · The Surprise Examination | [`Philosophy/LOG/LOG_11.lean`](../lean/Philosophy/LOG/LOG_11.lean) |
| LOG-12 | LOG-12-a · Identity Is Absolute | [`Philosophy/LOG/LOG_12.lean`](../lean/Philosophy/LOG/LOG_12.lean) |
| LOG-13 | LOG-13-a · Distributivity Survives Quantum Mechanics | [`Philosophy/LOG/LOG_13.lean`](../lean/Philosophy/LOG/LOG_13.lean) |
| LOG-16 | LOG-16-a · The Logical Constants and Permutation Invariance | [`Philosophy/LOG/LOG_16.lean`](../lean/Philosophy/LOG/LOG_16.lean) |
| LOG-17 | LOG-17-a · Hempel's Ravens and Bayesian Confirmation | [`Philosophy/LOG/LOG_17.lean`](../lean/Philosophy/LOG/LOG_17.lean) |
| LOG-18 | LOG-18-a · What the Tortoise Said to Achilles, Revisited | [`Philosophy/LOG/LOG_18.lean`](../lean/Philosophy/LOG/LOG_18.lean) |
| LOG-19 | LOG-19-a · Fitch's Paradox Accepted | [`Philosophy/LOG/LOG_19.lean`](../lean/Philosophy/LOG/LOG_19.lean) |
| LOG-20 | LOG-20-a · Completeness and Its Limits | [`Philosophy/LOG/LOG_20.lean`](../lean/Philosophy/LOG/LOG_20.lean) |
| SCI-01 | SCI-01-a · The Demarcation Problem Revisited | [`Philosophy/SCI/SCI_01.lean`](../lean/Philosophy/SCI/SCI_01.lean) |
| SCI-02 | SCI-02-a · Scientific Realism Defended | [`Philosophy/SCI/SCI_02.lean`](../lean/Philosophy/SCI/SCI_02.lean) |
| SCI-07 | SCI-07-a · The Falsifiability Criterion Is Not Self-Refuting | [`Philosophy/SCI/SCI_07.lean`](../lean/Philosophy/SCI/SCI_07.lean) |
| SCI-09 | SCI-09-a · The Everett Interpretation Defended | [`Philosophy/SCI/SCI_09.lean`](../lean/Philosophy/SCI/SCI_09.lean) |
| SCI-10 | SCI-10-a · Idealization and Representation | [`Philosophy/SCI/SCI_10.lean`](../lean/Philosophy/SCI/SCI_10.lean) |
| SCI-12 | SCI-12-a · Bayesian Confirmation and Old Evidence | [`Philosophy/SCI/SCI_12.lean`](../lean/Philosophy/SCI/SCI_12.lean) |
| SCI-16 | SCI-16-a · From Correlation to Causation | [`Philosophy/SCI/SCI_16.lean`](../lean/Philosophy/SCI/SCI_16.lean) |
| SCI-19 | SCI-19-a · Self-Correction in Science | [`Philosophy/SCI/SCI_19.lean`](../lean/Philosophy/SCI/SCI_19.lean) |
| SCI-21 | SCI-21-a · Survival of the Fittest Is Not a Tautology | [`Philosophy/SCI/SCI_21.lean`](../lean/Philosophy/SCI/SCI_21.lean) |
| SCI-22 | SCI-22-a · The Scientific Status of Machine-Generated Results | [`Philosophy/SCI/SCI_22.lean`](../lean/Philosophy/SCI/SCI_22.lean) |
| POL-01 | POL-01-a · On Justice | [`Philosophy/POL/POL_01.lean`](../lean/Philosophy/POL/POL_01.lean) |
| POL-02 | POL-02-a · The Legitimacy of the State | [`Philosophy/POL/POL_02.lean`](../lean/Philosophy/POL/POL_02.lean) |
| POL-04 | POL-04-a · Democracy, Doubly Justified | [`Philosophy/POL/POL_04.lean`](../lean/Philosophy/POL/POL_04.lean) |
| POL-06 | POL-06-a · Property Is Not Theft | [`Philosophy/POL/POL_06.lean`](../lean/Philosophy/POL/POL_06.lean) |
| POL-11 | POL-11-a · The Social Contract as Implicit Framework | [`Philosophy/POL/POL_11.lean`](../lean/Philosophy/POL/POL_11.lean) |
| POL-16 | POL-16-a · The Paradox of Tolerance | [`Philosophy/POL/POL_16.lean`](../lean/Philosophy/POL/POL_16.lean) |
| AES-01 | AES-01-a · What Art Is | [`Philosophy/AES/AES_01.lean`](../lean/Philosophy/AES/AES_01.lean) |
| AES-05 | AES-05-a · Quasi-Emotions and the Paradox of Fiction | [`Philosophy/AES/AES_05.lean`](../lean/Philosophy/AES/AES_05.lean) |
| ACT-01 | ACT-01-a · On Free Will | [`Philosophy/ACT/ACT_01.lean`](../lean/Philosophy/ACT/ACT_01.lean) |
| ACT-02 | ACT-02-a · Frankfurt Cases Vindicated | [`Philosophy/ACT/ACT_02.lean`](../lean/Philosophy/ACT/ACT_02.lean) |
| ACT-05 | ACT-05-a · Libet Does Not Refute Free Will | [`Philosophy/ACT/ACT_05.lean`](../lean/Philosophy/ACT/ACT_05.lean) |
| ACT-08 | ACT-08-a · The Basic Argument Fails | [`Philosophy/ACT/ACT_08.lean`](../lean/Philosophy/ACT/ACT_08.lean) |
| ACT-12 | ACT-12-a · External Reasons Exist | [`Philosophy/ACT/ACT_12.lean`](../lean/Philosophy/ACT/ACT_12.lean) |
| ACT-15 | ACT-15-a · Luck and Libertarian Freedom | [`Philosophy/ACT/ACT_15.lean`](../lean/Philosophy/ACT/ACT_15.lean) |
| PID-01 | PID-01-a · On Personal Identity | [`Philosophy/PID/PID_01.lean`](../lean/Philosophy/PID/PID_01.lean) |
| PID-02 | PID-02-a · Teletransportation and Extrinsic Survival | [`Philosophy/PID/PID_02.lean`](../lean/Philosophy/PID/PID_02.lean) |
| PID-05 | PID-05-a · Animalism Defended | [`Philosophy/PID/PID_05.lean`](../lean/Philosophy/PID/PID_05.lean) |
| PID-10 | PID-10-a · Disembodied Persons | [`Philosophy/PID/PID_10.lean`](../lean/Philosophy/PID/PID_10.lean) |
| PID-11 | PID-11-a · Perdurantism and Persons | [`Philosophy/PID/PID_11.lean`](../lean/Philosophy/PID/PID_11.lean) |
| TSM-01 | TSM-01-a · On the Reality of Time | [`Philosophy/TSM/TSM_01.lean`](../lean/Philosophy/TSM/TSM_01.lean) |
| TSM-02 | TSM-02-a · Against Temporal Passage | [`Philosophy/TSM/TSM_02.lean`](../lean/Philosophy/TSM/TSM_02.lean) |
| TSM-04 | TSM-04-a · Time Travel and the Grandfather Paradox | [`Philosophy/TSM/TSM_04.lean`](../lean/Philosophy/TSM/TSM_04.lean) |
| TSM-07 | TSM-07-a · Possible Worlds as Abstract Objects | [`Philosophy/TSM/TSM_07.lean`](../lean/Philosophy/TSM/TSM_07.lean) |
| TSM-13 | TSM-13-a · Zeno's Achilles and Convergent Series | [`Philosophy/TSM/TSM_13.lean`](../lean/Philosophy/TSM/TSM_13.lean) |
| EXI-01 | EXI-01-a · On the Meaning of Life | [`Philosophy/EXI/EXI_01.lean`](../lean/Philosophy/EXI/EXI_01.lean) |
| PHE-01 | PHE-01-a · The Duration of the Epoché | [`Philosophy/PHE/PHE_01.lean`](../lean/Philosophy/PHE/PHE_01.lean) |
| PHE-05 | PHE-05-a · The Thickness of the Living Present | [`Philosophy/PHE/PHE_05.lean`](../lean/Philosophy/PHE/PHE_05.lean) |
| PHE-07 | PHE-07-a · Anticipatory Resoluteness as a Limit Concept | [`Philosophy/PHE/PHE_07.lean`](../lean/Philosophy/PHE/PHE_07.lean) |
| PHE-11 | PHE-11-a · The World as Horizon of Horizons | [`Philosophy/PHE/PHE_11.lean`](../lean/Philosophy/PHE/PHE_11.lean) |
| PHE-13 | PHE-13-a · The Infinite Demand of the Face | [`Philosophy/PHE/PHE_13.lean`](../lean/Philosophy/PHE/PHE_13.lean) |
| PHE-18 | PHE-18-a · Philosophy as Rigorous Science, Circularly Grounded | [`Philosophy/PHE/PHE_18.lean`](../lean/Philosophy/PHE/PHE_18.lean) |
| PHE-19 | PHE-19-a · The Impossible Gift and the Present Collection | [`Philosophy/PHE/PHE_19.lean`](../lean/Philosophy/PHE/PHE_19.lean) |
| PHE-20 | PHE-20-a · The Irreducible Residue | [`Philosophy/PHE/PHE_20.lean`](../lean/Philosophy/PHE/PHE_20.lean) |
| PHE-22 | PHE-22-a · On the Impossibility of Machine Epoché | [`Philosophy/PHE/PHE_22.lean`](../lean/Philosophy/PHE/PHE_22.lean) |
| MTH-01 | MTH-01-a · On the Existence of Numbers | [`Philosophy/MTH/MTH_01.lean`](../lean/Philosophy/MTH/MTH_01.lean) |
| MTH-02 | MTH-02-a · Benacerraf's Problem Answered | [`Philosophy/MTH/MTH_02.lean`](../lean/Philosophy/MTH/MTH_02.lean) |
| MTH-04 | MTH-04-a · Neo-Logicism Vindicated | [`Philosophy/MTH/MTH_04.lean`](../lean/Philosophy/MTH/MTH_04.lean) |
| MTH-05 | MTH-05-a · Gödel's Theorem and the Mechanist Thesis | [`Philosophy/MTH/MTH_05.lean`](../lean/Philosophy/MTH/MTH_05.lean) |
| MTH-06 | MTH-06-a · The Continuum Hypothesis Is False | [`Philosophy/MTH/MTH_06.lean`](../lean/Philosophy/MTH/MTH_06.lean) |
| MTH-07 | MTH-07-a · Excluded Middle in Mathematics | [`Philosophy/MTH/MTH_07.lean`](../lean/Philosophy/MTH/MTH_07.lean) |
| MTH-09 | MTH-09-a · What Is a Proof? | [`Philosophy/MTH/MTH_09.lean`](../lean/Philosophy/MTH/MTH_09.lean) |
| MTH-12 | MTH-12-a · Unknowable Mathematical Truths | [`Philosophy/MTH/MTH_12.lean`](../lean/Philosophy/MTH/MTH_12.lean) |
| MTH-16 | MTH-16-a · Against Fictionalism | [`Philosophy/MTH/MTH_16.lean`](../lean/Philosophy/MTH/MTH_16.lean) |
| MTH-18 | MTH-18-a · Can Machines Do Philosophy? | [`Philosophy/MTH/MTH_18.lean`](../lean/Philosophy/MTH/MTH_18.lean) |

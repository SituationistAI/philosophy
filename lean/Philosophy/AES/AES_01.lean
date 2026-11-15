/-
AES-01 · What Art Is
Formalization of Lemma 3.1, Theorems 3.2, 3.3, 3.6 and 3.9, Corollary 3.4,
Proposition 3.5, and of the bounded checks of Propositions 5.4, C.1 and D.1.

Part I (the logical skeleton). Episodes are objects at a stage of their
history, relative to an artworld. Presentation (Definition 2.1), critical
uptake (Definition 2.2), adverse and favourable assessment (Definition 2.4),
market uptake (Definition 2.5) and an agent's decision that an episode is art
are primitives. The institutional condition (Principle P1), the clause of
Definition 2.2 on which adverse assessment is uptake, and Assumptions 2.7–2.9
are axioms.

Part II (the bounded checks). A finite encoding of states (Appendix C) and of
histories of artworld events (Appendix D), with the verdict function of the
manuscript; the checks are proved by exhaustive case analysis and `decide`.

What this file establishes. Given P1, the adverse-assessment clause and
Assumptions 2.7–2.9: presentation is necessary but not sufficient for art
status; adverse uptake suffices for it; status does not require favourable
assessment; market uptake is neither necessary nor sufficient; and no single
agent's decision suffices. Part II establishes that the encoded verdict
function satisfies the corresponding checks on every state and on every
history of length three.

What it does not establish. It does not establish Principle P1 or the
assumptions, which are defended in Sections 2, 3 and 7 of the manuscript; it
does not establish that the encoding of any catalogued case is correct; and it
says nothing about the value of any work (Remark 2.10).
-/

namespace Philosophy.AES_01

/-! ## Part I: the logical skeleton -/

/-- Episodes: objects at a stage of their history, relative to an artworld. -/
axiom Episode : Type

/-- Participants in artworlds, and other agents. -/
axiom Agent : Type

/-- Definition 2.1. The episode is presented as art within an artworld. -/
axiom Presented : Episode → Prop

/-- Definition 2.2. The presented object receives critical uptake. -/
axiom TakenUp : Episode → Prop

/-- Definition 2.4. The critical practice assesses the object unfavourably. -/
axiom AssessedAdversely : Episode → Prop

/-- Definition 2.4. The critical practice assesses the object favourably. -/
axiom AssessedFavourably : Episode → Prop

/-- Definition 2.5. The object receives market uptake. -/
axiom MarketUptake : Episode → Prop

/-- `Decides a e`: agent `a` decides that the object is art (by declaring,
conferring, signing, certifying, or presenting it). -/
axiom Decides : Agent → Episode → Prop

/-- Art status at the episode. -/
axiom Art : Episode → Prop

/-- Principle P1 (institutional condition). An episode is art iff it is
presented as art within an artworld and receives critical uptake there. -/
axiom institutional : ∀ e, Art e ↔ Presented e ∧ TakenUp e

/-- Definition 2.2, with Definition 2.4. Adverse assessment of a presented
object as a candidate is critical uptake. -/
axiom adverse_is_uptake : ∀ e, Presented e → AssessedAdversely e → TakenUp e

/-- Assumption 2.7 (offered and ignored). Some presented objects receive no
critical uptake. -/
axiom offered_and_ignored : ∃ e, Presented e ∧ ¬ TakenUp e

/-- Assumption 2.8 (no participant commands the practice). For every agent
there is an object that the agent decides is art and presents, and that the
practice does not take up. -/
axiom no_command : ∀ a : Agent, ∃ e, Decides a e ∧ Presented e ∧ ¬ TakenUp e

/-- Assumption 2.9 (market and criticism come apart). Some presented object
receives market uptake without critical uptake, and some object taken up
receives no market uptake. -/
axiom market_apart :
    (∃ e, MarketUptake e ∧ Presented e ∧ ¬ TakenUp e) ∧
    (∃ e, ¬ MarketUptake e ∧ Presented e ∧ TakenUp e)

/-- Lemma 3.1. Presentation is necessary for art status. -/
theorem presentation_necessary : ∀ e, Art e → Presented e :=
  fun e h => ((institutional e).mp h).1

/-- Theorem 3.2. Presentation alone does not suffice for art status. -/
theorem presentation_insufficient : ¬ ∀ e, Presented e → Art e := by
  intro h
  obtain ⟨e, hp, hn⟩ := offered_and_ignored
  exact hn ((institutional e).mp (h e hp)).2

/-- Theorem 3.3. Adverse uptake suffices: a presented object assessed
unfavourably by the critical practice is art. -/
theorem adverse_suffices : ∀ e, Presented e → AssessedAdversely e → Art e :=
  fun e hp ha => (institutional e).mpr ⟨hp, adverse_is_uptake e hp ha⟩

/-- Corollary 3.4. Status and merit come apart: an object that is presented
and assessed only unfavourably is art without favourable assessment. -/
theorem status_without_merit :
    ∀ e, Presented e → AssessedAdversely e → ¬ AssessedFavourably e →
      Art e ∧ ¬ AssessedFavourably e :=
  fun e hp ha hf => ⟨adverse_suffices e hp ha, hf⟩

/-- Proposition 3.5. Market uptake is neither sufficient (with presentation)
nor necessary for art status. -/
theorem market_neither :
    ¬ (∀ e, Presented e → MarketUptake e → Art e) ∧
    ¬ (∀ e, Art e → MarketUptake e) := by
  obtain ⟨⟨e, hm, hp, hn⟩, ⟨e', hm', hp', ht'⟩⟩ := market_apart
  constructor
  · intro h
    exact hn ((institutional e).mp (h e hp hm)).2
  · intro h
    exact hm' (h e' ((institutional e').mpr ⟨hp', ht'⟩))

/-- Theorem 3.6. No single agent's decision suffices for art status. -/
theorem no_single_agent : ∀ a : Agent, ¬ ∀ e, Decides a e → Art e := by
  intro a h
  obtain ⟨e, hd, _, hn⟩ := no_command a
  exact hn ((institutional e).mp (h e hd)).2

/-- Theorem 3.6, second form: there is no agent whose decisions confer art
status. -/
theorem no_conferring_agent : ¬ ∃ a : Agent, ∀ e, Decides a e → Art e :=
  fun ⟨a, h⟩ => no_single_agent a h

/-- Theorem 3.9 (criterion theorem, formal core). Presentation is necessary
and not sufficient, adverse uptake suffices, market uptake is neither
necessary nor sufficient, and no agent's decision suffices. -/
theorem criterion :
    (∀ e, Art e → Presented e) ∧
    (¬ ∀ e, Presented e → Art e) ∧
    (∀ e, Presented e → AssessedAdversely e → Art e) ∧
    (¬ (∀ e, Presented e → MarketUptake e → Art e) ∧
      ¬ (∀ e, Art e → MarketUptake e)) ∧
    (∀ a : Agent, ¬ ∀ e, Decides a e → Art e) :=
  ⟨presentation_necessary, presentation_insufficient, adverse_suffices,
    market_neither, no_single_agent⟩

/-! ## Part II: the bounded checks of Appendices C and D -/

/-- Presentation values of the encoding (Appendix A). -/
inductive Pres where
  | no | maker | other
  deriving DecidableEq, Repr

/-- Critical-uptake values of the encoding (Definition 2.4). -/
inductive Crit where
  | none | curio | refused | adverse | favourable | mixed | divided
  deriving DecidableEq, Repr

/-- Market-uptake values of the encoding (Definition 2.5). -/
inductive Mkt where
  | none | sold | high
  deriving DecidableEq, Repr

/-- Verdicts: art, contested, candidate (presented, not taken up), not
presented, no artworld at the index. -/
inductive Verdict where
  | art | contested | candidate | notPresented | noArtworld
  deriving DecidableEq, Repr

/-- An encoded state (Appendix C). -/
structure State where
  aw : Bool
  pres : Pres
  crit : Crit
  mkt : Mkt
  decl : Bool

/-- The verdict function of the generator (Appendix C), implementing
Principle P1 with Definitions 2.1–2.5. -/
def verdict (s : State) : Verdict :=
  if s.aw = false then .noArtworld
  else match s.pres with
    | .no => .notPresented
    | _ => match s.crit with
      | .none | .curio | .refused => .candidate
      | .adverse | .favourable | .mixed => .art
      | .divided => .contested

/-- Proposition C.1 (i). On every encoded state, presentation without
engagement as a candidate never yields art. -/
theorem census_presentation_insufficient :
    ∀ s : State, (s.crit = .none ∨ s.crit = .curio ∨ s.crit = .refused) →
      verdict s ≠ .art := by
  intro ⟨aw, p, c, m, d⟩ h
  cases aw <;> cases p <;> cases c <;> simp_all [verdict]

/-- Proposition C.1 (ii). On every state within an artworld in which the
object is presented, adverse uptake yields art, and gives the same verdict as
favourable uptake. -/
theorem census_adverse :
    ∀ s : State, s.aw = true → s.pres ≠ .no →
      verdict { s with crit := .adverse } = .art ∧
      verdict { s with crit := .adverse } = verdict { s with crit := .favourable } := by
  intro ⟨aw, p, c, m, d⟩ ha hp
  cases aw <;> cases p <;> simp_all [verdict]

/-- Proposition 5.4 (openness), on the encoding. Every state within an
artworld in which the object is presented has a response of the critical
practice under which it is art. -/
theorem census_open :
    ∀ s : State, s.aw = true → s.pres ≠ .no →
      ∃ c : Crit, verdict { s with crit := c } = .art :=
  fun s ha hp => ⟨.adverse, (census_adverse s ha hp).1⟩

/-- Proposition C.1 (iii). The verdict is independent of market uptake and of
single declarations. (It holds by the form of the verdict function, which is
what Proposition 3.5 and Theorem 3.6 require of it.) -/
theorem census_independent :
    ∀ (s : State) (m : Mkt) (d : Bool),
      verdict { s with mkt := m, decl := d } = verdict s := by
  intro ⟨aw, p, c, m0, d0⟩ m d
  rfl

/-- Proposition C.1 (iv). Without presentation, no state is art. -/
theorem census_presentation_necessary :
    ∀ s : State, s.pres = .no → verdict s ≠ .art := by
  intro ⟨aw, p, c, m, d⟩ h
  cases aw <;> cases p <;> simp_all [verdict]

/-- Events of a history (Appendix D). -/
inductive Ev where
  | nothing | present | declare | refuse | sell | adverse | favourable | divided
  deriving DecidableEq, Repr

/-- Status along a history: flags for presented, engaged and divided. -/
structure Flags where
  pres : Bool
  eng : Bool
  div : Bool

def step (f : Flags) : Ev → Flags
  | .present => { f with pres := true }
  | .adverse => if f.pres then { f with eng := true } else f
  | .favourable => if f.pres then { f with eng := true } else f
  | .divided => if f.pres then { f with div := true } else f
  | _ => f

def status (f : Flags) : Verdict :=
  if f.pres = false then .notPresented
  else if f.eng then .art
  else if f.div then .contested
  else .candidate

/-- The trajectory of statuses along a history (Appendix D). -/
def traj : Flags → List Ev → List Verdict
  | _, [] => []
  | f, e :: es => let g := step f e; status g :: traj g es

def start : Flags := ⟨false, false, false⟩

def isEngage : Ev → Bool
  | .adverse | .favourable => true
  | _ => false

/-- Replace sales, declarations and refusals by idle events. -/
def idleSDR : Ev → Ev
  | .sell | .declare | .refuse => .nothing
  | e => e

/-- Exchange adverse and favourable engagement. -/
def swapAF : Ev → Ev
  | .adverse => .favourable
  | .favourable => .adverse
  | e => e

/-- Once art, art at every later stage. -/
def persistent : List Verdict → Bool
  | [] => true
  | .art :: rest => rest.all (· == .art)
  | _ :: rest => persistent rest

/-- The checks H1, H3, H4, H5, H6 of Appendix D on one history. -/
def check (h : List Ev) : Bool :=
  let t := traj start h
  (h.any isEngage || !(t.contains .art)) &&
  (traj start (h.map idleSDR) == t) &&
  persistent t &&
  (traj start (h.map swapAF) == t)

/-- Proposition D.1. Every history of length three (8 × 8 × 8 = 512
histories) satisfies the checks:
no art without favourable or adverse engagement; sales, declarations and
refusals change nothing; status persists; adverse and favourable engagement
are interchangeable. -/
theorem histories_three : ∀ a b c : Ev, check [a, b, c] = true := by
  intro a b c
  cases a <;> cases b <;> cases c <;> rfl

end Philosophy.AES_01

#print axioms Philosophy.AES_01.criterion
#print axioms Philosophy.AES_01.no_single_agent
#print axioms Philosophy.AES_01.histories_three

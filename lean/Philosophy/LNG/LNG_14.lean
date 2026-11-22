/-
LNG-14 · Fictional Characters as Abstract Artefacts
Formalization of Theorem 3.1 and Corollaries 3.2–3.4.

What this file establishes. If a sentence of the form "n is a fictional
character created by a" is literally true (Assumption 2.3), and literal
truth of an atomic predication requires reference (Assumption 2.4), then,
given that what authors create are artefacts (Assumption 2.5) and that
characters are not concrete (Assumption 2.6), the name refers to an abstract
artefact created by a. Applied to "Holmes": the referent exists in the sense
of MET-24 (something is identical to it), is not a detective, though the
stories ascribe detection to it (Assumptions 2.7 and 2.8), and nothing
concrete is Holmes.

It does not establish the assumptions, in particular that critical discourse
is literally true, which is defended in Sections 1 and 5 of the manuscript.
-/

namespace Philosophy.LNG_14

/-- Everything there is. -/
axiom Thing : Type

/-- Names. -/
axiom Name : Type

/-- Reference: `Ref n x`, the name `n` refers to `x`. -/
axiom Ref : Name → Thing → Prop

/-- Being a fictional character. -/
axiom Character : Thing → Prop

/-- `CreatedBy x a`: `x` was created by the author `a`. -/
axiom CreatedBy : Thing → Thing → Prop

/-- Being concrete (Definition 2.2). -/
axiom Concrete : Thing → Prop

/-- Being an artefact (Definition 2.2). -/
axiom Artefact : Thing → Prop

/-- Being a detective, in the plain sense. -/
axiom Detective : Thing → Prop

/-- Being ascribed detection by the Holmes stories (Definition 2.1). -/
axiom AscribedDetective : Thing → Prop

/-- Definition 2.2. Abstract: not concrete. -/
def Abstract (x : Thing) : Prop := ¬ Concrete x

/-- Existence as in MET-24: something is identical to it. -/
def Exists (x : Thing) : Prop := ∃ y, y = x

/-- Assumption 2.4 (first part). The literal truth condition of "n is a
character created by a". -/
def CriticalTrue (n : Name) (a : Thing) : Prop :=
  ∃ x, Ref n x ∧ Character x ∧ CreatedBy x a

axiom holmes : Name
axiom doyle : Thing

/-- Assumption 2.3. "Holmes is a fictional character created by Conan Doyle"
is literally true. -/
axiom critical_truth : CriticalTrue holmes doyle

/-- Assumption 2.4 (second part). A name refers to at most one thing. -/
axiom ref_unique : ∀ n x y, Ref n x → Ref n y → x = y

/-- Assumption 2.5. What an author creates is an artefact. -/
axiom creation : ∀ x a, CreatedBy x a → Artefact x

/-- Assumption 2.6. No fictional character is concrete. -/
axiom characters_abstract : ∀ x, Character x → ¬ Concrete x

/-- Assumption 2.7. Detectives, in the plain sense, are concrete. -/
axiom detectives_concrete : ∀ x, Detective x → Concrete x

/-- Assumption 2.8. The stories ascribe detection to the referent of
"Holmes". -/
axiom ascription : ∀ x, Ref holmes x → AscribedDetective x

/-- Theorem 3.1. A name of which a sentence of the form "n is a character
created by a" is literally true refers to an abstract artefact created
by a. -/
theorem abstract_artefact (n : Name) (a : Thing) (h : CriticalTrue n a) :
    ∃ x, Ref n x ∧ Abstract x ∧ Artefact x ∧ CreatedBy x a :=
  let ⟨x, hr, hc, hcr⟩ := h
  ⟨x, hr, characters_abstract x hc, creation x a hcr, hcr⟩

/-- Corollary 3.2. "Holmes" refers to an abstract artefact created by Conan
Doyle, which exists. -/
theorem holmes_refers :
    ∃ x, Ref holmes x ∧ Abstract x ∧ Artefact x ∧ CreatedBy x doyle ∧ Exists x :=
  let ⟨x, hr, ha, hart, hc⟩ := abstract_artefact holmes doyle critical_truth
  ⟨x, hr, ha, hart, hc, ⟨x, rfl⟩⟩

/-- Corollary 3.3. Whatever "Holmes" refers to is not a detective, and is
ascribed detection by the stories. -/
theorem not_detective (x : Thing) (hx : Ref holmes x) :
    ¬ Detective x ∧ AscribedDetective x := by
  obtain ⟨y, hy, hc, _⟩ := critical_truth
  have hxy : x = y := ref_unique holmes x y hx hy
  subst hxy
  exact ⟨fun hd => characters_abstract x hc (detectives_concrete x hd),
    ascription x hx⟩

/-- Corollary 3.4. Nothing concrete is Holmes. -/
theorem no_concrete_holmes : ¬ ∃ x, Ref holmes x ∧ Concrete x := by
  intro ⟨x, hx, hc⟩
  obtain ⟨y, hy, hch, _⟩ := critical_truth
  have hxy : x = y := ref_unique holmes x y hx hy
  subst hxy
  exact characters_abstract x hch hc

end Philosophy.LNG_14

#print axioms Philosophy.LNG_14.abstract_artefact
#print axioms Philosophy.LNG_14.holmes_refers
#print axioms Philosophy.LNG_14.not_detective

/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import NeuralArtifacts.CertifiedChain.TraceWord
import NeuralArtifacts.Hardening
import NeuralArtifacts.Stability
import PRLT.DrawingBoard

/-!
# B5 — hardening is a restriction on the read axis

Soft routing exposes score coordinates; hard routing exposes the winner only. As
presentations over the read alphabet that is an inclusion `hardRead ⊆ softRead`, and the
read-axis law of the presentation lattice (`PresentationRelative.DrawingBoard.ReadAxisRefines`,
discharged here as `readAxisRefines`) turns that inclusion into a coarsening of the joint
quotient.

The engineered operator `NeuralArtifacts.Neural.roundSymbol` then stops being an ad hoc
correction and becomes an instance of a presentation law: the wrong-mass condition
(`Neural.exact_symbol_iff`) is a sufficient numerical criterion for the presentation-theoretic
fact that the restriction creates **no darkness** between states the machine must separate,
and the same conclusion survives perturbation of the realized coordinates
(`Neural.corrected_perturbation`) and perturbation of the scores
(`Neural.score_winner_preserved`). That is why the criterion lifts past a single gate.

Main declarations.

* `ReadAtom S` — the read alphabet: winner atoms and score-threshold atoms.
* `readConceptOf hard v` — the concept a routed state induces on the read alphabet.
* `hardRead S ⊂ softRead S` — the restriction, and `hardRead_ssubset_softRead`: it is
  proper, so hardening genuinely removes words.
* `readAxisRefines` — the read-axis law of `PRLT/DrawingBoard`, proved.
* `hardening_coarsens` — the law applied at the hardening inclusion.
* `not_darkAt_hardRead` — the separation criterion at the hard presentation.
* `hard_not_dark_of_wrong_mass`, `hard_not_dark_of_perturbation`,
  `hard_not_dark_of_score_margin` — **B5**: three sufficient conditions, from the exact
  mass criterion, the perturbed mass criterion, and the score margin.
* `cascade_hard_not_dark_of_route_ne` — the same at a `MuxCascade` route.
-/

universe u v

noncomputable section

namespace NeuralArtifacts.CertifiedChain

open TLT.TemperedDesignLaw.MuxHierarchy
open PresentationRelative

/-! ## The read alphabet -/

/-- A read atom over the symbol alphabet `S`: either the hard read "the selected symbol is
`s`", or the soft read "the score coordinate at `s` is at least `θ`". -/
inductive ReadAtom (S : Type u) : Type u where
  | winner : S → ReadAtom S
  | mass : S → ℝ → ReadAtom S

variable {S : Type u}

/-- The read concept of a routed state: `hard` answers the winner atoms, the score vector
`v` answers the threshold atoms. -/
def readConceptOf (hard : S → Bool) (v : S → ℝ) : FLT.Concept (ReadAtom S) Bool :=
  fun a => match a with
    | .winner s => hard s
    | .mass s θ => decide (θ ≤ v s)

@[simp] theorem readConceptOf_winner (hard : S → Bool) (v : S → ℝ) (s : S) :
    readConceptOf hard v (.winner s) = hard s := rfl

@[simp] theorem readConceptOf_mass (hard : S → Bool) (v : S → ℝ) (s : S) (θ : ℝ) :
    readConceptOf hard v (.mass s θ) = decide (θ ≤ v s) := rfl

/-! ## The two presentations and the read-axis law -/

/-- The hard read: only winner words are admissible. -/
def hardRead (S : Type u) : Presentation (ReadAtom S) := {w | ∃ s, w.1 = .winner s}

/-- The soft read: winner words and score words. -/
def softRead (S : Type u) : Presentation (ReadAtom S) :=
  {w | (∃ s, w.1 = .winner s) ∨ (∃ s θ, w.1 = .mass s θ)}

theorem hardRead_subset_softRead (S : Type u) : hardRead S ⊆ softRead S :=
  fun _ hw => Or.inl hw

theorem softRead_eq_top (S : Type u) : softRead S = (⊤ : Presentation (ReadAtom S)) := by
  ext w
  simp only [softRead, Set.mem_setOf_eq, Set.top_eq_univ, Set.mem_univ, iff_true]
  obtain ⟨a, _⟩ := w
  cases a with
  | winner s => exact Or.inl ⟨s, rfl⟩
  | mass s θ => exact Or.inr ⟨s, θ, rfl⟩

/-- Hardening genuinely removes words: the inclusion is proper as soon as there is a symbol
to score. -/
theorem hardRead_ssubset_softRead (S : Type u) [Nonempty S] : hardRead S ⊂ softRead S := by
  refine ⟨hardRead_subset_softRead S, ?_⟩
  intro hsub
  obtain ⟨s⟩ := ‹Nonempty S›
  have hmem : ((ReadAtom.mass s 0, true) : ReadAtom S × Bool) ∈ softRead S :=
    Or.inr ⟨s, 0, rfl⟩
  obtain ⟨t, ht⟩ := hsub hmem
  simp at ht

/-- **The read-axis law**, discharged. Enlarging the admissible words refines the joint
quotient; restricting them coarsens it. This is the drawing-board target
`PresentationRelative.DrawingBoard.ReadAxisRefines`. -/
theorem readAxisRefines : DrawingBoard.ReadAxisRefines.{u} :=
  fun _ _ _ _ hPQ _ _ h g hg w hw => h g hg w (hPQ hw)

/-- **B5 (hardening coarsens the joint quotient).** The read-axis law at the hardening
inclusion: samples the soft read cannot separate, the hard read cannot separate either, for
every teaching family. -/
theorem hardening_coarsens
    (G : Set (Finset (ReadAtom S × Bool) → Finset (ReadAtom S × Bool)))
    (σ₁ σ₂ : Finset (ReadAtom S × Bool))
    (h : DrawingBoard.jointBisimAt (softRead S) G σ₁ σ₂) :
    DrawingBoard.jointBisimAt (hardRead S) G σ₁ σ₂ :=
  readAxisRefines (ReadAtom S) (hardRead S) (softRead S) G
    (hardRead_subset_softRead S) σ₁ σ₂ h

/-! ## The separation criterion at the hard presentation -/

/-- Two read concepts whose hard answers differ at one symbol are not dark at the hard
presentation: the winner word at that symbol still separates them. -/
theorem not_darkAt_hardRead {hard₁ hard₂ : S → Bool} {v₁ v₂ : S → ℝ} (s : S)
    (h : hard₁ s ≠ hard₂ s) :
    ¬ DarkAt (hardRead S) (readConceptOf hard₁ v₁) (readConceptOf hard₂ v₂) := by
  intro hdark
  have hmem : ((ReadAtom.winner s, hard₁ s) : ReadAtom S × Bool) ∈
      Frame.obsOn wordSat (hardRead S) (readConceptOf hard₁ v₁) := ⟨⟨s, rfl⟩, rfl⟩
  rw [hdark] at hmem
  exact h hmem.2.symm

/-! ## The hardened read of a soft coordinate vector -/

/-- The hard read produced by the saturating correction `roundSymbol` at tolerance `η`. -/
def hardOf (η : ℝ) (v : S → ℝ) : S → Bool :=
  fun s => decide (Neural.roundSymbol η (v s) = 1)

/-- The read concept of a soft coordinate vector: the winner atoms are answered by the
hardened coordinates, the score atoms by the coordinates themselves. -/
def readConcept (η : ℝ) (v : S → ℝ) : FLT.Concept (ReadAtom S) Bool :=
  readConceptOf (hardOf η v) v

theorem readConcept_eq (η : ℝ) (v : S → ℝ) :
    readConcept η v = readConceptOf (hardOf η v) v := rfl

/-- An exact one-hot correction is the same thing as a hard read pinned to one symbol. -/
theorem hardOf_of_eq_oneHot [DecidableEq S] {η : ℝ} {v : S → ℝ} {t : S}
    (h : (fun s => Neural.roundSymbol η (v s)) = Neural.oneHot t) (s : S) :
    hardOf η v s = decide (s = t) := by
  have hs : Neural.roundSymbol η (v s) = Neural.oneHot t s := congrFun h s
  by_cases hst : s = t
  · subst hst
    simp [hardOf, hs]
  · simp [hardOf, hs, Neural.oneHot, hst]

/-- The wrong-mass condition pins the hard read to the target symbol. This is
`Neural.exact_symbol_iff` read as a statement about the hard presentation. -/
theorem hardOf_eq_of_wrong_mass [DecidableEq S] {I : Type v} [Fintype I] {η : ℝ}
    (hη : η < 1 / 2) (p : Neural.Probability I) (lab : I → S) (t : S)
    (hmass : p.wrong lab t ≤ η) (s : S) :
    hardOf η (p.coord lab) s = decide (s = t) :=
  hardOf_of_eq_oneHot ((Neural.exact_symbol_iff hη p lab t).mpr hmass) s

/-- **B5 (the exact mass criterion creates no darkness).** Two routed states that each
satisfy the wrong-mass condition at their own target symbol, the targets being distinct,
are still separated by the hard read: hardening destroys no distinction the machine
makes. -/
theorem hard_not_dark_of_wrong_mass [DecidableEq S] {I₁ I₂ : Type v} [Fintype I₁] [Fintype I₂]
    {η : ℝ} (hη : η < 1 / 2)
    {p₁ : Neural.Probability I₁} {lab₁ : I₁ → S} {t₁ : S}
    {p₂ : Neural.Probability I₂} {lab₂ : I₂ → S} {t₂ : S}
    (h₁ : p₁.wrong lab₁ t₁ ≤ η) (h₂ : p₂.wrong lab₂ t₂ ≤ η) (hne : t₁ ≠ t₂) :
    ¬ DarkAt (hardRead S) (readConcept η (p₁.coord lab₁)) (readConcept η (p₂.coord lab₂)) := by
  refine not_darkAt_hardRead (v₁ := p₁.coord lab₁) (v₂ := p₂.coord lab₂) t₁ ?_
  rw [hardOf_eq_of_wrong_mass hη p₁ lab₁ t₁ h₁, hardOf_eq_of_wrong_mass hη p₂ lab₂ t₂ h₂]
  simp [hne]

/-- **B5 (the perturbed mass criterion creates no darkness).** The same conclusion when the
realized coordinates are only within `ξ` of the softmax coordinates, with the mass budget
reduced by `ξ`. -/
theorem hard_not_dark_of_perturbation [DecidableEq S] {I₁ I₂ : Type v} [Fintype I₁] [Fintype I₂]
    {η ξ₁ ξ₂ : ℝ} (hη : η < 1 / 2)
    {p₁ : Neural.Probability I₁} {lab₁ : I₁ → S} {t₁ : S} {v₁ : S → ℝ}
    {p₂ : Neural.Probability I₂} {lab₂ : I₂ → S} {t₂ : S} {v₂ : S → ℝ}
    (hb₁ : p₁.wrong lab₁ t₁ ≤ η - ξ₁) (hv₁ : ∀ s, |v₁ s - p₁.coord lab₁ s| ≤ ξ₁)
    (hb₂ : p₂.wrong lab₂ t₂ ≤ η - ξ₂) (hv₂ : ∀ s, |v₂ s - p₂.coord lab₂ s| ≤ ξ₂)
    (hne : t₁ ≠ t₂) :
    ¬ DarkAt (hardRead S) (readConcept η v₁) (readConcept η v₂) := by
  refine not_darkAt_hardRead (v₁ := v₁) (v₂ := v₂) t₁ ?_
  rw [hardOf_of_eq_oneHot (Neural.corrected_perturbation hη p₁ lab₁ t₁ ξ₁ v₁ hb₁ hv₁) t₁,
    hardOf_of_eq_oneHot (Neural.corrected_perturbation hη p₂ lab₂ t₂ ξ₂ v₂ hb₂ hv₂) t₁]
  simp [hne]

/-! ## The score-margin form -/

open Classical in
/-- The winner read of a score vector: the strict argmax. -/
def winnerOf (sc : S → ℝ) : S → Bool :=
  fun s => decide (∀ s', s' ≠ s → sc s' < sc s)

theorem winnerOf_eq_true_iff (sc : S → ℝ) (s : S) :
    winnerOf sc s = true ↔ ∀ s', s' ≠ s → sc s' < sc s := by
  unfold winnerOf
  simp only [decide_eq_true_eq]

theorem winnerOf_eq_false_iff (sc : S → ℝ) (s : S) :
    winnerOf sc s = false ↔ ¬ ∀ s', s' ≠ s → sc s' < sc s := by
  unfold winnerOf
  simp only [decide_eq_false_iff_not]

/-- A score margin larger than twice the realized error pins the winner read. This is
`Neural.score_winner_preserved` read as a statement about the hard presentation. -/
theorem winnerOf_eq_of_margin [Fintype S] (sc real : S → ℝ) (winner : S)
    (delta err : ℝ) (hgap : ∀ j, j ≠ winner → delta ≤ sc winner - sc j)
    (herror : ∀ j, |real j - sc j| ≤ err) (hmargin : 2 * err < delta) :
    winnerOf real winner = true ∧ ∀ j, j ≠ winner → winnerOf real j = false := by
  have hpres := Neural.score_winner_preserved sc real winner delta err hgap herror hmargin
  refine ⟨(winnerOf_eq_true_iff real winner).mpr hpres, fun j hj => ?_⟩
  refine (winnerOf_eq_false_iff real j).mpr fun hall => ?_
  exact absurd (hall winner fun hc => hj hc.symm) (not_lt.mpr (le_of_lt (hpres j hj)))

/-- **B5 (the score-margin criterion creates no darkness).** Two routed states whose soft
scores carry a margin larger than twice the realized error, at distinct winners, are still
separated by the hard read. -/
theorem hard_not_dark_of_score_margin [Fintype S]
    {sc₁ real₁ sc₂ real₂ : S → ℝ} {w₁ w₂ : S} {δ₁ e₁ δ₂ e₂ : ℝ}
    (hgap₁ : ∀ j, j ≠ w₁ → δ₁ ≤ sc₁ w₁ - sc₁ j) (herr₁ : ∀ j, |real₁ j - sc₁ j| ≤ e₁)
    (hm₁ : 2 * e₁ < δ₁)
    (hgap₂ : ∀ j, j ≠ w₂ → δ₂ ≤ sc₂ w₂ - sc₂ j) (herr₂ : ∀ j, |real₂ j - sc₂ j| ≤ e₂)
    (hm₂ : 2 * e₂ < δ₂)
    (hne : w₁ ≠ w₂) :
    ¬ DarkAt (hardRead S) (readConceptOf (winnerOf real₁) real₁)
      (readConceptOf (winnerOf real₂) real₂) := by
  refine not_darkAt_hardRead (v₁ := real₁) (v₂ := real₂) w₁ ?_
  rw [(winnerOf_eq_of_margin sc₁ real₁ w₁ δ₁ e₁ hgap₁ herr₁ hm₁).1,
    (winnerOf_eq_of_margin sc₂ real₂ w₂ δ₂ e₂ hgap₂ herr₂ hm₂).2 w₁ hne]
  exact Bool.noConfusion

/-! ## The same at a cascade route -/

variable {d L k : ℕ}

/-- The soft read of a cascade route: the affine route scores at the cascade output. -/
def cascadeScores (C : MuxCascade d L) (rs : Fin k → AffineFunctional d)
    (y : Fin d → ℝ) : Fin k → ℝ :=
  fun j => (rs j).eval (C.run y)

/-- The hard read of a cascade route: the winner index. -/
def cascadeWinner (C : MuxCascade d L) (rs : Fin k → AffineFunctional d) (hk : 0 < k)
    (y : Fin d → ℝ) : Fin k → Bool :=
  fun j => decide (cascadeRoute C rs hk y = j)

/-- The read concept of a cascade run through its route. -/
def cascadeReadConcept (C : MuxCascade d L) (rs : Fin k → AffineFunctional d) (hk : 0 < k)
    (y : Fin d → ℝ) : FLT.Concept (ReadAtom (Fin k)) Bool :=
  readConceptOf (cascadeWinner C rs hk y) (cascadeScores C rs y)

/-- **B5 at the cascade.** Runs the route sends to different symbols are not dark at the
hard read. -/
theorem cascade_hard_not_dark_of_route_ne (C : MuxCascade d L)
    (rs : Fin k → AffineFunctional d) (hk : 0 < k) (y₁ y₂ : Fin d → ℝ)
    (h : cascadeRoute C rs hk y₁ ≠ cascadeRoute C rs hk y₂) :
    ¬ DarkAt (hardRead (Fin k)) (cascadeReadConcept C rs hk y₁) (cascadeReadConcept C rs hk y₂) := by
  refine not_darkAt_hardRead (v₁ := cascadeScores C rs y₁) (v₂ := cascadeScores C rs y₂)
    (cascadeRoute C rs hk y₁) ?_
  have h1 : cascadeWinner C rs hk y₁ (cascadeRoute C rs hk y₁) = true := decide_eq_true rfl
  have h2 : cascadeWinner C rs hk y₂ (cascadeRoute C rs hk y₁) = false :=
    decide_eq_false fun hc => h hc.symm
  rw [h1, h2]
  exact Bool.noConfusion

end NeuralArtifacts.CertifiedChain

end

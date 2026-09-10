/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import PRLT.Core
import TLT_Proofs.TemperedDesignLaw.MuxDepthLadderGeneral

/-!
# B1 — the cascade trace is a presentation word

The routing line of the certified-compiler chain localizes by exact fibers. This module
supplies the first bridge: the active-branch trace of an affine-mux cascade
(`TLT_Proofs.TemperedDesignLaw.MuxHierarchy.MuxCascade.trace`) is a word over the branch
alphabet, and the cascade's partial-trace fiber predicate
(`MuxCascade.PFiber`, TLT) is agreement of word prefixes, hence a condition on a
presentation in the sense of `PresentationRelative.Presentation` (PRLT).

Main declarations.

* `TraceAtom C` — the letter alphabet: the dependent pair `(layer, selected branch)`. An
  atom is the assertion "layer `i` selects branch `b`", so it is a `PRLT` domain point and
  a labeled atom `(a, β)` is a `PRLT` word.
* `traceWord C y` — the layer-ordered trace word of the run on `y`.
* `PrefixFiber C x₀ y m` — prefix agreement at every carrier dimension `d`; at `d = 1` it
  is TLT's `MuxCascade.PFiber` definitionally (`prefixFiber_eq_pfiber`).
* `take_traceWord_eq_iff` / `pfiber_iff_take` — **the locked B1 statement**: the fiber
  predicate is equality of length-`m` word prefixes.
* `tracePres C m` — the depth-`m` trace presentation: the atoms of the layers below `m`,
  at both polarities.
* `prefixFiber_iff_darkAt` / `pfiber_iff_darkAt` — the fiber predicate IS a presentation
  condition: it is darkness (`PresentationRelative.DarkAt`) at `tracePres C m`.
* `admissibleTrace C` — the set of trace words the cascade admits, and
  `darkAt_admissibleTrace_iff`: that presentation is faithful to the trace.

Nothing here is metric. There is no ball, no Lipschitz constant, no covering number: a
fiber is an exact equality of finitely many branch letters.
-/

universe u

noncomputable section

namespace NeuralArtifacts.CertifiedChain

open TLT.TemperedDesignLaw.MuxHierarchy
open PresentationRelative

variable {d L : ℕ}

/-! ## The letter alphabet -/

/-- A trace atom of a cascade: the assertion that layer `i` selects branch `b`. This is the
PRLT domain point of the trace read; a labeled atom `(a, β) : TraceAtom C × Bool` is a PRLT
word. -/
abbrev TraceAtom (C : MuxCascade d L) : Type := Σ i : Fin L, Fin (C.arity i)

/-- The word a trace vector spells: one letter per layer, in layer order. -/
def wordOfTrace (C : MuxCascade d L) (W : (i : Fin L) → Fin (C.arity i)) :
    List (TraceAtom C) :=
  (List.finRange L).map fun i => ⟨i, W i⟩

/-- The trace word of a cascade run. -/
def traceWord (C : MuxCascade d L) (y : Fin d → ℝ) : List (TraceAtom C) :=
  wordOfTrace C (C.trace y)

theorem traceWord_eq_wordOfTrace (C : MuxCascade d L) (y : Fin d → ℝ) :
    traceWord C y = wordOfTrace C (C.trace y) := rfl

theorem length_traceWord (C : MuxCascade d L) (y : Fin d → ℝ) :
    (traceWord C y).length = L := by
  simp [traceWord, wordOfTrace]

/-! ## Prefix fibers at every dimension -/

/-- Prefix agreement of two runs: they select the same branch at every layer below `m`.
Stated at every carrier dimension `d`; TLT's `MuxCascade.PFiber` is the `d = 1` case, on
the nose. -/
def PrefixFiber (C : MuxCascade d L) (x₀ y : Fin d → ℝ) (m : ℕ) : Prop :=
  ∀ i : Fin L, i.val < m → C.trace y i = C.trace x₀ i

/-- The general-dimension prefix fiber restricts to TLT's `MuxCascade.PFiber`. -/
theorem prefixFiber_eq_pfiber (C : MuxCascade 1 L) (x₀ y : Fin 1 → ℝ) (m : ℕ) :
    PrefixFiber C x₀ y m ↔ C.PFiber x₀ y m := Iff.rfl

/-- The full-depth prefix fiber is TLT's full trace fiber. -/
theorem prefixFiber_full_iff (C : MuxCascade d L) (x₀ y : Fin d → ℝ) :
    PrefixFiber C x₀ y L ↔ C.trace y = C.trace x₀ := by
  constructor
  · intro h; funext i; exact h i i.isLt
  · intro h i _; exact congrFun h i

/-! ## The locked statement: fibers are word prefixes -/

theorem mem_take_finRange {n m : ℕ} {i : Fin n} :
    i ∈ (List.finRange n).take m ↔ i.val < m := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨j, hj, hji⟩
    rw [List.length_finRange] at hj
    rw [List.getElem_finRange] at hji
    have hval : (j : ℕ) = (i : ℕ) := by rw [← hji]; rfl
    omega
  · intro hi
    refine ⟨i.val, ?_, ?_⟩
    · rw [List.length_finRange]
      exact lt_min hi i.isLt
    · rw [List.getElem_finRange]
      exact Fin.ext rfl

/-- **B1 (trace-as-word).** Two runs lie in the same depth-`m` trace fiber exactly when
their trace words agree on the first `m` letters. Exact, at every carrier dimension. -/
theorem take_traceWord_eq_iff (C : MuxCascade d L) (x₀ y : Fin d → ℝ) (m : ℕ) :
    (traceWord C y).take m = (traceWord C x₀).take m ↔ PrefixFiber C x₀ y m := by
  rw [traceWord, traceWord, wordOfTrace, wordOfTrace, ← List.map_take, ← List.map_take,
    List.map_inj_left]
  constructor
  · intro h i hi
    have hmem := h i (mem_take_finRange.mpr hi)
    simpa using hmem
  · intro h i hi
    have hval := h i (mem_take_finRange.mp hi)
    simp [hval]

/-- **B1 at TLT's own predicate.** `MuxCascade.PFiber` is prefix agreement of trace
words. -/
theorem pfiber_iff_take (C : MuxCascade 1 L) (x₀ y : Fin 1 → ℝ) (m : ℕ) :
    C.PFiber x₀ y m ↔ (traceWord C y).take m = (traceWord C x₀).take m :=
  ((take_traceWord_eq_iff C x₀ y m).trans (prefixFiber_eq_pfiber C x₀ y m)).symm

/-- Full trace fibers are equality of the whole trace word. -/
theorem traceWord_eq_iff (C : MuxCascade d L) (x₀ y : Fin d → ℝ) :
    traceWord C y = traceWord C x₀ ↔ C.trace y = C.trace x₀ := by
  constructor
  · intro h
    refine (prefixFiber_full_iff C x₀ y).mp ((take_traceWord_eq_iff C x₀ y L).mp ?_)
    rw [h]
  · intro h
    rw [traceWord, traceWord, h]

/-! ## The trace presentation -/

/-- The trace concept of a run: the trace atoms it realizes. -/
def traceConcept (C : MuxCascade d L) (y : Fin d → ℝ) : FLT.Concept (TraceAtom C) Bool :=
  fun a => decide (C.trace y a.1 = a.2)

theorem traceConcept_inj (C : MuxCascade d L) {y₁ y₂ : Fin d → ℝ} :
    traceConcept C y₁ = traceConcept C y₂ ↔ C.trace y₁ = C.trace y₂ := by
  constructor
  · intro h
    funext i
    have hi : decide (C.trace y₁ i = C.trace y₁ i) = decide (C.trace y₂ i = C.trace y₁ i) :=
      congrFun h (⟨i, C.trace y₁ i⟩ : TraceAtom C)
    rw [decide_eq_decide] at hi
    exact (hi.mp rfl).symm
  · intro h
    funext a
    simp [traceConcept, h]

/-- The depth-`m` trace presentation: the admissible words are the trace atoms of the layers
below `m`, at both polarities. `tracePres C L` is the informant setting `⊤` and
`tracePres C 0` is the empty read. -/
def tracePres (C : MuxCascade d L) (m : ℕ) : Presentation (TraceAtom C) :=
  {w | w.1.1.val < m}

theorem mem_tracePres {C : MuxCascade d L} {m : ℕ} {w : TraceAtom C × Bool} :
    w ∈ tracePres C m ↔ w.1.1.val < m := Iff.rfl

theorem tracePres_zero (C : MuxCascade d L) : tracePres C 0 = (∅ : Set (TraceAtom C × Bool)) := by
  ext w
  simp [tracePres]

theorem tracePres_full (C : MuxCascade d L) : tracePres C L = (⊤ : Presentation (TraceAtom C)) := by
  ext w
  simp only [tracePres, Set.mem_setOf_eq, Set.top_eq_univ, Set.mem_univ, iff_true]
  exact w.1.1.isLt

theorem tracePres_mono (C : MuxCascade d L) {m n : ℕ} (h : m ≤ n) :
    tracePres C m ⊆ tracePres C n :=
  fun _ hw => lt_of_lt_of_le hw h

/-- The two-sided region of the depth-`m` trace presentation is exactly the set of atoms of
the layers below `m`: every admissible atom carries both polarities. -/
theorem fullRegion_tracePres (C : MuxCascade d L) (m : ℕ) :
    fullRegion (tracePres C m) = {a : TraceAtom C | a.1.val < m} := by
  ext a
  constructor
  · intro ha; exact ha.1
  · intro ha; exact ⟨ha, ha⟩

/-- **B1 (the fiber IS a presentation condition).** The depth-`m` prefix fiber is darkness
at the depth-`m` trace presentation. TLT's fiber predicate and PRLT's darkness are the same
condition on the same pair of objects. -/
theorem prefixFiber_iff_darkAt (C : MuxCascade d L) (x₀ y : Fin d → ℝ) (m : ℕ) :
    PrefixFiber C x₀ y m ↔ DarkAt (tracePres C m) (traceConcept C y) (traceConcept C x₀) := by
  constructor
  · intro h
    ext w
    simp only [Frame.mem_obsOn, wordSat, traceConcept]
    constructor
    · rintro ⟨hw, hsat⟩
      exact ⟨hw, by rw [← hsat, h w.1.1 hw]⟩
    · rintro ⟨hw, hsat⟩
      exact ⟨hw, by rw [← hsat, h w.1.1 hw]⟩
  · intro h i hi
    have hsat : wordSat (traceConcept C y) ((⟨i, C.trace y i⟩ : TraceAtom C), true) :=
      decide_eq_true rfl
    have hmem : ((⟨i, C.trace y i⟩ : TraceAtom C), true) ∈
        Frame.obsOn wordSat (tracePres C m) (traceConcept C y) := ⟨hi, hsat⟩
    rw [h] at hmem
    have := hmem.2
    simp only [wordSat, traceConcept, decide_eq_true_eq] at this
    exact this.symm

/-- **B1 at TLT's own predicate.** -/
theorem pfiber_iff_darkAt (C : MuxCascade 1 L) (x₀ y : Fin 1 → ℝ) (m : ℕ) :
    C.PFiber x₀ y m ↔ DarkAt (tracePres C m) (traceConcept C y) (traceConcept C x₀) :=
  (prefixFiber_eq_pfiber C x₀ y m).symm.trans (prefixFiber_iff_darkAt C x₀ y m)

/-! ## The admissible trace words of a cascade -/

/-- The trace words the cascade admits: the labeled atoms realized by some run. -/
def admissibleTrace (C : MuxCascade d L) : Presentation (TraceAtom C) :=
  {w | ∃ y : Fin d → ℝ, wordSat (traceConcept C y) w}

theorem admissibleTrace_subset_top (C : MuxCascade d L) :
    admissibleTrace C ⊆ (⊤ : Presentation (TraceAtom C)) := le_top

/-- The cascade's own trace presentation loses nothing about its runs: every word a run
satisfies is admissible. -/
theorem obsOn_admissibleTrace (C : MuxCascade d L) (y : Fin d → ℝ) :
    obsOn (admissibleTrace C) (traceConcept C y) = obs (traceConcept C y) := by
  ext w
  constructor
  · intro hw; exact hw.2
  · intro hw; exact ⟨⟨y, hw⟩, hw⟩

/-- Darkness at the admissible trace presentation is equality of traces: the presentation of
admissible trace words is faithful. -/
theorem darkAt_admissibleTrace_iff (C : MuxCascade d L) (y₁ y₂ : Fin d → ℝ) :
    DarkAt (admissibleTrace C) (traceConcept C y₁) (traceConcept C y₂) ↔
      C.trace y₁ = C.trace y₂ := by
  rw [← traceConcept_inj C]
  constructor
  · intro h
    apply obs_injective
    rw [← obsOn_admissibleTrace C y₁, ← obsOn_admissibleTrace C y₂]
    exact h
  · intro h
    rw [h]
    exact Frame.DarkAt.refl _ _ _

end NeuralArtifacts.CertifiedChain

end

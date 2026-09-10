/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import NeuralArtifacts.CertifiedChain.HardeningRead

/-!
# B6 — the repair of a hardening collapse is one word, and here it is

`PresentationRelative.darkAt_cured_by_word` says that two concepts dark at a presentation,
yet distinguishable at the full vocabulary, are separated by some word outside it, and that
inserting that one word already breaks the darkness. This module instantiates that law at
the failure case of B5 and then names the word.

Main declarations.

* `darkAt_hardRead_iff` — darkness at the hard read is exactly agreement of the hard
  readouts, so the failure case of B5 is `hard₁ = hard₂` with `v₁ ≠ v₂`.
* `readConceptOf_eq_iff` — the soft read is faithful: read concepts agree exactly when both
  the hard readout and the score vector agree.
* `hardRead_darkness_cured` — `darkAt_cured_by_word` at the hardening restriction.
* `hardRead_cure_word` — **B6**: the explicit cure. Where the hard read collapses a
  distinction the scores make at the symbol `s`, the threshold word at
  `max (v₁ s) (v₂ s)` lies outside the hard presentation, separates the two states, and
  breaks the darkness when inserted.
-/

universe u

noncomputable section

namespace NeuralArtifacts.CertifiedChain

open PresentationRelative

variable {S : Type u}

/-- No score word is admissible in the hard read. -/
theorem mass_not_mem_hardRead (s : S) (θ : ℝ) (β : Bool) :
    ((ReadAtom.mass s θ, β) : ReadAtom S × Bool) ∉ hardRead S := by
  rintro ⟨t, ht⟩
  simp at ht

/-- **Darkness at the hard read is agreement of the hard readouts.** This locates the
failure case of B5 exactly: hardening collapses a distinction precisely when the two states
select the same symbols. -/
theorem darkAt_hardRead_iff {hard₁ hard₂ : S → Bool} {v₁ v₂ : S → ℝ} :
    DarkAt (hardRead S) (readConceptOf hard₁ v₁) (readConceptOf hard₂ v₂) ↔ hard₁ = hard₂ := by
  constructor
  · intro hdark
    funext s
    by_contra hs
    exact not_darkAt_hardRead (v₁ := v₁) (v₂ := v₂) s hs hdark
  · intro h
    ext w
    obtain ⟨a, β⟩ := w
    constructor
    · rintro ⟨⟨t, ht⟩, hsat⟩
      refine ⟨⟨t, ht⟩, ?_⟩
      have hat : a = ReadAtom.winner t := ht
      subst hat
      show readConceptOf hard₂ v₂ (ReadAtom.winner t) = β
      rw [readConceptOf_winner, ← h]
      exact hsat
    · rintro ⟨⟨t, ht⟩, hsat⟩
      refine ⟨⟨t, ht⟩, ?_⟩
      have hat : a = ReadAtom.winner t := ht
      subst hat
      show readConceptOf hard₁ v₁ (ReadAtom.winner t) = β
      rw [readConceptOf_winner, h]
      exact hsat

/-- **The soft read is faithful.** Two read concepts are equal exactly when both the hard
readout and the score vector agree; the score words recover the coordinates. -/
theorem readConceptOf_eq_iff {hard₁ hard₂ : S → Bool} {v₁ v₂ : S → ℝ} :
    readConceptOf hard₁ v₁ = readConceptOf hard₂ v₂ ↔ hard₁ = hard₂ ∧ v₁ = v₂ := by
  constructor
  · intro h
    refine ⟨funext fun s => ?_, funext fun s => ?_⟩
    · have hs := congrFun h (ReadAtom.winner s)
      simpa using hs
    · have h₁ := congrFun h (ReadAtom.mass s (v₁ s))
      have h₂ := congrFun h (ReadAtom.mass s (v₂ s))
      simp only [readConceptOf_mass, decide_eq_decide] at h₁ h₂
      exact le_antisymm (h₁.mp le_rfl) (h₂.mpr le_rfl)
  · rintro ⟨rfl, rfl⟩
    rfl

/-- **B6 (the presentation law).** Two read concepts dark at the hard presentation but
distinct are separated by a single word outside it, whose insertion already breaks the
darkness. This is `PresentationRelative.darkAt_cured_by_word` at the hardening
restriction. -/
theorem hardRead_darkness_cured {c₁ c₂ : FLT.Concept (ReadAtom S) Bool}
    (hdark : DarkAt (hardRead S) c₁ c₂) (hne : c₁ ≠ c₂) :
    ∃ w ∉ hardRead S, ¬ (wordSat c₁ w ↔ wordSat c₂ w) ∧
      ¬ DarkAt (insert w (hardRead S)) c₁ c₂ :=
  darkAt_cured_by_word hdark hne

/-- **B6 (the explicit cure).** Where the hard read collapses a distinction that the score
vectors make at the symbol `s`, the score word at the threshold `max (v₁ s) (v₂ s)` is the
cure: it lies outside the hard presentation, the two states disagree on it, and inserting it
breaks the darkness. The failure of hardening comes with its repair, named. -/
theorem hardRead_cure_word {hard₁ hard₂ : S → Bool} {v₁ v₂ : S → ℝ}
    (s : S) (hv : v₁ s ≠ v₂ s) :
    ∃ β : Bool,
      ((ReadAtom.mass s (max (v₁ s) (v₂ s)), β) : ReadAtom S × Bool) ∉ hardRead S ∧
      ¬ (wordSat (readConceptOf hard₁ v₁) (ReadAtom.mass s (max (v₁ s) (v₂ s)), β) ↔
          wordSat (readConceptOf hard₂ v₂) (ReadAtom.mass s (max (v₁ s) (v₂ s)), β)) ∧
      ¬ DarkAt (insert ((ReadAtom.mass s (max (v₁ s) (v₂ s)), β) : ReadAtom S × Bool)
          (hardRead S)) (readConceptOf hard₁ v₁) (readConceptOf hard₂ v₂) := by
  have hle₁ : max (v₁ s) (v₂ s) ≤ v₁ s ↔ v₂ s ≤ v₁ s := by
    rw [max_le_iff]
    exact ⟨fun h => h.2, fun h => ⟨le_rfl, h⟩⟩
  have hle₂ : max (v₁ s) (v₂ s) ≤ v₂ s ↔ v₁ s ≤ v₂ s := by
    rw [max_le_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, le_rfl⟩⟩
  have hdiff : decide (max (v₁ s) (v₂ s) ≤ v₁ s) ≠ decide (max (v₁ s) (v₂ s) ≤ v₂ s) := by
    rw [Ne, decide_eq_decide, hle₁, hle₂]
    intro hiff
    rcases le_total (v₁ s) (v₂ s) with h | h
    · exact hv (le_antisymm h (hiff.mpr h))
    · exact hv (le_antisymm (hiff.mp h) h)
  refine ⟨decide (max (v₁ s) (v₂ s) ≤ v₁ s), mass_not_mem_hardRead _ _ _, ?_, ?_⟩
  · intro hiff
    exact hdiff (hiff.mp rfl).symm
  · intro hins
    have hmem : ((ReadAtom.mass s (max (v₁ s) (v₂ s)),
        decide (max (v₁ s) (v₂ s) ≤ v₁ s)) : ReadAtom S × Bool) ∈
        Frame.obsOn wordSat
          (insert ((ReadAtom.mass s (max (v₁ s) (v₂ s)),
            decide (max (v₁ s) (v₂ s) ≤ v₁ s)) : ReadAtom S × Bool) (hardRead S))
          (readConceptOf hard₁ v₁) := ⟨Set.mem_insert _ _, rfl⟩
    rw [hins] at hmem
    exact hdiff hmem.2.symm

end NeuralArtifacts.CertifiedChain

end

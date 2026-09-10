/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import NeuralArtifacts.CertifiedChain.TraceWord
import PRLT.Trace

/-!
# B4 — the trace count is a dimension

PRLT's capacity identity `PresentationRelative.vcdim_traceClass_eq` says that the
presentation-indexed capacity `vcOn P C` is the kernel `VCDim` of the class traced on the
two-sided region of `P`. Instantiated at a cascade's trace class it turns counting traces
into a dimension question, and the dimension is bounded by the depth: a shattered set of
trace atoms carries at most one atom per layer, so the carrier dimension `d` never enters.

Main declarations.

* `cascadeTraceClass C` — the concept class of realized trace concepts.
* `vcdim_cascadeTraceClass_eq` — **B4**: the capacity identity at the cascade trace class.
* `vcOn_tracePres_le`, `vcdim_cascadeTraceClass_le` — the depth bound: the depth-`m` trace
  read has capacity at most `min m L`, so `VCDim (TraceAtom C) (cascadeTraceClass C) ≤ L`.
* `traceWord_alternations_le` — where the two prices meet: the PRLT-side trace WORD inherits
  TLT's alternation bound `2 ^ L - 1` along any increasing one-dimensional sample.
-/

noncomputable section

namespace NeuralArtifacts.CertifiedChain

open TLT.TemperedDesignLaw.MuxHierarchy
open PresentationRelative

variable {d L : ℕ}

/-! ## The cascade trace class -/

/-- The concept class of a cascade's realized trace concepts. -/
def cascadeTraceClass (C : MuxCascade d L) : ConceptClass (TraceAtom C) Bool :=
  Set.range (traceConcept C)

/-- **B4 (the capacity identity at the cascade trace class).** Counting the traces a cascade
realizes, read through the depth-`m` presentation, is a kernel `VCDim` computation on the
two-sided region — not a fresh estimate. -/
theorem vcdim_cascadeTraceClass_eq (C : MuxCascade d L) (m : ℕ) :
    VCDim (fullRegion (tracePres C m))
        (PresentationRelative.traceClass (tracePres C m) (cascadeTraceClass C))
      = vcOn (tracePres C m) (cascadeTraceClass C) :=
  vcdim_traceClass_eq _ _

/-! ## The depth bound -/

/-- A set of trace atoms observably shattered by the cascade trace class carries at most one
atom per layer: two atoms at the same layer cannot both be realized by one run. -/
theorem shatteredOn_fst_injOn (C : MuxCascade d L) {m : ℕ} {S : Finset (TraceAtom C)}
    (hS : ShattersOn (tracePres C m) (cascadeTraceClass C) S) :
    ∀ a ∈ S, ∀ b ∈ S, a.1.val = b.1.val → a = b := by
  intro a ha b hb hab
  obtain ⟨c, hcC, hc⟩ := (hS fun _ => true).2
  obtain ⟨y, rfl⟩ := hcC
  have hfa : C.trace y a.1 = a.2 := by
    have := hc ⟨a, ha⟩
    simpa [traceConcept] using this
  have hfb : C.trace y b.1 = b.2 := by
    have := hc ⟨b, hb⟩
    simpa [traceConcept] using this
  have h1 : a.1 = b.1 := Fin.ext hab
  calc a = (⟨a.1, C.trace y a.1⟩ : TraceAtom C) := by rw [hfa]
    _ = (⟨b.1, C.trace y b.1⟩ : TraceAtom C) :=
        congrArg (fun i => (⟨i, C.trace y i⟩ : TraceAtom C)) h1
    _ = b := by rw [hfb]

/-- **B4 (depth prices the trace).** The depth-`m` trace read of a cascade has capacity at
most `min m L`. Depth indexes the partition; the carrier dimension does not appear. -/
theorem vcOn_tracePres_le (C : MuxCascade d L) (m : ℕ) :
    vcOn (tracePres C m) (cascadeTraceClass C) ≤ ((min m L : ℕ) : WithTop ℕ) := by
  classical
  refine iSup₂_le fun S hS => ?_
  have hfull : ∀ a ∈ S, a.1.val < m := by
    intro a ha
    have hsub := (shattersOn_iff.mp hS).1
    have : a ∈ fullRegion (tracePres C m) := hsub (Finset.mem_coe.mpr ha)
    exact this.1
  have hinj : ∀ a ∈ S, ∀ b ∈ S, (fun x : TraceAtom C => x.1.val) a
      = (fun x : TraceAtom C => x.1.val) b → a = b :=
    shatteredOn_fst_injOn C hS
  have hcard : S.card = (S.image fun x : TraceAtom C => x.1.val).card :=
    (Finset.card_image_of_injOn hinj).symm
  have hsub : (S.image fun x : TraceAtom C => x.1.val) ⊆ Finset.range (min m L) := by
    intro j hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (lt_min (hfull a ha) a.1.isLt)
  have : S.card ≤ min m L := by
    rw [hcard]
    calc (S.image fun x : TraceAtom C => x.1.val).card
        ≤ (Finset.range (min m L)).card := Finset.card_le_card hsub
      _ = min m L := Finset.card_range _
  exact_mod_cast this

/-- **B4 (the trace class dimension is at most the depth).** -/
theorem vcdim_cascadeTraceClass_le (C : MuxCascade d L) :
    VCDim (TraceAtom C) (cascadeTraceClass C) ≤ ((L : ℕ) : WithTop ℕ) := by
  have h := vcOn_tracePres_le C L
  rw [tracePres_full, vcOn_top] at h
  simpa using h

/-! ## Where the dimension meets the alternation bound -/

/-- **B4 (the two prices meet).** For a binary cascade on a one-dimensional carrier, the
PRLT-side trace WORD inherits TLT's alternation bound: along any strictly increasing sample
it changes at most `2 ^ L - 1` times. Together with `vcdim_cascadeTraceClass_le` both prices
are read off the depth alone. -/
theorem traceWord_alternations_le {L : ℕ} (layers : Fin L → AffineMuxLayer 1 2) {M : ℕ}
    (pts : Fin (M + 1) → ℝ) (hinc : Increasing pts) :
    seqChanges (fun k => traceWord (binCascade layers) (fun _ => pts k)) ≤ 2 ^ L - 1 :=
  le_trans
    (seqChanges_comp_le (fun k => (binCascade layers).trace (fun _ => pts k))
      (wordOfTrace (binCascade layers)))
    (binTrace_alternations_le layers pts hinc)

end NeuralArtifacts.CertifiedChain

end

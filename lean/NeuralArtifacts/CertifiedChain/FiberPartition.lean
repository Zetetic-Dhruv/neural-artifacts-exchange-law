/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import NeuralArtifacts.CertifiedChain.TraceWord
import NeuralArtifacts.Extraction

/-!
# B2 — the trace-word fibers are the extraction template's finite partition

The continuous-state extraction template (`NeuralArtifacts.FiniteAbstraction.ofRegions`)
asks for a cover of the concrete state space by disjoint regions on which the transition is
invariant and the readout is constant. The trace words of an affine-mux cascade supply
exactly that, and every inclusion is an equality rather than an error bound.

Main declarations.

* `wordPrefixMap C W m` — the affine self-map the first `m` letters of a trace word
  determine, with no base point. `prefixMap_eq_wordPrefixMap` identifies it with TLT's
  `MuxCascade.prefixMap`, and `wordPrefixMap_congr` says it reads only the first `m`
  letters.
* `runUpTo_eq_wordPrefixMap_of_prefixFiber` — the affine collapse at every carrier
  dimension `d`: on the depth-`m` prefix fiber, `runUpTo m` IS a single fixed affine map.
  TLT proves this at `d = 1` (`MuxCascade.runUpTo_eq_prefixMap_on_pfiber`); the same
  induction is carried here with `d` free.
* `prefixVec_succ` — **successor determinacy**: the depth-`(m+1)` word is the depth-`m`
  word updated at layer `m` by the layer-`m` letter.
* `trace_eq_gate_wordPrefixMap` — the layer-`m` letter, on a depth-`m` region, is the gate
  of one fixed affine map applied to the input. Exact.
* `prefixRegion_cover`, `prefixRegion_disjoint`, `runUpTo_const_affine_on_prefixRegion`,
  `fiberMap_const_on_fiber` — the four hypotheses of the extraction template.
* `traceCertificate`, `clocked_all_histories` — the template discharged: a
  `FiniteAbstraction.Certificate` whose finite side is the trace word, hence agreement at
  every horizon.

No metric enters. `Metric.ball`, `LipschitzWith` and covering numbers belong to the
capacity side of TLT and have no role in this file.
-/

noncomputable section

namespace NeuralArtifacts.CertifiedChain

open TLT.TemperedDesignLaw.MuxHierarchy
open PresentationRelative

variable {d L : ℕ}

/-! ## The affine map of a trace word -/

/-- The affine self-map determined by the first `m` letters of a trace word: at each layer
`i < m` it applies the branch that the word selects. No base point is involved. -/
def wordPrefixMap (C : MuxCascade d L) (W : (i : Fin L) → Fin (C.arity i)) :
    ℕ → AffineSelfMap d
  | 0 => AffineSelfMap.id d
  | (m + 1) =>
      if h : m < L then
        ((C.layers ⟨m, h⟩).branches (W ⟨m, h⟩)).comp (wordPrefixMap C W m)
      else wordPrefixMap C W m

/-- The full-depth map of a trace word. -/
def wordFiberMap (C : MuxCascade d L) (W : (i : Fin L) → Fin (C.arity i)) : AffineSelfMap d :=
  wordPrefixMap C W L

/-- The depth-`m` map reads only the first `m` letters. -/
theorem wordPrefixMap_congr (C : MuxCascade d L)
    (W₁ W₂ : (i : Fin L) → Fin (C.arity i)) :
    ∀ m, (∀ i : Fin L, i.val < m → W₁ i = W₂ i) →
      wordPrefixMap C W₁ m = wordPrefixMap C W₂ m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro h
      rw [wordPrefixMap, wordPrefixMap]
      by_cases hm : m < L
      · rw [dif_pos hm, dif_pos hm, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)),
          h ⟨m, hm⟩ (Nat.lt_succ_self m)]
      · rw [dif_neg hm, dif_neg hm]
        exact ih (fun i hi => h i (Nat.lt_succ_of_lt hi))

/-- TLT's base-point prefix map is the word's prefix map: the affine map a run collapses to
depends on the input only through its trace. -/
theorem prefixMap_eq_wordPrefixMap (C : MuxCascade d L) (x₀ : Fin d → ℝ) :
    ∀ m, C.prefixMap x₀ m = wordPrefixMap C (C.trace x₀) m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [MuxCascade.prefixMap, wordPrefixMap]
      by_cases hm : m < L
      · rw [dif_pos hm, dif_pos hm, ih]
      · rw [dif_neg hm, dif_neg hm]; exact ih

theorem fiberMap_eq_wordFiberMap (C : MuxCascade d L) (x₀ : Fin d → ℝ) :
    C.fiberMap x₀ = wordFiberMap C (C.trace x₀) :=
  prefixMap_eq_wordPrefixMap C x₀ L

/-! ## The affine collapse on a prefix fiber, at every carrier dimension -/

/-- **Exact affine collapse on a prefix fiber, at every `d`.** On the depth-`m` prefix fiber
of `x₀`, running the first `m` layers is applying one fixed affine map. Equality, not an
error bound. TLT carries this at `d = 1`
(`MuxCascade.runUpTo_eq_prefixMap_on_pfiber`); the induction is the same with `d` free. -/
theorem runUpTo_eq_wordPrefixMap_of_prefixFiber (C : MuxCascade d L) (x₀ y : Fin d → ℝ) :
    ∀ m, PrefixFiber C x₀ y m → C.runUpTo m y = (wordPrefixMap C (C.trace x₀) m).apply y := by
  intro m
  induction m with
  | zero => intro _; simp [MuxCascade.runUpTo, wordPrefixMap]
  | succ m ih =>
      intro hpf
      rw [MuxCascade.runUpTo, wordPrefixMap]
      by_cases hm : m < L
      · rw [dif_pos hm, dif_pos hm]
        have hpf_m : PrefixFiber C x₀ y m := fun i hi => hpf i (Nat.lt_succ_of_lt hi)
        rw [AffineSelfMap.comp_apply, ← ih hpf_m]
        have hgate : (C.layers ⟨m, hm⟩).gate (C.harity ⟨m, hm⟩) (C.runUpTo m y)
            = C.trace x₀ ⟨m, hm⟩ := hpf ⟨m, hm⟩ (Nat.lt_succ_self m)
        simp only [AffineMuxLayer.applyLayer, hgate]
      · rw [dif_neg hm, dif_neg hm]
        exact ih (fun i hi => hpf i (Nat.lt_succ_of_lt hi))

/-- The run of the first `m` layers is the word's own affine map applied to the input. -/
theorem runUpTo_eq_wordPrefixMap (C : MuxCascade d L) (y : Fin d → ℝ) (m : ℕ) :
    C.runUpTo m y = (wordPrefixMap C (C.trace y) m).apply y :=
  runUpTo_eq_wordPrefixMap_of_prefixFiber C y y m (fun _ _ => rfl)

/-- The full-depth form: on a trace fiber the whole cascade is one fixed affine map. -/
theorem run_eq_wordFiberMap_of_fiber (C : MuxCascade d L) (x₀ y : Fin d → ℝ)
    (h : C.trace y = C.trace x₀) :
    C.run y = (wordFiberMap C (C.trace x₀)).apply y := by
  rw [C.run_eq_on_fiber x₀ y h, fiberMap_eq_wordFiberMap]

/-- **Readout constancy.** The affine map a run collapses to is literally constant on each
trace fiber. -/
theorem fiberMap_const_on_fiber (C : MuxCascade d L) (x₀ y : Fin d → ℝ)
    (h : C.trace y = C.trace x₀) : C.fiberMap y = C.fiberMap x₀ := by
  rw [fiberMap_eq_wordFiberMap, fiberMap_eq_wordFiberMap, h]

/-! ## Successor determinacy and the layer letter -/

/-- The depth-`m` prefix word of a run: the first `m` letters as realized, the rest padded by
the least branch index (which exists because every arity is positive). -/
def prefixVec (C : MuxCascade d L) (m : ℕ) (y : Fin d → ℝ) : (i : Fin L) → Fin (C.arity i) :=
  fun i => if i.val < m then C.trace y i else ⟨0, C.harity i⟩

theorem prefixVec_full (C : MuxCascade d L) (y : Fin d → ℝ) :
    prefixVec C L y = C.trace y := by
  funext i
  simp [prefixVec, i.isLt]

/-- **B2 (successor determinacy).** The depth-`(m+1)` prefix word is the depth-`m` prefix
word updated at layer `m` by the layer-`m` letter: the successor word is a function of the
current word and the layer-`m` letter alone. -/
theorem prefixVec_succ (C : MuxCascade d L) (m : ℕ) (y : Fin d → ℝ) :
    prefixVec C (m + 1) y
      = fun i => if i.val = m then C.trace y i else prefixVec C m y i := by
  funext i
  simp only [prefixVec]
  by_cases hi : i.val = m
  · rw [if_pos (by omega), if_pos hi]
  · by_cases hlt : i.val < m
    · rw [if_pos (by omega), if_neg hi, if_pos hlt]
    · rw [if_neg (by omega), if_neg hi, if_neg hlt]

theorem prefixVec_eq_iff (C : MuxCascade d L) (m : ℕ) (x₀ y : Fin d → ℝ) :
    prefixVec C m y = prefixVec C m x₀ ↔ PrefixFiber C x₀ y m := by
  constructor
  · intro h i hi
    have hy := congrFun h i
    simpa [prefixVec, hi] using hy
  · intro h
    funext i
    by_cases hi : i.val < m
    · simp [prefixVec, hi, h i hi]
    · simp [prefixVec, hi]

/-- **B2 (the letter is one affine argmax).** On the depth-`m` prefix fiber of `x₀`, the
layer-`m` branch letter is the gate of a single FIXED affine map applied to the input. This
is the exact statement of "the fiber refines by one affine cut": no metric ball, no
Lipschitz constant, no covering number. -/
theorem trace_eq_gate_wordPrefixMap (C : MuxCascade d L) (x₀ y : Fin d → ℝ) (m : ℕ)
    (hm : m < L) (h : PrefixFiber C x₀ y m) :
    C.trace y ⟨m, hm⟩
      = (C.layers ⟨m, hm⟩).gate (C.harity ⟨m, hm⟩)
          ((wordPrefixMap C (C.trace x₀) m).apply y) := by
  show (C.layers ⟨m, hm⟩).gate (C.harity ⟨m, hm⟩) (C.runUpTo m y) = _
  rw [runUpTo_eq_wordPrefixMap_of_prefixFiber C x₀ y m h]

/-! ## The region system -/

/-- The depth-`m` region of a prefix word: the inputs whose first `m` letters spell it. -/
def prefixRegion (C : MuxCascade d L) (m : ℕ) (W : (i : Fin L) → Fin (C.arity i)) :
    Set (Fin d → ℝ) :=
  {y | prefixVec C m y = W}

/-- The regions cover. -/
theorem prefixRegion_cover (C : MuxCascade d L) (m : ℕ) (y : Fin d → ℝ) :
    ∃ W, y ∈ prefixRegion C m W := ⟨prefixVec C m y, rfl⟩

/-- The regions are disjoint. -/
theorem prefixRegion_disjoint (C : MuxCascade d L) (m : ℕ) (y : Fin d → ℝ)
    {W₁ W₂ : (i : Fin L) → Fin (C.arity i)}
    (h₁ : y ∈ prefixRegion C m W₁) (h₂ : y ∈ prefixRegion C m W₂) : W₁ = W₂ :=
  h₁.symm.trans h₂

/-- **The region readout is exact.** On the depth-`m` region of the word `W`, running the
first `m` layers is applying `wordPrefixMap C W m` — the same fixed affine map for every
point of the region. -/
theorem runUpTo_const_affine_on_prefixRegion (C : MuxCascade d L) (m : ℕ)
    (W : (i : Fin L) → Fin (C.arity i)) (y : Fin d → ℝ) (hy : y ∈ prefixRegion C m W) :
    C.runUpTo m y = (wordPrefixMap C W m).apply y := by
  have hW : ∀ i : Fin L, i.val < m → C.trace y i = W i := by
    intro i hi
    have := congrFun hy i
    simpa [prefixVec, hi] using this
  rw [runUpTo_eq_wordPrefixMap C y m, wordPrefixMap_congr C (C.trace y) W m hW]

/-- **The full-depth region readout.** On the trace-fiber of `W` the whole cascade is the
one fixed affine map `wordFiberMap C W`. -/
theorem run_const_affine_on_fiber (C : MuxCascade d L)
    (W : (i : Fin L) → Fin (C.arity i)) (y : Fin d → ℝ) (hy : C.trace y = W) :
    C.run y = (wordFiberMap C W).apply y := by
  have hreg : y ∈ prefixRegion C L W := by
    show prefixVec C L y = W
    rw [prefixVec_full]
    exact hy
  rw [MuxCascade.run, wordFiberMap, runUpTo_const_affine_on_prefixRegion C L W y hreg]

/-! ## The extraction template, discharged -/

/-- The concrete layer-clocked system: the persistent state is `(layers consumed, input)`,
the clock ticks one layer per step, and the readout is the affine map the run has collapsed
to so far. -/
def clockedRun (C : MuxCascade d L) (y₀ : Fin d → ℝ) :
    Moore (ℕ × (Fin d → ℝ)) Unit (AffineSelfMap d) where
  initial := (0, y₀)
  step z _ := (z.1 + 1, z.2)
  out z := C.prefixMap z.2 z.1

/-- The extracted finite system: the persistent state is `(layers consumed, trace word)`. -/
def clockedWord (C : MuxCascade d L) (W₀ : (i : Fin L) → Fin (C.arity i)) :
    Moore (ℕ × ((i : Fin L) → Fin (C.arity i))) Unit (AffineSelfMap d) where
  initial := (0, W₀)
  step q _ := (q.1 + 1, q.2)
  out q := wordPrefixMap C q.2 q.1

/-- **B2 (the extraction template discharged).** The trace-word regions satisfy the four
hypotheses of `FiniteAbstraction.ofRegions` — cover, disjointness, transition invariance,
readout constancy — so the cascade's layer-clocked run carries a finite abstraction whose
states are trace words. The label function is constructed by the template rather than
assumed. -/
def traceCertificate (C : MuxCascade d L) (y₀ : Fin d → ℝ) :
    FiniteAbstraction.Certificate (clockedRun C y₀) (clockedWord C (C.trace y₀)) :=
  FiniteAbstraction.ofRegions (clockedRun C y₀) (clockedWord C (C.trace y₀))
    (fun q => {z | z.1 = q.1 ∧ C.trace z.2 = q.2})
    (fun z => ⟨(z.1, C.trace z.2), rfl, rfl⟩)
    (fun _ q r hq hr => Prod.ext (hq.1.symm.trans hr.1) (hq.2.symm.trans hr.2))
    ⟨rfl, rfl⟩
    (fun q z _ hz => by
      refine ⟨?_, hz.2⟩
      show z.1 + 1 = q.1 + 1
      rw [hz.1])
    (fun q z hz => by
      show C.prefixMap z.2 z.1 = wordPrefixMap C q.2 q.1
      rw [prefixMap_eq_wordPrefixMap C z.2 z.1, hz.1, hz.2])

/-- **B2 (all horizons).** The affine map the cascade has collapsed to after any number of
layers is recovered exactly from the trace word. Agreement on the infinite set of futures,
from a finite object. -/
theorem clocked_all_histories (C : MuxCascade d L) (y₀ : Fin d → ℝ) (s : List Unit) :
    (clockedRun C y₀).out ((clockedRun C y₀).run s)
      = (clockedWord C (C.trace y₀)).out ((clockedWord C (C.trace y₀)).run s) :=
  FiniteAbstraction.all_histories _ _ (traceCertificate C y₀) s

end NeuralArtifacts.CertifiedChain

end

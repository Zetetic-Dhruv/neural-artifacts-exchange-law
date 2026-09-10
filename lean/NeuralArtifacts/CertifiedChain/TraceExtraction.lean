/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import NeuralArtifacts.CertifiedChain.FiberPartition

/-!
# B3 — extraction at the trace presentation

A cascade read through its trace atoms is an inference problem in the sense of
`NeuralArtifacts.Inference`: each atom is a query, its answer cuts the candidate inputs down
to a trace fiber, and the reachable version spaces are exactly the fibers. The machine that
consumes those queries is `traceMachine`; its minimal machine is the canonical inference
state, at all horizons and exactly.

Main declarations.

* `traceQuery C` — the query map: the atom `⟨i, b⟩` cuts to the inputs whose layer-`i`
  letter is `b`.
* `version_traceQuery`, `eval_generator_traceQuery` — the reachable version space after
  reading a list of atoms IS the trace fiber those atoms cut out.
* `latticeMachine` / `latticeMachine_correct` — the machine of an inference problem, correct
  on every history by construction.
* `traceMinimalEquiv` — **B3**: `MinState (reachableMachine (traceMachine C rho)) ≃
  Inference.State rho`, the instantiation of `Extraction.minimalCanonicalEquiv` at the
  cascade's trace presentation.
* `traceAffineReadout`, `traceAffineReadout_of_pinned` — the readout that matters for the
  routing line: the fixed affine maps still possible. Once the version space has pinned the
  trace, that set is the single map `wordFiberMap C W` (B2).
-/

noncomputable section

namespace NeuralArtifacts.CertifiedChain

open TLT.TemperedDesignLaw.MuxHierarchy
open PresentationRelative

variable {d L : ℕ}

/-! ## The cascade as an inference problem -/

/-- The trace queries of a cascade: the atom `⟨i, b⟩` cuts the candidate inputs down to
those whose layer-`i` branch letter is `b`. -/
def traceQuery (C : MuxCascade d L) : TraceAtom C → Set (Fin d → ℝ) :=
  fun a => {y | C.trace y a.1 = a.2}

/-- The version space of a list of trace atoms is the trace fiber those atoms cut out. -/
theorem version_traceQuery (C : MuxCascade d L) (s : List (TraceAtom C)) :
    VersionSpace.version (traceQuery C) s = {y | ∀ a ∈ s, C.trace y a.1 = a.2} := by
  induction s with
  | nil => ext y; simp [VersionSpace.version]
  | cons a s ih =>
      ext y
      simp only [VersionSpace.version_cons, ih, traceQuery, Set.mem_inter_iff,
        Set.mem_setOf_eq, List.mem_cons, forall_eq_or_imp]

/-- The state the machine reaches after reading a word is that word's trace fiber. -/
theorem eval_generator_traceQuery (C : MuxCascade d L) (s : List (TraceAtom C)) :
    (Inference.eval (VersionSpace.generator (traceQuery C)) s).val
      = {y | ∀ a ∈ s, C.trace y a.1 = a.2} := by
  rw [VersionSpace.eval_generator, version_traceQuery]

/-! ## The machine of an inference problem -/

/-- The machine of a presentation-indexed inference problem: the state is the surviving
version space, one query per step, and the readout is whatever the version space
determines. -/
def latticeMachine {R : Type*} [SemilatticeInf R] [OrderTop R] {P Y : Type*}
    (g : P → R) (rho : R → Y) : Moore R P Y where
  initial := ⊤
  step r p := r ⊓ g p
  out := rho

theorem latticeMachine_runFrom {R : Type*} [SemilatticeInf R] [OrderTop R] {P Y : Type*}
    (g : P → R) (rho : R → Y) (r : R) (s : List P) :
    (latticeMachine g rho).runFrom r s = r ⊓ Inference.eval g s := by
  induction s generalizing r with
  | nil => simp [Moore.runFrom, Inference.eval]
  | cons p s ih =>
      show (latticeMachine g rho).runFrom (r ⊓ g p) s = _
      rw [ih, Inference.eval_cons, inf_assoc]

@[simp] theorem latticeMachine_run {R : Type*} [SemilatticeInf R] [OrderTop R] {P Y : Type*}
    (g : P → R) (rho : R → Y) (s : List P) :
    (latticeMachine g rho).run s = Inference.eval g s := by
  have h := latticeMachine_runFrom g rho ⊤ s
  rwa [top_inf_eq] at h

/-- The machine is correct on every history, not on a sample. -/
theorem latticeMachine_correct {R : Type*} [SemilatticeInf R] [OrderTop R] {P Y : Type*}
    (g : P → R) (rho : R → Y) : Inference.Correct (latticeMachine g rho) g rho := by
  intro s
  show rho ((latticeMachine g rho).run s) = rho (Inference.eval g s)
  rw [latticeMachine_run]

/-! ## The cascade's trace machine and its minimal machine -/

/-- The cascade's machine at its trace presentation: the state is the surviving trace fiber,
the alphabet is the trace atoms. -/
def traceMachine (C : MuxCascade d L) {Y : Type*}
    (rho : VersionSpace.Reachable (traceQuery C) → Y) :
    Moore (VersionSpace.Reachable (traceQuery C)) (TraceAtom C) Y :=
  latticeMachine (VersionSpace.generator (traceQuery C)) rho

theorem traceMachine_correct (C : MuxCascade d L) {Y : Type*}
    (rho : VersionSpace.Reachable (traceQuery C) → Y) :
    Inference.Correct (traceMachine C rho) (VersionSpace.generator (traceQuery C)) rho :=
  latticeMachine_correct _ rho

/-- **B3 (extraction at the trace).** The minimal machine of the cascade read at its trace
presentation is the canonical inference state of the readout. All-horizon (the equivalence
is through observational equivalence, quantified over every continuation) and exact. -/
def traceMinimalEquiv (C : MuxCascade d L) {Y : Type*}
    (rho : VersionSpace.Reachable (traceQuery C) → Y) :
    Extraction.MinState (Extraction.reachableMachine (traceMachine C rho))
      ≃ Inference.State rho :=
  Extraction.minimalCanonicalEquiv (traceMachine C rho)
    (VersionSpace.generator (traceQuery C)) rho
    (VersionSpace.generated (traceQuery C)) (traceMachine_correct C rho)

/-- Extracted semantics and observational equivalence coincide on the trace machine. -/
theorem traceDelta_eq_iff_obsEq (C : MuxCascade d L) {Y : Type*}
    (rho : VersionSpace.Reachable (traceQuery C) → Y)
    (q r : (traceMachine C rho).Reach) :
    Inference.delta (traceMachine C rho) (VersionSpace.generator (traceQuery C)) rho q
        = Inference.delta (traceMachine C rho) (VersionSpace.generator (traceQuery C)) rho r
      ↔ (traceMachine C rho).ObsEq q.val r.val :=
  Extraction.delta_eq_iff_obsEq (traceMachine C rho) (VersionSpace.generator (traceQuery C))
    rho (VersionSpace.generated (traceQuery C)) (traceMachine_correct C rho) q r

/-! ## The readout of the routing line -/

/-- The affine readout of a trace version space: the fixed affine maps the surviving inputs
still allow. -/
def traceAffineReadout (C : MuxCascade d L) :
    VersionSpace.Reachable (traceQuery C) → Set (AffineSelfMap d) :=
  fun V => (fun y => C.fiberMap y) '' V.val

/-- Once the surviving version space has pinned the trace to a word, the affine readout is
the single map that word determines (B2). The extracted state names the affine map
exactly. -/
theorem traceAffineReadout_of_pinned (C : MuxCascade d L)
    (V : VersionSpace.Reachable (traceQuery C)) (W : (i : Fin L) → Fin (C.arity i))
    (hpin : ∀ y ∈ V.val, C.trace y = W) (hne : V.val.Nonempty) :
    traceAffineReadout C V = {wordFiberMap C W} := by
  ext A
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff]
    show C.fiberMap y = wordFiberMap C W
    rw [fiberMap_eq_wordFiberMap, hpin y hy]
  · rintro hA
    obtain ⟨y, hy⟩ := hne
    refine ⟨y, hy, ?_⟩
    show C.fiberMap y = A
    rw [Set.mem_singleton_iff] at hA
    rw [fiberMap_eq_wordFiberMap, hpin y hy, hA]

/-- **B3 at the cascade's affine readout.** -/
def cascadeTraceMinimalEquiv (C : MuxCascade d L) :
    Extraction.MinState (Extraction.reachableMachine (traceMachine C (traceAffineReadout C)))
      ≃ Inference.State (traceAffineReadout C) :=
  traceMinimalEquiv C (traceAffineReadout C)

end NeuralArtifacts.CertifiedChain

end

import NeuralArtifacts.GuardedProjection

/-!
# 24. Building exact guards for finite neural computation graphs

This supplies the graph-language bridge used by the projection theorem.
Continuous operations include affine maps and products of variable weights
with activations. Hard attention is represented by its finite tie-broken
comparison guards, not by a continuity assertion.
-/
noncomputable section
open Classical Function
namespace NeuralArtifacts.Regularity
open Neural

namespace Guard
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def truth : Guard X := le (fun _ => 0) (fun _ => 0) continuous_const continuous_const

def all : List (Guard X) -> Guard X
  | [] => truth
  | p :: rest => and p (all rest)

def any : List (Guard X) -> Guard X
  | [] => not truth
  | p :: rest => or p (any rest)

@[simp] theorem holds_all (ps : List (Guard X)) (x : X) :
    (all ps).holds x ↔ ∀ p ∈ ps, p.holds x := by
  induction ps with
  | nil => simp [all, truth, holds]
  | cons p ps ih => simp [all, holds, ih]

@[simp] theorem holds_any (ps : List (Guard X)) (x : X) :
    (any ps).holds x ↔ ∃ p ∈ ps, p.holds x := by
  induction ps with
  | nil => simp [any, truth, holds]
  | cons p ps ih => simp [any, holds, ih]

def pullback (f : Y -> X) (hf : Continuous f) : Guard X -> Guard Y
  | le a b ha hb => le (a ∘ f) (b ∘ f) (ha.comp hf) (hb.comp hf)
  | and p q => and (pullback f hf p) (pullback f hf q)
  | or p q => or (pullback f hf p) (pullback f hf q)
  | not p => not (pullback f hf p)

@[simp] theorem pullback_exact (f : Y -> X) (hf : Continuous f) (p : Guard X) (y : Y) :
    (pullback f hf p).holds y ↔ p.holds (f y) := by
  induction p <;> simp_all [pullback, holds, Function.comp_def]
end Guard

/-- A finite register instruction. Every index denotes an operational register. -/
inductive Instruction (d : Nat) where
  | continuous (f : (Fin d -> Real) -> Real) (hf : Continuous f)
  | relu (source : Fin d)
  | attention (k : Nat) (scores values : Fin (k + 1) -> Fin d)

namespace Instruction
variable {d : Nat}

def eval : Instruction d -> (Fin d -> Real) -> Real
  | continuous f _, x => f x
  | relu j, x => Neural.relu (x j)
  | attention _ scores values, x =>
    x (values (argmax (fun i => x (scores i))))

def branchGuard (k : Nat) (scores values : Fin (k + 1) -> Fin d)
    (i : Fin (k + 1)) : Guard ((Fin d -> Real) × Real) :=
  Guard.and
    (Guard.eq Prod.snd (fun z => z.1 (values i)) continuous_snd
      ((continuous_apply _).comp continuous_fst))
    (Guard.all ((List.ofFn (fun j : Fin (k + 1) =>
      Guard.le (fun z => z.1 (scores j)) (fun z => z.1 (scores i))
        ((continuous_apply _).comp continuous_fst) ((continuous_apply _).comp continuous_fst))) ++
      (List.ofFn (fun j : Fin i.val =>
        Guard.lt (fun z => z.1 (scores ⟨j.val, j.isLt.trans i.isLt⟩))
          (fun z => z.1 (scores i))
          ((continuous_apply _).comp continuous_fst) ((continuous_apply _).comp continuous_fst)))))

def graph : Instruction d -> Guard ((Fin d -> Real) × Real)
  | continuous f hf => Guard.eq Prod.snd (f ∘ Prod.fst) continuous_snd (hf.comp continuous_fst)
  | relu j => Guard.pullback (fun z => (z.1 j, z.2))
      (((continuous_apply _).comp continuous_fst).prodMk continuous_snd) reluGraph
  | attention k scores values => Guard.any
      (List.ofFn (fun i => branchGuard k scores values i))

theorem branchGuard_exact (k : Nat) (scores values : Fin (k + 1) -> Fin d)
    (i : Fin (k + 1)) (x : Fin d -> Real) (y : Real) :
    (branchGuard k scores values i).holds (x, y) ↔
      y = x (values i) ∧ argmax (fun j => x (scores j)) = i := by
  rw [argmax_characterization]
  simp only [branchGuard, Guard.holds, Guard.holds_eq, Guard.holds_all,
    List.mem_append, List.mem_ofFn]
  constructor
  · rintro ⟨hy, h⟩
    refine ⟨hy, ?_, ?_⟩
    · intro j; exact h _ (Or.inl ⟨j, rfl⟩)
    · intro j hj
      have hlt : j.val < i.val := hj
      simpa using h _ (Or.inr ⟨⟨j.val, hlt⟩, rfl⟩)
  · rintro ⟨hy, hmax, hfirst⟩
    refine ⟨hy, ?_⟩
    intro p hp
    rcases hp with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact hmax j
    · exact (Guard.holds_lt _ _ _ _ _).mpr
        (hfirst ⟨j.val, j.isLt.trans i.isLt⟩ j.isLt)

theorem graph_exact (op : Instruction d) (x : Fin d -> Real) (y : Real) :
    op.graph.holds (x, y) ↔ y = op.eval x := by
  cases op with
  | continuous f hf => simp [graph, Guard.holds_eq, eval, Function.comp_def]
  | relu j => simp [graph, Guard.pullback_exact, reluGraph_exact, eval]
  | attention k scores values =>
    simp only [graph, Guard.holds_any, List.mem_ofFn]
    constructor
    · rintro ⟨p, ⟨i, rfl⟩, hp⟩
      obtain ⟨hy, hi⟩ := (branchGuard_exact k scores values i x y).mp hp
      simpa [eval, hi] using hy
    · intro hy
      refine ⟨branchGuard k scores values (argmax (fun j => x (scores j))), ?_, ?_⟩
      · exact ⟨_, rfl⟩
      · exact (branchGuard_exact _ _ _ _ _ _).mpr ⟨hy, rfl⟩
end Instruction

/-- One register write; residual additions are continuous instructions before
this write and can use both old-payload and update coordinates. -/
structure RegisterStep (d : Nat) where
  destination : Fin d
  operation : Instruction d

namespace RegisterStep
variable {d : Nat}

def eval (s : RegisterStep d) (x : Fin d -> Real) : Fin d -> Real :=
  Function.update x s.destination (s.operation.eval x)

def graph (s : RegisterStep d) : Guard ((Fin d -> Real) × (Fin d -> Real)) :=
  Guard.and
    (Guard.pullback (fun z => (z.1, z.2 s.destination))
      (continuous_fst.prodMk ((continuous_apply _).comp continuous_snd)) s.operation.graph)
    (Guard.all (List.ofFn (fun j : Fin d =>
      if j = s.destination then Guard.truth else
        Guard.eq (fun z => z.2 j) (fun z => z.1 j)
          ((continuous_apply _).comp continuous_snd) ((continuous_apply _).comp continuous_fst))))

theorem graph_exact (s : RegisterStep d) (x y : Fin d -> Real) :
    s.graph.holds (x, y) ↔ y = s.eval x := by
  have hgraph : s.graph.holds (x, y) ↔
      y s.destination = s.operation.eval x ∧
        ∀ j : Fin d, j ≠ s.destination -> y j = x j := by
    simp only [graph, Guard.holds, Guard.pullback_exact, Instruction.graph_exact,
      Guard.holds_all, List.mem_ofFn]
    constructor
    · rintro ⟨hdest, hothers⟩
      refine ⟨hdest, ?_⟩
      intro j hj
      have hh := hothers _ ⟨j, rfl⟩
      simpa [hj, Guard.holds_eq] using hh
    · rintro ⟨hdest, hothers⟩
      refine ⟨hdest, ?_⟩
      intro p hp
      obtain ⟨j, rfl⟩ := hp
      by_cases hj : j = s.destination
      · simp [hj, Guard.truth, Guard.holds]
      · simpa [hj, Guard.holds_eq] using hothers j hj
  rw [hgraph]
  constructor
  · rintro ⟨hdest, hothers⟩
    funext j
    by_cases hj : j = s.destination
    · subst j; simpa [eval] using hdest
    · simpa [eval, Function.update_of_ne hj] using hothers j hj
  · intro hy
    subst y
    constructor
    · simp [eval]
    · intro j hj
      simp [eval, Function.update_of_ne hj]

end RegisterStep

/-- Existence of a finite neural trace is a finite-dimensional guarded
projection. The guard may include parameter constraints and the deviation
inequality, in addition to all RegisterStep.graph constraints. -/
theorem guarded_network_event_borel (p v z : Nat)
    (constraints : List (Guard ((Fin p -> Real) × (Fin v -> Real) × (Fin z -> Real)))) :
    MeasurableSet {sample : Fin z -> Real |
      ∃ parameters trace, ∀ c ∈ constraints, c.holds (parameters, trace, sample)} := by
  simpa [Guard.holds_all] using finite_dimensional_existential_borel p v z (Guard.all constraints)

end NeuralArtifacts.Regularity

end -- noncomputable section

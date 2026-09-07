import NeuralArtifacts.Hardening

/-!
# 22. Measurable finite argmax and uniform deviation events

The individual-network theorem and the parameter-uniform event theorem are
separate. Discontinuity is not used as evidence of nonmeasurability.
-/
noncomputable section
open Classical Function MeasureTheory
open scoped BigOperators
namespace NeuralArtifacts.Regularity
open Neural

variable {X : Type*} [MeasurableSpace X]

/-- Countable intersection, in set-builder form. -/
theorem measurableSet_setOf_forall {Y : Type*} [MeasurableSpace Y] {iota : Sort*}
    [Countable iota] {p : iota -> Y -> Prop} (h : ∀ i, MeasurableSet {y | p i y}) :
    MeasurableSet {y | ∀ i, p i y} := by
  have hs : {y : Y | ∀ i, p i y} = ⋂ i, {y | p i y} := by
    ext y; simp
  rw [hs]
  exact MeasurableSet.iInter h

/-- Countable union, in set-builder form. -/
theorem measurableSet_setOf_exists {Y : Type*} [MeasurableSpace Y] {iota : Sort*}
    [Countable iota] {p : iota -> Y -> Prop} (h : ∀ i, MeasurableSet {y | p i y}) :
    MeasurableSet {y | ∃ i, p i y} := by
  have hs : {y : Y | ∃ i, p i y} = ⋃ i, {y | p i y} := by
    ext y; simp
  rw [hs]
  exact MeasurableSet.iUnion h

theorem argmax_event {n : Nat} (score : X -> Fin (n + 1) -> Real)
    (hscore : ∀ i, Measurable (fun x => score x i)) (i : Fin (n + 1)) :
    MeasurableSet {x | argmax (score x) = i} := by
  have he : {x | argmax (score x) = i} =
      {x | ∀ j, score x j ≤ score x i} ∩
      {x | ∀ j : {j : Fin (n + 1) // j < i}, score x j.val < score x i} := by
    ext x
    simp only [argmax_characterization, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hm, hf⟩; exact ⟨hm, fun j => hf j.val j.property⟩
    · rintro ⟨hm, hf⟩; exact ⟨hm, fun j hj => hf ⟨j, hj⟩⟩
  rw [he]
  apply MeasurableSet.inter
  · exact measurableSet_setOf_forall (fun j => measurableSet_le (hscore j) (hscore i))
  · exact measurableSet_setOf_forall (fun j => measurableSet_lt (hscore j.val) (hscore i))

/-- With the discrete sigma-algebra on the finite index set, all fibres suffice. -/
theorem measurable_argmax {n : Nat} (score : X -> Fin (n + 1) -> Real)
    (hscore : ∀ i, Measurable (fun x => score x i)) :
    Measurable (fun x => argmax (score x)) := by
  apply measurable_to_countable'
  intro i
  exact argmax_event score hscore i

/-- Explicit finite branch sum avoids a continuity assumption at tie surfaces. -/
theorem measurable_hard_output {n : Nat} (score value : X -> Fin (n + 1) -> Real)
    (hscore : ∀ i, Measurable (fun x => score x i))
    (hvalue : ∀ i, Measurable (fun x => value x i)) :
    Measurable (fun x => hardAttention (score x) (value x)) := by
  have he : (fun x => hardAttention (score x) (value x)) =
      (fun x => ∑ i, if argmax (score x) = i then value x i else 0) := by
    funext x
    simp [hardAttention]
  rw [he]
  apply Finset.measurable_sum
  intro i hi
  exact Measurable.ite (argmax_event score hscore i) (hvalue i) measurable_const

theorem measurable_relu {f : X -> Real} (hf : Measurable f) :
    Measurable (fun x => relu (f x)) := measurable_const.max hf

theorem measurable_softmax {I : Type*} [Fintype I] [Nonempty I]
    (score : X -> I -> Real) (hscore : ∀ i, Measurable (fun x => score x i))
    (T : Real) (i : I) : Measurable (fun x => (softmax (score x) T).weight i) := by
  unfold softmax partition
  exact ((hscore i).div_const T).exp.div
    (Finset.measurable_sum _ (fun j _ => ((hscore j).div_const T).exp))

def empirical {Theta Z : Type*} (loss : Theta -> Z -> Real) (theta : Theta)
    {m : Nat} (sample : Fin m -> Z) : Real :=
  (∑ i, loss theta (sample i)) / (m : Real)

theorem measurable_empirical {Theta Z : Type*} [MeasurableSpace Z]
    (loss : Theta -> Z -> Real) (theta : Theta) (m : Nat)
    (hloss : Measurable (loss theta)) :
    Measurable (fun sample : Fin m -> Z => empirical loss theta sample) := by
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i hi
  exact hloss.comp (measurable_pi_apply i)

/-- Population losses are fixed finite real constants, e.g. defined expectations.
No interchange of an uncountable supremum and measurability is used. -/
theorem finite_uniform_deviation {Theta Z : Type*} [Fintype Theta]
    [MeasurableSpace Z] (loss : Theta -> Z -> Real) (population : Theta -> Real)
    (m : Nat) (eps : Real) (hloss : ∀ theta, Measurable (loss theta)) :
    MeasurableSet {sample : Fin m -> Z |
      ∃ theta, eps < |population theta - empirical loss theta sample|} := by
  apply measurableSet_setOf_exists
  intro theta
  exact measurableSet_lt measurable_const
    ((measurable_const.sub (measurable_empirical loss theta m (hloss theta))).abs)

/-- Finite parameter alphabets include every fixed-width fixed-precision network. -/
theorem finite_precision_deviation {Z : Type*} [MeasurableSpace Z]
    (W b m : Nat) (loss : (Fin W -> Fin b) -> Z -> Real)
    (population : (Fin W -> Fin b) -> Real) (eps : Real)
    (hloss : ∀ theta, Measurable (loss theta)) :
    MeasurableSet {sample : Fin m -> Z |
      ∃ theta, eps < |population theta - empirical loss theta sample|} :=
  finite_uniform_deviation loss population m eps hloss

end NeuralArtifacts.Regularity

end -- noncomputable section

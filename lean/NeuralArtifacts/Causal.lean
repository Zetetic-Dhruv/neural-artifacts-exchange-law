import NeuralArtifacts.Queries
import NeuralArtifacts.Stability

/-!
# 20. Finite acyclic structural causal models and intervention preservation

All predecessors of node i are indexed by Fin i.val. An equation may ignore
coordinates that are not parents. This gives an actual topological interpreter
and explicitly constructs its tuple-forming ReLU implementation.
-/
noncomputable section
open Classical Function
open scoped BigOperators
namespace NeuralArtifacts.Causal
open Neural

structure SCM (n : Nat) (S U : Type*) where
  equation : (i : Fin n) -> (Fin i.val -> S) -> U -> S

variable {n : Nat} {S U : Type*}

def earlier (i : Fin n) (j : Fin i.val) : Fin n := ⟨j.val, j.isLt.trans i.isLt⟩

def eval (M : SCM n S U) (intervene : Fin n -> Option S) (u : U) (i : Fin n) : S :=
  match intervene i with
  | some s => s
  | none => M.equation i (fun j => eval M intervene u (earlier i j)) u
termination_by i.val
decreasing_by exact j.isLt

/-- Native intervention semantics: replace an equation, not its observational input. -/
theorem eval_intervened (M : SCM n S U) (I : Fin n -> Option S) (u : U)
    (i : Fin n) (s : S) (h : I i = some s) : eval M I u i = s := by
  rw [eval, h]

theorem eval_unintervened (M : SCM n S U) (I : Fin n -> Option S) (u : U)
    (i : Fin n) (h : I i = none) :
    eval M I u i = M.equation i (fun j => eval M I u (earlier i j)) u := by
  rw [eval, h]

def Satisfies (M : SCM n S U) (I : Fin n -> Option S) (u : U) (v : Fin n -> S) : Prop :=
  ∀ i, v i = match I i with
    | some s => s
    | none => M.equation i (fun j => v (earlier i j)) u

theorem eval_satisfies (M : SCM n S U) (I : Fin n -> Option S) (u : U) :
    Satisfies M I u (eval M I u) := by
  intro i
  rw [eval]

theorem solution_unique (M : SCM n S U) (I : Fin n -> Option S) (u : U)
    (v : Fin n -> S) (hv : Satisfies M I u v) : v = eval M I u := by
  funext i
  have aux : ∀ k, ∀ i : Fin n, i.val = k -> v i = eval M I u i := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hi
      rw [hv i, eval]
      cases hI : I i with
      | some s => rfl
      | none =>
        show M.equation i (fun j => v (earlier i j)) u
            = M.equation i (fun j => eval M I u (earlier i j)) u
        congr 1
        funext j
        exact ih j.val (by simp [<- hi]) (earlier i j) rfl
  exact aux i.val i rfl

section NeuralRealization
variable [Fintype S] [DecidableEq S]

def retrieved (payload : Fin n -> S -> Real) (i : Fin n) :
    (Sigma (fun _ : Fin i.val => S)) -> Real :=
  fun z => hardAttention (fun _ : Fin 1 => 0)
    (fun _ => payload (earlier i z.1)) z.2

omit [Fintype S] in
@[simp] theorem retrieved_oneHot (values : Fin n -> S) (i : Fin n) :
    retrieved (fun j => oneHot (values j)) i =
      tupleInput (fun j => values (earlier i j)) := by
  funext z
  rfl

/-- Actual recursive circuit: each predecessor is retrieved by a singleton
attention head; the FFN forms conjunctions and applies the structural table. -/
def neuralEval (M : SCM n S U) (I : Fin n -> Option S) (u : U) (i : Fin n) : S -> Real :=
  match I i with
  | some s => oneHot s
  | none =>
    (tupleFFN (fun parents => M.equation i parents u)).eval
      (fun z : Sigma (fun _ : Fin i.val => S) =>
        hardAttention (fun _ : Fin 1 => 0)
          (fun _ => neuralEval M I u (earlier i z.1)) z.2)
termination_by i.val
decreasing_by exact z.1.isLt

/-- Nodewise equality for every intervention and every exogenous assignment. -/
theorem intervention_preservation (M : SCM n S U) (I : Fin n -> Option S) (u : U) :
    ∀ i, neuralEval M I u i = oneHot (eval M I u i) := by
  have aux : ∀ k, ∀ i : Fin n, i.val = k ->
      neuralEval M I u i = oneHot (eval M I u i) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hi
      rw [neuralEval, eval]
      cases hI : I i with
      | some s => rfl
      | none =>
        have hinput :
            (fun z : Sigma (fun _ : Fin i.val => S) =>
              hardAttention (fun _ : Fin 1 => 0)
                (fun _ => neuralEval M I u (earlier i z.1)) z.2) =
            tupleInput (fun j => eval M I u (earlier i j)) := by
          funext z
          simp only [singleton_hard]
          rw [ih z.1.val (by simp [<- hi]) (earlier i z.1) rfl]
          rfl
        rw [hinput]
        exact tupleFFN_oneHot _ _
  intro i
  exact aux i.val i rfl

/-- A joint observable tuple is also formed within the FFN. -/
theorem joint_observable_preservation {J O : Type*} [Fintype J] [DecidableEq J]
    [DecidableEq O] (M : SCM n S U) (I : Fin n -> Option S) (u : U)
    (nodes : J -> Fin n) (f : (J -> S) -> O) :
    (tupleFFN f).eval (fun z : Sigma (fun _ : J => S) => neuralEval M I u (nodes z.1) z.2) =
      oneHot (f (fun j => eval M I u (nodes j))) := by
  have h : (fun z : Sigma (fun _ : J => S) => neuralEval M I u (nodes z.1) z.2) =
      tupleInput (fun j => eval M I u (nodes j)) := by
    funext z
    rw [intervention_preservation]
    rfl
  rw [h]
  exact tupleFFN_oneHot f _

/-- Exact exogenous averaging preserves distributions, not only support. -/
theorem distribution_preservation [Fintype U] (M : SCM n S U)
    (I : Fin n -> Option S) (mass : U -> Real) (i : Fin n) (s : S) :
    (∑ u, mass u * neuralEval M I u i s) =
      ∑ u, if eval M I u i = s then mass u else 0 := by
  apply Finset.sum_congr rfl
  intro u hu
  rw [intervention_preservation]
  by_cases h : eval M I u i = s
  · simp [oneHot, h]
  · simp [oneHot, h, Ne.symm h]
end NeuralRealization

namespace TwinWitness

/-- X := U; Y := X. -/
def mediated : SCM 2 Bool Bool where
  equation i parents u := if h : i.val = 0 then u else parents ⟨0, by omega⟩

/-- X := U; Y := U. The common cause is preserved when X is intervened on. -/
def commonCause : SCM 2 Bool Bool where
  equation _ _ u := u

def observe : Fin 2 -> Option Bool := fun _ => none

def setXFalse : Fin 2 -> Option Bool := fun i => if i = 0 then some false else none

theorem observational_equivalence (u : Bool) :
    eval mediated observe u = eval commonCause observe u := by
  funext i
  fin_cases i <;> simp [eval, mediated, commonCause, observe, earlier]

theorem interventional_separation :
    eval mediated setXFalse true 1 = false ∧ eval commonCause setXFalse true 1 = true := by
  constructor <;> simp [eval, mediated, commonCause, setXFalse, earlier]

theorem y_false_probability_mediated :
    (∑ u : Bool, (1 / 2 : Real) * oneHot (eval mediated setXFalse u 1) false) = 1 := by
  norm_num [Fintype.sum_bool, eval, mediated, setXFalse, earlier, oneHot]

theorem y_false_probability_commonCause :
    (∑ u : Bool, (1 / 2 : Real) * oneHot (eval commonCause setXFalse u 1) false) = 1 / 2 := by
  norm_num [Fintype.sum_bool, eval, commonCause, setXFalse, earlier, oneHot]
end TwinWitness

end NeuralArtifacts.Causal

end -- noncomputable section

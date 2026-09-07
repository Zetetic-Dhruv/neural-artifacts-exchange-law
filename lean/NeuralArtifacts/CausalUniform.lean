import NeuralArtifacts.Causal

/-!
# 27. One fixed causal artifact for all exogenous assignments

The earlier topological proof first specialized structural equations at u.
Here u is an input symbol, not a parameter used to change the FFN weights.
A heterogeneous tuple contains every predecessor and one exogenous symbol.
Thus one set of structural tables realizes all interventions and all
exogenous assignments of a finite SCM. This is the uniform causal compiler.
-/
noncomputable section
open Classical Function
open scoped BigOperators
namespace NeuralArtifacts.Causal.Uniform
open Neural
universe uS uU
variable {n : Nat} {S : Type uS} {U : Type uU}
variable [Fintype S] [DecidableEq S] [Fintype U] [DecidableEq U]

/-- Universe lifting transports a one-hot indicator. -/
theorem oneHot_ulift {A : Type v} [DecidableEq A] (x : A) (v : ULift.{w} A) :
    oneHot (ULift.up x) v = oneHot x v.down := by
  by_cases h : v.down = x
  · rw [ULift.down_inj.mp h]
    simp
  · simp only [oneHot]
    rw [if_neg h, if_neg (fun hc => h (congrArg ULift.down hc))]

/-- The `none` coordinate is the exogenous input; `some j` is predecessor j. -/
def InputSort (i : Fin n) : Option (Fin i.val) -> Type (max uS uU)
  | none => ULift.{uS} U
  | some _ => ULift.{uU} S

instance inputFinite (i : Fin n) (j : Option (Fin i.val)) :
    Fintype (InputSort (S := S) (U := U) i j) := by
  cases j <;> dsimp [InputSort] <;> infer_instance

instance inputDecidableEq (i : Fin n) (j : Option (Fin i.val)) :
    DecidableEq (InputSort (S := S) (U := U) i j) := by
  cases j <;> dsimp [InputSort] <;> infer_instance

def assignment (i : Fin n) (parents : Fin i.val -> S) (u : U) :
    (j : Option (Fin i.val)) -> InputSort (S := S) (U := U) i j
  | none => ULift.up u
  | some j => ULift.up (parents j)

/-- The compiled table depends on M and i, but not on the run's u or intervention. -/
def structuralTable (M : SCM n S U) (i : Fin n)
    (values : (j : Option (Fin i.val)) -> InputSort (S := S) (U := U) i j) : S :=
  M.equation i (fun j => (values (some j)).down) (values none).down

omit [Fintype S] [DecidableEq S] [Fintype U] [DecidableEq U] in
@[simp] theorem structuralTable_assignment (M : SCM n S U) (i : Fin n)
    (parents : Fin i.val -> S) (u : U) :
    structuralTable M i (assignment i parents u) = M.equation i parents u := rfl

/-- This is a literal finite FFN, with one hidden unit per heterogeneous tuple. -/
def fixedFFN (M : SCM n S U) (i : Fin n) := tupleFFN (structuralTable M i)

def neuralEval (M : SCM n S U) (I : Fin n -> Option S) (u : U) (i : Fin n) : S -> Real :=
  match I i with
  | some s => oneHot s
  | none => (fixedFFN M i).eval (fun z : Sigma (InputSort (S := S) (U := U) i) =>
      match z with
      | ⟨none, v⟩ => oneHot (ULift.up u) v
      | ⟨some j, s⟩ =>
        hardAttention (fun _ : Fin 1 => 0)
          (fun _ => neuralEval M I u (earlier i j)) s.down)
termination_by i.val
decreasing_by exact j.isLt

/-- An exact run-by-run theorem for the same compiled parameters. -/
theorem intervention_preservation (M : SCM n S U) (I : Fin n -> Option S) (u : U) :
    ∀ i, neuralEval M I u i = oneHot (Causal.eval M I u i) := by
  have aux : ∀ k, ∀ i : Fin n, i.val = k ->
      neuralEval M I u i = oneHot (Causal.eval M I u i) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hi
      rw [neuralEval, Causal.eval]
      cases hI : I i with
      | some s => rfl
      | none =>
        have hinput :
            (fun z : Sigma (InputSort (S := S) (U := U) i) =>
              match z with
              | ⟨none, v⟩ => oneHot (ULift.up u) v
              | ⟨some j, s⟩ =>
                hardAttention (fun _ : Fin 1 => 0)
                  (fun _ => neuralEval M I u (earlier i j)) s.down) =
            tupleInput (assignment i (fun j => Causal.eval M I u (earlier i j)) u) := by
          funext z
          rcases z with ⟨j, value⟩
          cases j with
          | none => rfl
          | some j =>
            simp only [singleton_hard]
            rw [ih j.val (by simp [<- hi]) (earlier i j) rfl]
            exact (oneHot_ulift _ _).symm
        rw [hinput]
        exact tupleFFN_oneHot (structuralTable M i) _
  intro i
  exact aux i.val i rfl

/-- Exact averaging over exogenous inputs preserves every marginal under do(I). -/
theorem distribution_preservation (M : SCM n S U) (I : Fin n -> Option S)
    (mass : U -> Real) (i : Fin n) (s : S) :
    (∑ u, mass u * neuralEval M I u i s) =
      ∑ u, if Causal.eval M I u i = s then mass u else 0 := by
  apply Finset.sum_congr rfl
  intro u hu
  rw [intervention_preservation]
  by_cases h : Causal.eval M I u i = s
  · simp [oneHot, h]
  · simp [oneHot, h, Ne.symm h]

/-- Arbitrary finite joint queries use a further fixed tuple-forming FFN. -/
theorem joint_query_preservation {J O : Type*} [Fintype J] [DecidableEq J]
    [DecidableEq O] (M : SCM n S U) (I : Fin n -> Option S) (u : U)
    (nodes : J -> Fin n) (query : (J -> S) -> O) :
    (tupleFFN query).eval
      (fun z : Sigma (fun _ : J => S) => neuralEval M I u (nodes z.1) z.2) =
      oneHot (query (fun j => Causal.eval M I u (nodes j))) := by
  have hinput :
      (fun z : Sigma (fun _ : J => S) => neuralEval M I u (nodes z.1) z.2) =
      tupleInput (fun j => Causal.eval M I u (nodes j)) := by
    funext z
    rw [intervention_preservation]
    rfl
  rw [hinput]
  exact tupleFFN_oneHot query _

end NeuralArtifacts.Causal.Uniform
end -- noncomputable section

import NeuralArtifacts.ForestCompiler

/-!
# 16. Constructing the shared schedule from a code tree

This file discharges the scheduling interface of ForestCompiler. Token
positions are actual nodes of the tree, not external program identifiers.
-/
noncomputable section
open Classical Function
open scoped BigOperators
namespace NeuralArtifacts.Neural.Code
universe u v w
variable {X : Type u} {S : Type v} {F : Type w}
variable [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]
variable [Inhabited S] [Fintype F]

/-- Each occurrence is a distinct token. DAG sharing can be unfolded first. -/
def Nodes : Code X S F -> Type (max u v w)
  | leaf _ => PUnit
  | gate n _ children _ => Option (Sigma (fun j : Fin (n + 1) => Nodes (children j)))

instance nodesFinite : (c : Code X S F) -> Fintype (Nodes c)
  | leaf _ => inferInstanceAs (Fintype PUnit)
  | gate n keys children out => by
    letI : ∀ j, Fintype (Nodes (children j)) := fun j => nodesFinite (children j)
    exact inferInstanceAs (Fintype (Option (Sigma (fun j => Nodes (children j)))))

instance nodesDecidableEq (c : Code X S F) : DecidableEq (Nodes c) := Classical.decEq _

def root : (c : Code X S F) -> Nodes c
  | leaf _ => PUnit.unit
  | gate _ _ _ _ => none

def level : (c : Code X S F) -> Nodes c -> Nat
  | leaf _, _ => 0
  | gate n keys children out, none => depth (gate n keys children out)
  | gate _ _ children _, some z => level (children z.1) z.2

def target (phi : X -> F -> Real) : (c : Code X S F) -> X -> Nodes c -> S
  | leaf f, x, _ => f x
  | gate n keys children out, x, none => eval phi (gate n keys children out) x
  | gate _ _ children _, x, some z => target phi (children z.1) x z.2

def initialSymbols : (c : Code X S F) -> X -> Nodes c -> S
  | leaf f, x, _ => f x
  | gate _ _ _ _, _, none => default
  | gate _ _ children _, x, some z => initialSymbols (children z.1) x z.2

def choose (phi : X -> F -> Real) : (c : Code X S F) -> X -> Nodes c -> Nodes c
  | leaf _, _, _ => PUnit.unit
  | gate _ keys children _, x, none =>
    let j := argmax (fun j => dot (homogeneous (phi x)) (keys j))
    some ⟨j, root (children j)⟩
  | gate _ _ children _, x, some z => some ⟨z.1, choose phi (children z.1) x z.2⟩

def nodeTable : (c : Code X S F) -> Nodes c -> S -> S
  | leaf _, _ => id
  | gate _ _ _ out, none => out
  | gate _ _ children _, some z => nodeTable (children z.1) z.2

omit [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S] [Inhabited S] [Fintype F] in
@[simp] theorem level_root (c : Code X S F) : level c (root c) = depth c := by
  cases c <;> rfl

omit [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S] [Inhabited S] in
@[simp] theorem target_root (phi : X -> F -> Real) (c : Code X S F) (x : X) :
    target phi c x (root c) = eval phi c x := by
  cases c <;> rfl

omit [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S] [Inhabited S] [Fintype F] in
theorem level_le_depth (c : Code X S F) (v : Nodes c) : level c v ≤ depth c := by
  induction c with
  | leaf f => simp [level, depth]
  | gate n keys children out ih =>
    cases v with
    | none => exact le_rfl
    | some z =>
      have h := ih z.1 z.2
      have hm : depth (children z.1) ≤ Finset.univ.sup (fun j => depth (children j)) :=
        Finset.le_sup (f := fun j => depth (children j)) (Finset.mem_univ z.1)
      simp only [level, depth]
      omega

omit [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S] in
theorem initialize_leaf (phi : X -> F -> Real) (c : Code X S F) (x : X)
    (v : Nodes c) (h : level c v = 0) : initialSymbols c x v = target phi c x v := by
  induction c with
  | leaf f => rfl
  | gate n keys children out ih =>
    cases v with
    | none => simp [level, depth] at h
    | some z => exact ih z.1 z.2 h

omit [Fintype X] in
theorem chosen_child_earlier (phi : X -> F -> Real) (c : Code X S F) (x : X)
    (v : Nodes c) (h : 0 < level c v) : level c (choose phi c x v) < level c v := by
  induction c with
  | leaf f => simp [level] at h
  | gate n keys children out ih =>
    cases v with
    | none =>
      simp only [choose, level, level_root, depth]
      have hm : depth (children (argmax (fun j => dot (homogeneous (phi x)) (keys j)))) ≤
          Finset.univ.sup (fun j => depth (children j)) :=
        Finset.le_sup (f := fun j => depth (children j))
          (Finset.mem_univ (argmax (fun j => dot (homogeneous (phi x)) (keys j))))
      omega
    | some z => exact ih z.1 z.2 h

omit [Fintype X] in
theorem node_semantics (phi : X -> F -> Real) (c : Code X S F) (x : X) (v : Nodes c)
    (h : 0 < level c v) :
    nodeTable c v (target phi c x (choose phi c x v)) = target phi c x v := by
  induction c with
  | leaf f => simp [level] at h
  | gate n keys children out ih =>
    cases v with
    | none => simp [nodeTable, choose, target, target_root, eval]
    | some z => exact ih z.1 z.2 h

def sharedPlan (phi : X -> F -> Real) (c : Code X S F) :
    Schedule (X := X) (S := S) (N := Nodes c) where
  level := level c
  input := initialSymbols c
  active t v := decide (level c v = t + 1)
  choose t x v := if level c v = t + 1 then choose phi c x v else v
  table _ := nodeTable c

/-- After exactly D routing layers every node has its required semantic value. -/
theorem depth_suffices (phi : X -> F -> Real) (c : Code X S F) (x : X)
    (v : Nodes c) : symbols (sharedPlan phi c) x (depth c) v = target phi c x v := by
  apply scheduled_semantics (sharedPlan phi c) x (target phi c x)
  · exact initialize_leaf phi c x
  · intro t v
    simp [sharedPlan]
  · intro t v hv
    have he : level c v = t + 1 := by simpa [sharedPlan] using hv
    have hh := chosen_child_earlier phi c x v (by omega)
    simpa only [sharedPlan, he, if_true] using
      (show level c (choose phi c x v) ≤ t by omega)
  · intro t v hv
    have he : level c v = t + 1 := by simpa [sharedPlan] using hv
    simpa only [sharedPlan, he, if_true] using
      node_semantics phi c x v (by omega)
  · exact level_le_depth c v

/-- Complete shared-block compiler theorem, with all token coordinates tracked. -/
theorem literal_forest_correct {Z : Type*} (phi : X -> F -> Real)
    (c : Code X S F) (fixedCoordinates : Nodes c -> Z -> Real) (x : X) (v : Nodes c) :
    literalRun (sharedPlan phi c) fixedCoordinates x (depth c) v =
      Token.mk (oneHot v) (fixedCoordinates v) (oneHot (target phi c x v)) (fun _ => 0) := by
  rw [literalRun_invariant, depth_suffices]

theorem literal_root_correct {Z : Type*} (phi : X -> F -> Real)
    (c : Code X S F) (fixedCoordinates : Nodes c -> Z -> Real) (x : X) :
    (literalRun (sharedPlan phi c) fixedCoordinates x (depth c) (root c)).payload =
      oneHot (eval phi c x) := by
  rw [literal_forest_correct, target_root]

end NeuralArtifacts.Neural.Code

end -- noncomputable section

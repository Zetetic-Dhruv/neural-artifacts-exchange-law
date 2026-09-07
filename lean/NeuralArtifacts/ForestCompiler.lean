import NeuralArtifacts.Hardening

/-!
# 15. Code trees, extraction from operational matrices, and shared-block execution

The source program is not retained in an auxiliary artifact field. Leaf and
output maps are read back by evaluating the actual FFN on basis vectors.
Parameter permutations therefore preserve the extracted semantics.
-/
noncomputable section
open Classical Function
open scoped BigOperators
namespace NeuralArtifacts.Neural
universe u v w

variable {X : Type u} {S : Type v} {F : Type w}

inductive Code (X : Type u) (S : Type v) (F : Type w) where
  | leaf (table : X -> S)
  | gate (n : Nat) (keys : Fin (n + 1) -> Option F -> Real)
      (children : Fin (n + 1) -> Code X S F) (output : S -> S)

namespace Code
variable [Fintype F]

def eval (phi : X -> F -> Real) : Code X S F -> X -> S
  | leaf f, x => f x
  | gate _ keys children out, x =>
    out (eval phi (children (argmax (fun j => dot (homogeneous (phi x)) (keys j)))) x)

def depth : Code X S F -> Nat
  | leaf _ => 0
  | gate _ _ children _ => 1 + Finset.univ.sup (fun j => depth (children j))

/-- A semantics-preserving local replacement can be made inside any code tree. -/
theorem congr_gate (phi : X -> F -> Real) (n : Nat)
    (keys : Fin (n + 1) -> Option F -> Real)
    (c d : Fin (n + 1) -> Code X S F) (f : S -> S)
    (h : ∀ j x, eval phi (c j) x = eval phi (d j) x) :
    ∀ x, eval phi (gate n keys c f) x = eval phi (gate n keys d f) x := by
  intro x
  exact congrArg f (h _ x)
end Code

variable [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]
variable [Inhabited S] [Fintype F]

/-- Partial outside the one-hot interface; the default is irrelevant on certified inputs. -/
def readSymbol (v : S -> Real) : S :=
  if h : ∃ s, v = oneHot s then Classical.choose h else default

theorem readSymbol_oneHot (s : S) : readSymbol (oneHot s) = s := by
  unfold readSymbol
  rw [dif_pos ⟨s, rfl⟩]
  apply oneHot_injective
  exact (Classical.choose_spec (show ∃ t, oneHot s = oneHot t from ⟨s, rfl⟩)).symm

def readTable {I H : Type*} [Fintype I] [DecidableEq I] [Fintype H]
    (f : FFN I H S) : I -> S := fun i => readSymbol (f.eval (oneHot i))

@[simp] theorem read_compiled_table {I : Type*} [Fintype I] [DecidableEq I]
    (f : I -> S) : readTable (tableFFN f) = f := by
  funext i
  simp [readTable, tableFFN_oneHot, readSymbol_oneHot]

theorem readTable_permute {I H H' : Type*} [Fintype I] [DecidableEq I]
    [Fintype H] [Fintype H'] (f : FFN I H S) (e : H' ≃ H) :
    readTable (f.permute e) = readTable f := by
  funext i
  simp [readTable, FFN.eval_permute]

inductive Artifact (X : Type u) (S : Type v) (F : Type w) where
  | leaf (weights : FFN X X S)
  | gate (n : Nat) (keys : Fin (n + 1) -> Option F -> Real)
      (children : Fin (n + 1) -> Artifact X S F) (weights : FFN S S S)

namespace Artifact

def execute (phi : X -> F -> Real) : Artifact X S F -> X -> (S -> Real)
  | leaf W, x => W.eval (oneHot x)
  | gate _ keys children W, x =>
    W.eval (execute phi (children (argmax (fun j => dot (homogeneous (phi x)) (keys j)))) x)

def extract : Artifact X S F -> Code X S F
  | leaf W => Code.leaf (readTable W)
  | gate n keys children W => Code.gate n keys (fun j => extract (children j)) (readTable W)
end Artifact

namespace Code

def compile : Code X S F -> Artifact X S F
  | leaf f => Artifact.leaf (tableFFN f)
  | gate n keys children f => Artifact.gate n keys (fun j => compile (children j)) (tableFFN f)

omit [Inhabited S] in
/-- All leaf and internal operational matrix evaluations are accounted for. -/
theorem compiler_correct (phi : X -> F -> Real) (c : Code X S F) (x : X) :
    (compile c).execute phi x = oneHot (eval phi c x) := by
  induction c with
  | leaf f => exact tableFFN_oneHot f x
  | gate n keys children f ih =>
    change (tableFFN f).eval ((compile (children _)).execute phi x) = _
    rw [ih]
    exact tableFFN_oneHot f _

omit [Fintype F] in
theorem extract_compile (c : Code X S F) : (compile c).extract = c := by
  induction c with
  | leaf f => simp [compile, Artifact.extract, read_compiled_table]
  | gate n keys children f ih =>
    simp only [compile, Artifact.extract, read_compiled_table]
    congr 1
    funext j
    exact ih j

/-- This is the public round-trip statement; syntactic recovery is not required. -/
theorem semantic_roundtrip (phi : X -> F -> Real) (c : Code X S F) :
    ∀ x, eval phi ((compile c).extract) x = eval phi c x := by
  intro x
  rw [extract_compile]

/-- Exact soft execution with correction, at the same numerical parameters. -/
def executeSoft (phi : X -> F -> Real) (eta T : Real) :
    Code X S F -> X -> (S -> Real)
  | leaf f, x => (tableFFN f).eval (oneHot x)
  | gate _ keys children f, x =>
    let p := softmax (fun j => dot (homogeneous (phi x)) (keys j)) T
    let mixture := fun s => ∑ j, p.weight j * executeSoft phi eta T (children j) x s
    (tableFFN f).eval (fun s => roundSymbol eta (mixture s))

/-- This predicate is a checkable numeric condition at each actual gate; it is
not an assumed equality between the complete soft and hard computations. -/
def MassCertificate (phi : X -> F -> Real) (eta T : Real) : Code X S F -> X -> Prop
  | leaf _, _ => True
  | gate _ keys children _, x =>
    let score := fun j => dot (homogeneous (phi x)) (keys j)
    let labels := fun j => eval phi (children j) x
    (∀ j, MassCertificate phi eta T (children j) x) ∧
    (softmax score T).wrong labels (labels (argmax score)) ≤ eta

omit [Inhabited S] in
theorem soft_execution_exact (phi : X -> F -> Real) (eta T : Real)
    (he0 : 0 ≤ eta) (he : eta < 1 / 2) (c : Code X S F) (x : X)
    (cert : MassCertificate phi eta T c x) :
    executeSoft phi eta T c x = oneHot (eval phi c x) := by
  revert cert
  induction c with
  | leaf f =>
    intro cert
    exact tableFFN_oneHot f x
  | gate n keys children f ih =>
    intro cert
    rcases cert with ⟨hchildren, hmass⟩
    let score := fun j => dot (homogeneous (phi x)) (keys j)
    let labels := fun j => eval phi (children j) x
    have hcorrect :
        (fun s => roundSymbol eta
          (∑ j, (softmax score T).weight j * executeSoft phi eta T (children j) x s)) =
        oneHot (labels (argmax score)) := by
      have hm : ∀ s, (∑ j, (softmax score T).weight j *
          executeSoft phi eta T (children j) x s) = (softmax score T).coord labels s := by
        intro s
        simp_rw [ih _ (hchildren _)]
        exact Probability.mixture_eq_coord _ _ _
      have hkey := (exact_symbol_iff he0 he _ labels _).mpr hmass
      funext s
      rw [hm s]
      exact congrFun hkey s
    change (tableFFN f).eval _ = _
    rw [hcorrect, tableFFN_oneHot]
    rfl
end Code

/-- Summation against a one-hot mask selects a single term. -/
theorem sum_mul_oneHot {U : Type*} [Fintype U] [DecidableEq U]
    (g : U -> Real) (u : U) : (∑ z, g z * oneHot u z) = g u := by
  simp [oneHot]

/-- Soft correction followed by dispatch remains a shared single-hidden-layer
FFN: each output is a linear combination of the two displayed ReLU units. -/
def correctedDispatch {N : Type*} [Fintype N] [DecidableEq N]
    (eta : Real) (f : N -> S -> S) (u : N -> Real) (w : S -> Real) : S -> Real :=
  fun o => ∑ n, ∑ s, oneHot (f n s) o * gatedRound eta (u n) (w s)

omit [Inhabited S] in
theorem correctedDispatch_exact {N I : Type*} [Fintype N] [DecidableEq N] [Fintype I]
    (eta : Real) (he0 : 0 ≤ eta) (he : eta < 1 / 2)
    (f : N -> S -> S) (n : N) (p : Probability I) (label : I -> S) (target : S)
    (hmass : p.wrong label target ≤ eta) :
    correctedDispatch eta f (oneHot n) (p.coord label) = oneHot (f n target) := by
  have hround := (exact_symbol_iff he0 he p label target).mpr hmass
  have hh (m : N) (s : S) :
      gatedRound eta (oneHot n m) (p.coord label s) =
      if m = n then oneHot target s else 0 := by
    by_cases hm : m = n
    · subst m
      simp only [oneHot_self, gatedRound_one, if_true]
      exact congrFun hround s
    · simp [hm, gatedRound_zero he0 he (p.coord_le_one label s)]
  funext o
  simp [correctedDispatch, hh]
  exact sum_mul_oneHot (fun z => oneHot (f n z) o) target

section SharedSchedule
variable {N : Type*} [Fintype N] [DecidableEq N]
variable {Z : Type*}

/-- A topological semantic interface. The selected child is determined by
actual query/key scores in the literal layer below. -/
structure Schedule where
  level : N -> Nat
  input : X -> N -> S
  active : Nat -> N -> Bool
  choose : Nat -> X -> N -> N
  table : Nat -> N -> S -> S

def symbols (plan : Schedule (X := X) (S := S) (N := N)) (x : X) : Nat -> N -> S
  | 0 => plan.input x
  | t + 1 => fun n => if plan.active t n then
      plan.table t n (symbols plan x t (plan.choose t x n)) else symbols plan x t n

def literalLayer (plan : Schedule (X := X) (S := S) (N := N)) (t : Nat) (x : X)
    (tokens : N -> Token (N := N) (S := S) Z) : N -> Token (N := N) (S := S) Z :=
  fun n => feedforwardResidual (plan.active t) (plan.table t)
    (attentionResidual (tokens n) ((tokens (plan.choose t x n)).payload))

def literalRun (plan : Schedule (X := X) (S := S) (N := N))
    (fixedCoordinates : N -> Z -> Real) (x : X) : Nat -> N -> Token (N := N) (S := S) Z
  | 0 => fun n => Token.mk (oneHot n) (fixedCoordinates n) (oneHot (plan.input x n)) (fun _ => 0)
  | t + 1 => literalLayer plan t x (literalRun plan fixedCoordinates x t)

omit [Fintype X] [DecidableEq X] [Inhabited S] in
/-- The entire shared residual state is exact after every layer. -/
theorem literalRun_invariant (plan : Schedule (X := X) (S := S) (N := N))
    (fixedCoordinates : N -> Z -> Real) (x : X) (t : Nat) (n : N) :
    literalRun plan fixedCoordinates x t n =
      Token.mk (oneHot n) (fixedCoordinates n) (oneHot (symbols plan x t n)) (fun _ => 0) := by
  induction t generalizing n with
  | zero => rfl
  | succ t ih =>
    simp only [literalRun, literalLayer]
    rw [ih n, ih (plan.choose t x n)]
    exact shared_block_invariant _ _ _ _ _ _

omit [Fintype S] [DecidableEq S] [Inhabited S] [Fintype N] [DecidableEq N] in
/-- Wiring a finite nonempty mask to its child-indexed keys gives exactly the
parent payload used by the schedule, with no source-program lookup. -/
theorem mask_attention_payload {k : Nat}
    (children : Fin (k + 1) -> N) (query : Z -> Real)
    [Fintype Z] (keys : N -> Z -> Real)
    (tokens : N -> Token (N := N) (S := S) Z) :
    hardAttention (fun i => dot query (keys (children i)))
      (fun i => (tokens (children i)).payload) =
      (tokens (children (argmax (fun i => dot query (keys (children i)))))).payload := rfl

omit [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S] [Inhabited S] [Fintype N] [DecidableEq N] in
/-- The node-indexed schedule realizes every finite acyclic dataflow program:
active nodes are assigned their target value once their parents are complete. -/
theorem scheduled_semantics (plan : Schedule (X := X) (S := S) (N := N))
    (x : X) (target : N -> S)
    (hbase : ∀ n, plan.level n = 0 -> plan.input x n = target n)
    (hact : ∀ t n, plan.active t n = true ↔ plan.level n = t + 1)
    (hparent : ∀ t n, plan.active t n = true ->
      plan.level (plan.choose t x n) ≤ t)
    (hnode : ∀ t n, plan.active t n = true ->
      plan.table t n (target (plan.choose t x n)) = target n) :
    ∀ t n, plan.level n ≤ t -> symbols plan x t n = target n := by
  intro t
  induction t with
  | zero => intro n hn; exact hbase n (by omega)
  | succ t ih =>
    intro n hn
    by_cases ha : plan.active t n = true
    · simp only [symbols, ha, if_true]
      rw [ih _ (hparent t n ha)]
      exact hnode t n ha
    · have hlev : plan.level n ≠ t + 1 := fun h => ha ((hact t n).mpr h)
      have hn' : plan.level n ≤ t := by omega
      have haf : plan.active t n = false := Bool.eq_false_iff.mpr ha
      simp only [symbols, haf, Bool.false_eq_true, if_false]
      exact ih n hn'
end SharedSchedule

end NeuralArtifacts.Neural

end -- noncomputable section

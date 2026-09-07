import NeuralArtifacts.Prelude

/-!
# 12. Literal finite maps, tuple formation, and positionwise dispatch

Every displayed network below is a two-affine-layer ReLU network with
explicit weight entries. A finite map is not assumed to be an FFN.
-/
noncomputable section
open Classical Function
open scoped BigOperators
namespace NeuralArtifacts.Neural
universe u v w

def relu (t : Real) : Real := max 0 t

@[simp] theorem relu_of_nonneg {t : Real} (h : 0 ≤ t) : relu t = t := max_eq_right h
@[simp] theorem relu_of_nonpos {t : Real} (h : t ≤ 0) : relu t = 0 := max_eq_left h
@[simp] theorem relu_zero : relu 0 = 0 := by simp [relu]
@[simp] theorem relu_one : relu 1 = 1 := by norm_num [relu]

def oneHot {I : Type u} [DecidableEq I] (i : I) : I -> Real :=
  fun j => if j = i then 1 else 0

@[simp] theorem oneHot_self {I : Type u} [DecidableEq I] (i : I) : oneHot i i = 1 := by
  simp [oneHot]
@[simp] theorem oneHot_ne {I : Type u} [DecidableEq I] {i j : I} (h : j ≠ i) :
    oneHot i j = 0 := by simp [oneHot, h]

theorem oneHot_nonneg {I : Type u} [DecidableEq I] (i j : I) : 0 ≤ oneHot i j := by
  simp only [oneHot]; split_ifs <;> norm_num

theorem oneHot_le_one {I : Type u} [DecidableEq I] (i j : I) : oneHot i j ≤ 1 := by
  simp only [oneHot]; split_ifs <;> norm_num

theorem oneHot_injective {I : Type u} [DecidableEq I] :
    Injective (oneHot (I := I)) := by
  intro i j h
  by_contra hij
  have hc := congrFun h i
  simp [oneHot, hij] at hc

@[simp] theorem sum_oneHot {I : Type u} [Fintype I] [DecidableEq I] (i : I) :
    (∑ j, oneHot i j) = 1 := by simp [oneHot]

/-- All coefficients are operational parameters, not a stored source program. -/
structure FFN (I : Type u) (H : Type v) (O : Type w) where
  inputWeight : H -> I -> Real
  hiddenBias : H -> Real
  outputWeight : O -> H -> Real
  outputBias : O -> Real

namespace FFN
variable {I : Type u} {H : Type v} {O : Type w}
variable [Fintype I] [Fintype H]

def eval (F : FFN I H O) (x : I -> Real) : O -> Real :=
  fun o => (∑ h, F.outputWeight o h *
    relu ((∑ i, F.inputWeight h i * x i) + F.hiddenBias h)) + F.outputBias o

/-- Hidden-neuron permutations leave the function, hence the extracted table, unchanged. -/
def permute {H' : Type*} (F : FFN I H O) (e : H' ≃ H) : FFN I H' O where
  inputWeight h i := F.inputWeight (e h) i
  hiddenBias h := F.hiddenBias (e h)
  outputWeight o h := F.outputWeight o (e h)
  outputBias := F.outputBias

theorem eval_permute {H' : Type*} [Fintype H']
    (F : FFN I H O) (e : H' ≃ H) (x : I -> Real) :
    (F.permute e).eval x = F.eval x := by
  funext o
  unfold eval permute
  congr 1
  exact Equiv.sum_comp e (fun h => F.outputWeight o h *
    relu ((∑ i, F.inputWeight h i * x i) + F.hiddenBias h))
end FFN

section Table
variable {I : Type u} {O : Type v} [Fintype I] [DecidableEq I] [DecidableEq O]

def tableFFN (f : I -> O) : FFN I I O where
  inputWeight h i := if h = i then 1 else 0
  hiddenBias _ := 0
  outputWeight o h := oneHot (f h) o
  outputBias _ := 0

theorem tableFFN_oneHot (f : I -> O) (i : I) :
    (tableFFN f).eval (oneHot i) = oneHot (f i) := by
  funext o
  simp only [FFN.eval, tableFFN, oneHot, relu]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [hb]
  · simp
end Table

section Tuples
variable {J : Type u} [Fintype J] [DecidableEq J]
variable {S : J -> Type v} [∀ j, Fintype (S j)] [∀ j, DecidableEq (S j)]

/-- Equality indicators summed across positions. -/
def agreeCount (x y : (j : J) -> S j) : Nat :=
  (Finset.univ.filter (fun j => x j = y j)).card

omit [DecidableEq J] [∀ j, Fintype (S j)] in
theorem agreeCount_le (x y : (j : J) -> S j) : agreeCount x y ≤ Fintype.card J := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

omit [DecidableEq J] [∀ j, Fintype (S j)] in
theorem agreeCount_eq_card_iff (x y : (j : J) -> S j) :
    agreeCount x y = Fintype.card J ↔ x = y := by
  constructor
  · intro h
    have he : Finset.univ.filter (fun j => x j = y j) = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by simpa [agreeCount] using h.ge)
    funext j
    have hj : j ∈ Finset.univ.filter (fun j => x j = y j) := by rw [he]; simp
    exact (Finset.mem_filter.mp hj).2
  · rintro rfl
    simp [agreeCount]

omit [DecidableEq J] [(j : J) → Fintype (S j)] in
theorem agreeCount_lt_of_ne {x y : (j : J) -> S j} (h : x ≠ y) :
    agreeCount x y < Fintype.card J :=
  lt_of_le_of_ne (agreeCount_le x y) (fun he => h ((agreeCount_eq_card_iff x y).mp he))

omit [DecidableEq J] [∀ j, Fintype (S j)] in
theorem sum_oneHot_agreeCount (x y : (j : J) -> S j) :
    (∑ j, oneHot (x j) (y j)) = (agreeCount x y : Real) := by
  simp [oneHot, agreeCount, eq_comm, Finset.sum_boole]

/-- Empty arity is included: subtraction takes place in the reals, so the
unique empty conjunction has activation ReLU(0 - (0-1)) = 1. -/
def tupleNeuron (v : (j : J) -> S j -> Real) (y : (j : J) -> S j) : Real :=
  relu ((∑ j, v j (y j)) - ((Fintype.card J : Real) - 1))

omit [DecidableEq J] in
theorem tupleNeuron_oneHot (x y : (j : J) -> S j) :
    tupleNeuron (fun j => oneHot (x j)) y = oneHot x y := by
  rw [tupleNeuron, sum_oneHot_agreeCount]
  by_cases h : x = y
  · subst y
    have he := (agreeCount_eq_card_iff x x).mpr rfl
    simp [he, oneHot, relu]
  · have hl := agreeCount_lt_of_ne h
    have hr : (agreeCount x y : Real) ≤ (Fintype.card J : Real) - 1 := by
      have hh : agreeCount x y + 1 ≤ Fintype.card J := hl
      have hcast : (agreeCount x y : Real) + 1 ≤ (Fintype.card J : Real) := by exact_mod_cast hh
      linarith
    rw [relu_of_nonpos (by linarith)]
    simp [oneHot, Ne.symm h]

/-- The tuple input is a block vector, indexed by the dependent sum. -/
def tupleInput (x : (j : J) -> S j) : (Sigma S) -> Real :=
  fun z => oneHot (x z.1) z.2

def tupleFFN {O : Type w} [DecidableEq O] (f : ((j : J) -> S j) -> O) :
    FFN (Sigma S) ((j : J) -> S j) O where
  inputWeight h z := if z.2 = h z.1 then 1 else 0
  hiddenBias _ := 1 - (Fintype.card J : Real)
  outputWeight o h := oneHot (f h) o
  outputBias _ := 0

theorem tupleFFN_oneHot {O : Type w} [DecidableEq O]
    (f : ((j : J) -> S j) -> O) (x : (j : J) -> S j) :
    (tupleFFN f).eval (tupleInput x) = oneHot (f x) := by
  have hhidden (h : (j : J) -> S j) :
      relu ((∑ z : Sigma S, (if z.2 = h z.1 then 1 else 0) * tupleInput x z) +
        (1 - (Fintype.card J : Real))) = oneHot x h := by
    simp only [Fintype.sum_sigma, tupleInput]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    convert tupleNeuron_oneHot x h using 1; unfold tupleNeuron; congr 1; ring
  funext o
  simp only [FFN.eval, tupleFFN, hhidden, add_zero]
  simp [oneHot]
end Tuples

/-- The ordinary two-input conjunction network, with its exact hidden width. -/
def binaryFFN {Q P O : Type*} [Fintype Q] [Fintype P]
    [DecidableEq Q] [DecidableEq P] [DecidableEq O] (f : Q -> P -> O) :
    FFN (Q ⊕ P) (Q × P) O where
  inputWeight h i := match i with
    | Sum.inl q => if q = h.1 then 1 else 0
    | Sum.inr p => if p = h.2 then 1 else 0
  hiddenBias _ := -1
  outputWeight o h := oneHot (f h.1 h.2) o
  outputBias _ := 0

/-- Pair input is concatenation, not an oracle tuple code. -/
def pairInput {Q P : Type*} [DecidableEq Q] [DecidableEq P] (q : Q) (p : P) :
    Q ⊕ P -> Real := Sum.elim (oneHot q) (oneHot p)

theorem binaryFFN_oneHot {Q P O : Type*} [Fintype Q] [Fintype P]
    [DecidableEq Q] [DecidableEq P] [DecidableEq O]
    (f : Q -> P -> O) (q : Q) (p : P) :
    (binaryFFN f).eval (pairInput q p) = oneHot (f q p) := by
  have hh (a : Q) (b : P) :
      relu (oneHot q a + oneHot p b - 1) =
        if (a, b) = (q, p) then 1 else 0 := by
    by_cases ha : a = q <;> by_cases hb : b = p <;>
      simp [oneHot, ha, hb, relu, Prod.mk.injEq]
  funext o
  simp only [FFN.eval, binaryFFN, pairInput, Fintype.sum_sum_type]
  simp only [ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp_rw [show ∀ x y : Real, x + y + -1 = x + y - 1 from by intros; ring]
  simp [hh]

@[simp] theorem binary_hidden_width {Q P : Type*} [Fintype Q] [Fintype P] :
    Fintype.card (Q × P) = Fintype.card Q * Fintype.card P := Fintype.card_prod _ _

section Dispatch
variable {N : Type u} {S : Type v}
variable [Fintype N] [Fintype S] [DecidableEq N] [DecidableEq S]

def dispatch (u : N -> Real) (w : S -> Real) (n : N) (s : S) : Real :=
  relu (u n + w s - 1)

omit [Fintype N] [Fintype S] [DecidableEq S] in
theorem dispatch_selected (n : N) (w : S -> Real) (hw : ∀ s, 0 ≤ w s)
    (s : S) : dispatch (oneHot n) w n s = w s := by
  simp [dispatch, hw]

omit [Fintype N] [Fintype S] [DecidableEq S] in
theorem dispatch_other (n m : N) (hne : m ≠ n) (w : S -> Real)
    (hw : ∀ s, w s ≤ 1) (s : S) : dispatch (oneHot n) w m s = 0 := by
  simp only [dispatch, oneHot_ne hne, zero_add]
  exact relu_of_nonpos (sub_nonpos.mpr (hw s))

def dispatchedMap (f : N -> S -> S) (u : N -> Real) (w : S -> Real) : S -> Real :=
  fun o => ∑ n, ∑ s, oneHot (f n s) o * dispatch u w n s

theorem dispatchedMap_exact (f : N -> S -> S) (n : N) (s : S) :
    dispatchedMap f (oneHot n) (oneHot s) = oneHot (f n s) := by
  funext o
  unfold dispatchedMap
  have hh (m : N) (t : S) :
      dispatch (oneHot n) (oneHot s) m t =
      if m = n then oneHot s t else 0 := by
    by_cases hm : m = n
    · subst m; simp [dispatch_selected, oneHot_nonneg]
    · simp [hm, dispatch_other n m hm _ (oneHot_le_one s)]
  simp [hh, oneHot]

/-- A complete token interface; fixedCoordinates fields are explicit and never updated. -/
structure Token (F : Type w) where
  node : N -> Real
  fixedCoordinates : F -> Real
  payload : S -> Real
  scratch : S -> Real

def attentionResidual {F : Type w} (t : Token (N := N) (S := S) F) (w : S -> Real) :
    Token (N := N) (S := S) F :=
  {t with scratch := fun s => t.scratch s + w s}

/-- The updates are literally negative/positive output weights on ReLU units. -/
def feedforwardResidual {F : Type w} (active : N -> Bool) (f : N -> S -> S)
    (t : Token (N := N) (S := S) F) : Token (N := N) (S := S) F where
  node := fun n => t.node n + 0
  fixedCoordinates := fun z => t.fixedCoordinates z + 0
  payload := fun o => t.payload o +
    ((∑ n, ∑ s, oneHot (f n s) o * (if active n then 1 else 0) *
      dispatch t.node t.scratch n s) -
     (∑ n, (if active n then 1 else 0) * dispatch t.node t.payload n o))
  scratch := fun s => t.scratch s - relu (t.scratch s)

theorem shared_block_invariant {F : Type w} (active : N -> Bool) (f : N -> S -> S)
    (n : N) (old selected : S) (p : F -> Real) :
    feedforwardResidual active f
      (attentionResidual (Token.mk (oneHot n) p (oneHot old) (fun _ => 0)) (oneHot selected)) =
    Token.mk (oneHot n) p
      (oneHot (if active n then f n selected else old)) (fun _ => 0) := by
  have hh (m : N) (t s : S) :
      dispatch (oneHot n) (oneHot t) m s =
      if m = n then oneHot t s else 0 := by
    by_cases hm : m = n
    · subst m; simp [dispatch_selected, oneHot_nonneg]
    · simp [hm, dispatch_other n m hm _ (oneHot_le_one t)]
  have hh2 : ∀ (m : N) (s : S),
      dispatch (oneHot n) (fun s' => if s' = selected then (1 : Real) else 0) m s =
      if m = n then oneHot selected s else 0 := fun m s => hh m selected s
  have hscratch : ∀ x : S, oneHot selected x - max 0 (oneHot selected x) = 0 := by
    intro x
    simp only [oneHot]
    split_ifs <;> simp
  have hsum : ∀ o : S,
      (∑ x, oneHot (f n x) o * oneHot selected x) = oneHot (f n selected) o := by
    intro o
    rw [Finset.sum_eq_single selected]
    · simp [oneHot]
    · intro b _ hb; simp [oneHot, hb]
    · simp
  cases hn : active n <;>
    simp only [feedforwardResidual, attentionResidual, Token.mk.injEq] <;>
    refine ⟨?_, ?_, ?_⟩ <;>
    (try funext z) <;>
    simp [hh, hn, relu, hscratch, hsum, Finset.sum_ite_eq']
end Dispatch

end NeuralArtifacts.Neural

end -- noncomputable section

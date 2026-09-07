import NeuralArtifacts.ForestCompiler
import NeuralArtifacts.Inference

/-!
# 17. Shared soft correction, quantitative stability, and all-history preservation
-/
noncomputable section
open Classical Function
open scoped BigOperators
namespace NeuralArtifacts.Neural

section SharedSoft
variable {N S F I : Type*} [Fintype N] [DecidableEq N]
variable [Fintype S] [DecidableEq S] [Fintype I]

def correctedResidual (eta : Real) (active : N -> Bool) (f : N -> S -> S)
    (t : Token (N := N) (S := S) F) : Token (N := N) (S := S) F where
  node := fun n => t.node n + 0
  fixedCoordinates := fun z => t.fixedCoordinates z + 0
  payload := fun o => t.payload o +
    ((∑ n, ∑ s, (if active n then 1 else 0) * oneHot (f n s) o *
        gatedRound eta (t.node n) (t.scratch s)) -
     (∑ n, (if active n then 1 else 0) * dispatch t.node t.payload n o))
  scratch := fun s => t.scratch s - relu (t.scratch s)

theorem corrected_shared_block (eta : Real) (he0 : 0 ≤ eta) (he : eta < 1 / 2)
    (active : N -> Bool) (f : N -> S -> S) (n : N) (old target : S)
    (fixedCoordinates : F -> Real) (p : Probability I) (label : I -> S)
    (hmass : p.wrong label target ≤ eta) :
    correctedResidual eta active f
      (attentionResidual (Token.mk (oneHot n) fixedCoordinates (oneHot old) (fun _ => 0)) (p.coord label)) =
      Token.mk (oneHot n) fixedCoordinates
        (oneHot (if active n then f n target else old)) (fun _ => 0) := by
  have hround := (exact_symbol_iff he0 he p label target).mpr hmass
  have hg (m : N) (s : S) :
      gatedRound eta (oneHot n m) (p.coord label s) =
      if m = n then oneHot target s else 0 := by
    by_cases hm : m = n
    · subst m
      simp only [oneHot_self, gatedRound_one, if_true]
      exact congrFun hround s
    · simp [hm, gatedRound_zero he0 he (p.coord_le_one label s)]
  have hd (m : N) (s : S) :
      dispatch (oneHot n) (oneHot old) m s = if m = n then oneHot old s else 0 := by
    by_cases hm : m = n
    · subst m; simp [dispatch_selected, oneHot_nonneg]
    · simp [hm, dispatch_other n m hm _ (oneHot_le_one old)]
  have hsum : ∀ o : S, (∑ x, oneHot (f n x) o * oneHot target x) = oneHot (f n target) o :=
    fun o => sum_mul_oneHot (fun z => oneHot (f n z) o) target
  cases ha : active n <;>
    simp [correctedResidual, attentionResidual, hg, hd, ha, hsum,
      relu_of_nonneg (p.coord_nonneg label _)]
end SharedSoft

section Approximation
variable {I E : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [NormedSpace Real E]

omit [DecidableEq I] in
/-- The difference from a selected expert is a weighted sum of differences. -/
theorem mixture_sub (p : Probability I) (v : I -> E) (w : E) :
    (∑ i, p.weight i • v i) - w = ∑ i, p.weight i • (v i - w) := by
  simp only [smul_sub, Finset.sum_sub_distrib]
  rw [<- Finset.sum_smul, p.total, one_smul]

/-- A direct norm bound; the selected branch contributes exactly zero. -/
theorem mixture_error (p : Probability I) (v : I -> E) (winner : I)
    (B : Real) (hv : ∀ i, norm (v i) ≤ B) :
    norm ((∑ i, p.weight i • v i) - v winner) ≤
      2 * B * (∑ i, if i = winner then 0 else p.weight i) := by
  rw [mixture_sub]
  calc
    norm (∑ i, p.weight i • (v i - v winner)) ≤
        ∑ i, norm (p.weight i • (v i - v winner)) := norm_sum_le _ _
    _ = ∑ i, p.weight i * norm (v i - v winner) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (p.nonneg i)]
    _ ≤ ∑ i, 2 * B * (if i = winner then 0 else p.weight i) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases he : i = winner
      · subst i; simp
      · simp only [he, if_false]
        have hh : norm (v i - v winner) ≤ 2 * B := by
          have ht := norm_sub_le (v i) (v winner)
          linarith [hv i, hv winner]
        nlinarith [p.nonneg i]
    _ = 2 * B * (∑ i, if i = winner then 0 else p.weight i) := by
      rw [Finset.mul_sum]

/-- Discrete output margins turn a norm perturbation into exact label preservation. -/
theorem score_winner_preserved {J : Type*} [Fintype J]
    (s t : J -> Real) (winner : J) (delta err : Real)
    (hgap : ∀ j, j ≠ winner -> delta ≤ s winner - s j)
    (herror : ∀ j, |t j - s j| ≤ err) (hmargin : 2 * err < delta) :
    ∀ j, j ≠ winner -> t j < t winner := by
  intro j hj
  have hw := abs_le.mp (herror winner)
  have he := abs_le.mp (herror j)
  have hg := hgap j hj
  linarith
end Approximation

/-- Numerical iterates and the accumulated local-error recursion. -/
def iterate {E : Type*} (F : Nat -> E -> E) (x : E) : Nat -> E
  | 0 => x
  | n + 1 => F n (iterate F x n)

def errorBudget (L eps : Nat -> Real) : Nat -> Real
  | 0 => 0
  | n + 1 => L n * errorBudget L eps n + eps n

/-- Closed form in the paper, with empty downstream product equal to one. -/
def propagated (L eps : Nat -> Real) (n : Nat) : Real :=
  ∑ i ∈ Finset.range n, eps i * ∏ j ∈ Finset.Ico (i + 1) n, L j

theorem propagated_succ (L eps : Nat -> Real) (n : Nat) :
    propagated L eps (n + 1) = L n * propagated L eps n + eps n := by
  unfold propagated
  rw [Finset.sum_range_succ]
  have hterm (i : Nat) (hi : i ∈ Finset.range n) :
      (∏ j ∈ Finset.Ico (i + 1) (n + 1), L j) =
      (∏ j ∈ Finset.Ico (i + 1) n, L j) * L n := by
    apply Finset.prod_Ico_succ_top
    exact Nat.succ_le_of_lt (Finset.mem_range.mp hi)
  simp only [Finset.Ico_self, Finset.prod_empty, mul_one]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hterm i hi]
  ring

theorem errorBudget_closed (L eps : Nat -> Real) (n : Nat) :
    errorBudget L eps n = propagated L eps n := by
  induction n with
  | zero => simp [errorBudget, propagated]
  | succ n ih => rw [errorBudget, propagated_succ, ih]

/-- Region assumptions are explicit and apply to both compared trajectories. -/
theorem composed_error {E : Type*} [NormedAddCommGroup E]
    (soft hard : Nat -> E -> E) (x : E) (region : Nat -> Set E)
    (L eps : Nat -> Real) (hL : ∀ n, 0 ≤ L n)
    (hsoft : ∀ n, iterate soft x n ∈ region n)
    (hhard : ∀ n, iterate hard x n ∈ region n)
    (hlip : ∀ n, ∀ a ∈ region n, ∀ b ∈ region n,
      norm (soft n a - soft n b) ≤ L n * norm (a - b))
    (hlocal : ∀ n, ∀ a ∈ region n, norm (soft n a - hard n a) ≤ eps n) :
    ∀ n, norm (iterate soft x n - iterate hard x n) ≤ propagated L eps n := by
  have aux : ∀ n, norm (iterate soft x n - iterate hard x n) ≤ errorBudget L eps n := by
    intro n
    induction n with
    | zero => simp [iterate, errorBudget]
    | succ n ih =>
      have ht : norm (soft n (iterate soft x n) - hard n (iterate hard x n)) ≤
          norm (soft n (iterate soft x n) - soft n (iterate hard x n)) +
          norm (soft n (iterate hard x n) - hard n (iterate hard x n)) := by
        have hh := norm_add_le (soft n (iterate soft x n) - soft n (iterate hard x n))
          (soft n (iterate hard x n) - hard n (iterate hard x n))
        convert hh using 1; congr 1; abel
      have hl := hlip n _ (hsoft n) _ (hhard n)
      have he := hlocal n _ (hhard n)
      have hm := mul_le_mul_of_nonneg_left ih (hL n)
      simp only [iterate, errorBudget]
      linarith
  intro n
  rw [<- errorBudget_closed]
  exact aux n

/-- Approximate fitting version spaces have the two-sided loss sandwich. -/
theorem loss_version_sandwich {C : Type*} (soft hard : C -> Real) (eta eps : Real)
    (h : ∀ c, |soft c - hard c| ≤ eta) :
    {c | soft c ≤ eps - eta} ⊆ {c | hard c ≤ eps} ∧
    {c | hard c ≤ eps} ⊆ {c | soft c ≤ eps + eta} := by
  constructor <;> intro c hc <;> have hh := abs_le.mp (h c) <;>
    simp only [Set.mem_setOf_eq] at * <;> linarith

/-- Exact symbol transitions imply equality at every horizon, not just on a
fixed validation sample. -/
theorem symbolic_machine_run {Q P : Type*} [DecidableEq Q]
    (initial : Q) (step : Q -> P -> Q)
    (neuralStep : (Q -> Real) -> P -> (Q -> Real))
    (hstep : ∀ q p, neuralStep (oneHot q) p = oneHot (step q p)) :
    ∀ s : List P,
      s.foldl neuralStep (oneHot initial) = oneHot (s.foldl step initial) := by
  have aux : ∀ (s : List P) (q : Q),
      s.foldl neuralStep (oneHot q) = oneHot (s.foldl step q) := by
    intro s
    induction s with
    | nil => intro q; rfl
    | cons p s ih => intro q; simp only [List.foldl_cons, hstep]; exact ih _
  intro s
  exact aux s initial

end NeuralArtifacts.Neural

end -- noncomputable section

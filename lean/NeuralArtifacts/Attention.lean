import NeuralArtifacts.ReLU
import NeuralArtifacts.CoupledWidth

/-!
# 13. Deterministic hard attention and literal query/key projections

The tie rule is the least index among maximizing scores. The recursive
implementation below avoids any assumed argmax oracle.
-/
noncomputable section
open Classical Function
open scoped BigOperators
namespace NeuralArtifacts.Neural

/-- Exact least-index argmax, defined by a finite comparison recursion. -/
def argmax : {n : Nat} -> (Fin (n + 1) -> Real) -> Fin (n + 1)
  | 0, _ => 0
  | n + 1, s =>
    let t := argmax (fun i : Fin (n + 1) => s i.succ)
    if s 0 < s t.succ then t.succ else 0

theorem argmax_max {n : Nat} (s : Fin (n + 1) -> Real) :
    ∀ i, s i ≤ s (argmax s) := by
  induction n with
  | zero => intro i; have : i = 0 := Fin.fin_one_eq_zero i; subst i; exact le_rfl
  | succ n ih =>
    intro i
    let t := argmax (fun j : Fin (n + 1) => s j.succ)
    have ht (j : Fin (n + 1)) : s j.succ ≤ s t.succ :=
      ih (fun j : Fin (n + 1) => s j.succ) j
    by_cases h : s 0 < s t.succ
    · rw [argmax, if_pos h]
      refine Fin.cases h.le (fun j => ht j) i
    · rw [argmax, if_neg h]
      refine Fin.cases le_rfl (fun j => (ht j).trans (le_of_not_gt h)) i

theorem argmax_earliest {n : Nat} (s : Fin (n + 1) -> Real) :
    ∀ i, i < argmax s -> s i < s (argmax s) := by
  induction n with
  | zero => intro i h; exact False.elim (by simp [argmax] at h)
  | succ n ih =>
    let t := argmax (fun j : Fin (n + 1) => s j.succ)
    intro i hi
    by_cases h : s 0 < s t.succ
    · rw [argmax, if_pos h] at hi ⊢
      refine Fin.cases (fun _ => h) (fun j hj => ?_) i hi
      exact ih (fun j : Fin (n + 1) => s j.succ) j (Fin.succ_lt_succ_iff.mp hj)
    · rw [argmax, if_neg h] at hi
      exact False.elim (not_lt_of_ge (Fin.zero_le _) hi)

theorem argmax_characterization {n : Nat} (s : Fin (n + 1) -> Real)
    (i : Fin (n + 1)) :
    argmax s = i ↔
      (∀ j, s j ≤ s i) ∧ (∀ j, j < i -> s j < s i) := by
  constructor
  · rintro rfl
    exact ⟨argmax_max s, argmax_earliest s⟩
  · rintro ⟨hmax, hfirst⟩
    apply le_antisymm
    · by_contra h
      have hi : i < argmax s := lt_of_not_ge h
      exact (not_lt_of_ge (hmax _)) (argmax_earliest s i hi)
    · by_contra h
      have hi : argmax s < i := lt_of_not_ge h
      exact (not_lt_of_ge (argmax_max s i)) (hfirst _ hi)

def hardAttention {n : Nat} {V : Type*} (s : Fin (n + 1) -> Real)
    (v : Fin (n + 1) -> V) : V := v (argmax s)

/-- Equivalent query/key factorizations induce the same extracted routing. -/
theorem hardAttention_score_ext {n : Nat} {V : Type*}
    {s t : Fin (n + 1) -> Real} (h : ∀ i, s i = t i)
    (v : Fin (n + 1) -> V) : hardAttention s v = hardAttention t v := by
  congr 1
  exact funext h

def dot {F : Type*} [Fintype F] (x y : F -> Real) : Real := ∑ f, x f * y f

/-- Bias is a genuine homogeneous coordinate, represented by none. -/
def homogeneous {F : Type*} (x : F -> Real) : Option F -> Real :=
  fun z => match z with | none => 1 | some f => x f

def affineKey {F : Type*} (a : F -> Real) (b : Real) : Option F -> Real :=
  fun z => match z with | none => b | some f => a f

theorem dot_homogeneous {F : Type*} [Fintype F]
    (x a : F -> Real) (b : Real) :
    dot (homogeneous x) (affineKey a b) = dot x a + b := by
  simp [dot, homogeneous, affineKey, Fintype.sum_option, add_comm]

def projection {I O : Type*} [Fintype I] (W : O -> I -> Real)
    (x : I -> Real) : O -> Real := fun o => ∑ i, W o i * x i

def selectWeights {I O : Type*} [DecidableEq I] (index : O -> I) : O -> I -> Real :=
  fun o i => if i = index o then 1 else 0

theorem projection_select {I O : Type*} [Fintype I] [DecidableEq I]
    (index : O -> I) (x : I -> Real) : projection (selectWeights index) x = x ∘ index := by
  funext o
  simp [projection, selectWeights]

/-- A coordinate injection writes a vector into scratch, and zero elsewhere. -/
def writeWeights {I O : Type*} [DecidableEq O] (index : I -> O) : O -> I -> Real :=
  fun o i => if o = index i then 1 else 0

theorem projection_write_inside {I O : Type*} [Fintype I] [DecidableEq O]
    (index : I -> O) (hi : Injective index) (x : I -> Real) (j : I) :
    projection (writeWeights index) x (index j) = x j := by
  have h (i : I) : index j = index i ↔ i = j := by
    constructor
    · intro h; exact (hi h).symm
    · rintro rfl; rfl
  simp [projection, writeWeights, h]

theorem projection_write_outside {I O : Type*} [Fintype I] [DecidableEq O]
    (index : I -> O) (x : I -> Real) (o : O) (ho : ∀ i, o ≠ index i) :
    projection (writeWeights index) x o = 0 := by
  simp [projection, writeWeights, ho]

/-- A singleton mask eliminates every temperature dependence. -/
theorem singleton_hard {V : Type*} (s : Fin 1 -> Real) (v : Fin 1 -> V) :
    hardAttention s v = v 0 := rfl

/-- The coupled minimum comparator works in any finite encoding.
Equal ranks may tie, but their values are equal. -/
theorem coupled_minimum {n : Nat} {V : Type*} (code : Fin (n + 1) -> V)
    (r s : Fin (n + 1)) :
    hardAttention (fun i : Fin 2 => if i = 0 then -(r.val : Real) else -(s.val : Real))
      (fun i : Fin 2 => if i = 0 then code r else code s) = code (min r s) := by
  by_cases h : r ≤ s
  · have hm : argmax (fun i : Fin 2 => if i = 0 then -(r.val : Real) else -(s.val : Real)) = 0 := by
      apply (argmax_characterization _ _).mpr
      constructor
      · intro i
        fin_cases i <;> simp
        exact h
      · intro i hi; exact False.elim (not_lt_of_ge (Fin.zero_le _) hi)
    simp [hardAttention, hm, min_eq_left h]
  · have hsr : s < r := lt_of_not_ge h
    have hm : argmax (fun i : Fin 2 => if i = 0 then -(r.val : Real) else -(s.val : Real)) = 1 := by
      apply (argmax_characterization _ _).mpr
      constructor
      · intro i
        fin_cases i <;> simp
        exact hsr.le
      · intro i hi
        have hzero : ∀ j : Fin 2, j < 1 -> j = 0 := by decide
        have : i = 0 := hzero i hi
        subst i
        simp
        exact hsr
    simp [hardAttention, hm, min_eq_right hsr.le]

end NeuralArtifacts.Neural

end -- noncomputable section

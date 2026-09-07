import NeuralArtifacts.Inference
import NeuralArtifacts.FiniteOrder

/-!
# 28. Mind changes along a history

The states reached along a history descend in the inference state space, so the
reported answer takes a new value at most `height` minus one times. The bound is
exact. On the Boolean store of `k` candidates read by its least surviving
candidate, eliminating candidates from the bottom changes the answer `k` times,
and the inference state of that readout has height `k + 1`.
-/

noncomputable section
open Classical Function
open scoped BigOperators
namespace NeuralArtifacts
namespace MindChange
universe u v w

section Descent
variable {A : Type u} [PartialOrder A] [Fintype A]

/-- Positions below `n` at which a sequence takes a strictly smaller value. -/
def descentCount (f : Nat -> A) (n : Nat) : Nat :=
  ((Finset.range n).filter (fun i => f (i + 1) < f i)).card

omit [Fintype A] in
@[simp] theorem descentCount_zero (f : Nat -> A) : descentCount f 0 = 0 := by
  simp [descentCount]

omit [Fintype A] in
theorem descentCount_succ_of_lt (f : Nat -> A) {n : Nat} (h : f (n + 1) < f n) :
    descentCount f (n + 1) = descentCount f n + 1 := by
  have hn : n ∉ (Finset.range n).filter (fun i => f (i + 1) < f i) := by simp
  unfold descentCount
  rw [Finset.range_add_one, Finset.filter_insert, if_pos h,
    Finset.card_insert_of_notMem hn]

omit [Fintype A] in
theorem descentCount_succ_of_not_lt (f : Nat -> A) {n : Nat} (h : ¬ f (n + 1) < f n) :
    descentCount f (n + 1) = descentCount f n := by
  unfold descentCount
  rw [Finset.range_add_one, Finset.filter_insert, if_neg h]

/-- Each strict descent spends one unit of the rank of the starting point. -/
theorem descentCount_add_excessRank (f : Nat -> A)
    (hf : ∀ i, f (i + 1) ≤ f i) (n : Nat) :
    descentCount f n + FiniteOrder.excessRank (f n)
      ≤ FiniteOrder.excessRank (f 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases h : f (n + 1) < f n
    · have hr := FiniteOrder.excessRank_strict h
      rw [descentCount_succ_of_lt f h]
      omega
    · have he : f (n + 1) = f n := by
        by_contra hne
        exact h (lt_of_le_of_ne (hf n) hne)
      rw [descentCount_succ_of_not_lt f h, he]
      exact ih

omit [Fintype A] in
/-- A sequence that descends at every position below `n` has `n` descents. -/
theorem descentCount_eq (f : Nat -> A) (n : Nat) (h : ∀ i, i < n -> f (i + 1) < f i) :
    descentCount f n = n := by
  unfold descentCount
  rw [Finset.filter_true_of_mem (fun i hi => h i (Finset.mem_range.mp hi)),
    Finset.card_range]

/-- A descending sequence takes at most `height` minus one new values. -/
theorem descentCount_le_height (f : Nat -> A)
    (hf : ∀ i, f (i + 1) ≤ f i) (n : Nat) :
    descentCount f n ≤ FiniteOrder.height A - 1 := by
  have h := descentCount_add_excessRank f hf n
  have h0 := FiniteOrder.excessRank_le (f 0)
  omega
end Descent

section Readout
variable {R : Type u} [SemilatticeInf R] [OrderTop R]
variable {P : Type v} {Y : Type w}

/-- One more observation refines the evaluated state. -/
theorem eval_take_succ (g : P -> R) (s : List P) (i : Nat) :
    Inference.eval g (s.take (i + 1)) ≤ Inference.eval g (s.take i) := by
  induction s generalizing i with
  | nil => simp
  | cons p t ih =>
    cases i with
    | zero => simp
    | succ j =>
      simp only [List.take_succ_cons, Inference.eval_cons]
      exact inf_le_inf_left _ (ih j)

/-- The semantic state after the first `i` observations of `s`. -/
def semState (rho : R -> Y) (g : P -> R) (s : List P) (i : Nat) : Inference.State rho :=
  Inference.mk rho (Inference.eval g (s.take i))

theorem semState_antitone (rho : R -> Y) (g : P -> R) (s : List P) (i : Nat) :
    semState rho g s (i + 1) ≤ semState rho g s i :=
  (Inference.projection rho).monotone (eval_take_succ g s i)

/-- The answer reported after the first `i` observations of `s`. -/
def readoutAt (rho : R -> Y) (g : P -> R) (s : List P) (i : Nat) : Y :=
  rho (Inference.eval g (s.take i))

theorem readoutAt_eq_read (rho : R -> Y) (g : P -> R) (s : List P) (i : Nat) :
    readoutAt rho g s i = Inference.read rho (semState rho g s i) := rfl

/-- The number of prefixes of `s` at which the reported answer changes. -/
def readoutChanges (rho : R -> Y) (g : P -> R) (s : List P) : Nat :=
  ((Finset.range s.length).filter
    (fun i => readoutAt rho g s (i + 1) ≠ readoutAt rho g s i)).card

/-- The readout factors through the semantic state, so a change of answer is a
strict descent of that state. -/
theorem semState_lt_of_readoutAt_ne (rho : R -> Y) (g : P -> R) (s : List P) {i : Nat}
    (h : readoutAt rho g s (i + 1) ≠ readoutAt rho g s i) :
    semState rho g s (i + 1) < semState rho g s i := by
  refine lt_of_le_of_ne (semState_antitone rho g s i) ?_
  intro he
  exact h (by rw [readoutAt_eq_read, readoutAt_eq_read, he])

/-- A history on which every step changes the answer has as many changes as
observations. -/
theorem readoutChanges_eq_length (rho : R -> Y) (g : P -> R) (s : List P)
    (h : ∀ i, i < s.length -> readoutAt rho g s (i + 1) ≠ readoutAt rho g s i) :
    readoutChanges rho g s = s.length := by
  unfold readoutChanges
  rw [Finset.filter_true_of_mem (fun i hi => h i (Finset.mem_range.mp hi)),
    Finset.card_range]

/-- Mind-change bound: along any history the reported answer changes at most
`height` minus one times, for any readout and any observation grammar. -/
theorem readoutChanges_le_height [Fintype R] (rho : R -> Y) (g : P -> R) (s : List P) :
    readoutChanges rho g s ≤ FiniteOrder.height (Inference.State rho) - 1 := by
  have hsub : ((Finset.range s.length).filter
        (fun i => readoutAt rho g s (i + 1) ≠ readoutAt rho g s i)) ⊆
      ((Finset.range s.length).filter
        (fun i => semState rho g s (i + 1) < semState rho g s i)) := by
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hr, hne⟩
    exact Finset.mem_filter.mpr ⟨hr, semState_lt_of_readoutAt_ne rho g s hne⟩
  calc readoutChanges rho g s ≤ descentCount (semState rho g s) s.length :=
        Finset.card_le_card hsub
    _ ≤ FiniteOrder.height (Inference.State rho) - 1 :=
        descentCount_le_height _ (semState_antitone rho g s) _
end Readout

section Boolean

/-- First-consistent-model readout of a Boolean elimination store: the least
surviving candidate, and a value distinct from every candidate when none
survives. -/
def firstFit (k : Nat) (V : Finset (Fin k)) : WithTop (Fin k) := V.min

/-- The candidates numbered `i` and above. -/
def above (k i : Nat) : Finset (Fin k) := Finset.univ.filter (fun j : Fin k => i ≤ j.val)

/-- The observation that eliminates candidate number `i`. -/
def kill (k i : Nat) : Finset (Fin k) := Finset.univ.filter (fun j : Fin k => j.val ≠ i)

/-- Eliminate candidates from the bottom, in order. -/
def killHistory (k : Nat) : List (Finset (Fin k)) := (List.range k).map (kill k)

@[simp] theorem mem_above (k i : Nat) (j : Fin k) : j ∈ above k i ↔ i ≤ j.val := by
  simp [above]

@[simp] theorem mem_kill (k i : Nat) (j : Fin k) : j ∈ kill k i ↔ j.val ≠ i := by
  simp [kill]

@[simp] theorem killHistory_length (k : Nat) : (killHistory k).length = k := by
  simp [killHistory]

theorem above_zero (k : Nat) : above k 0 = ⊤ := by
  ext j; simp

theorem eval_kill_range (k i : Nat) :
    Inference.eval id ((List.range i).map (kill k)) = above k i := by
  induction i with
  | zero => simp [above_zero]
  | succ i ih =>
    have h1 : Inference.eval (id : Finset (Fin k) -> Finset (Fin k))
        (List.map (kill k) [i]) = kill k i := by simp
    rw [List.range_succ, List.map_append, Inference.eval_append, ih, h1]
    ext j
    simp only [Finset.inf_eq_inter, Finset.mem_inter, mem_above, mem_kill]
    omega

theorem eval_killHistory_take (k i : Nat) :
    Inference.eval id ((killHistory k).take i) = above k (min i k) := by
  rw [killHistory, <- List.map_take, List.take_range, eval_kill_range]

theorem firstFit_above_of_lt {k i : Nat} (h : i < k) :
    firstFit k (above k i) = ((⟨i, h⟩ : Fin k) : WithTop (Fin k)) := by
  apply le_antisymm
  · exact Finset.min_le (by simp)
  · refine Finset.le_min ?_
    intro b hb
    exact WithTop.coe_le_coe.mpr (Fin.le_def.mpr (by simpa using hb))

theorem firstFit_above_top (k : Nat) : firstFit k (above k k) = ⊤ := by
  rw [firstFit, Finset.min_eq_top, above, Finset.filter_eq_empty_iff]
  intro j _
  simp only [not_le]
  exact j.isLt

theorem readoutAt_killHistory (k i : Nat) :
    readoutAt (firstFit k) id (killHistory k) i = firstFit k (above k (min i k)) := by
  rw [readoutAt, eval_killHistory_take]

theorem readoutAt_killHistory_ne {k i : Nat} (h : i < k) :
    readoutAt (firstFit k) id (killHistory k) (i + 1) ≠
      readoutAt (firstFit k) id (killHistory k) i := by
  rw [readoutAt_killHistory, readoutAt_killHistory, min_eq_left h.le,
    firstFit_above_of_lt h]
  by_cases h2 : i + 1 < k
  · rw [min_eq_left h2.le, firstFit_above_of_lt h2]
    intro he
    have hv : i + 1 = i := by simpa using WithTop.coe_eq_coe.mp he
    omega
  · have hmin : min (i + 1) k = k := by omega
    rw [hmin, firstFit_above_top]
    exact WithTop.top_ne_coe

/-- Eliminating candidates from the bottom changes the answer at every step. -/
theorem boolean_firstFit_changes (k : Nat) :
    readoutChanges (firstFit k) id (killHistory k) = k := by
  rw [readoutChanges_eq_length _ _ _
    (fun i hi => readoutAt_killHistory_ne (by simpa using hi)), killHistory_length]

/-- Chains of survivor sets are graded by cardinality. -/
theorem height_store_le (k : Nat) : FiniteOrder.height (Finset (Fin k)) ≤ k + 1 := by
  apply Finset.sup_le
  intro s hs
  have hc := (FiniteOrder.mem_chains s).mp hs
  let f : {x // x ∈ s} -> Fin (k + 1) :=
    fun x => ⟨x.val.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ x.val)⟩
  have hf : Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hcard : x.val.card = y.val.card := congrArg Fin.val hxy
    rcases hc x.val x.property y.val y.property with hle | hle
    · exact Finset.eq_of_subset_of_card_le (Finset.le_iff_subset.mp hle)
        (le_of_eq hcard.symm)
    · exact (Finset.eq_of_subset_of_card_le (Finset.le_iff_subset.mp hle)
        (le_of_eq hcard)).symm
  simpa using Fintype.card_le_of_injective f hf

theorem height_store_ge (k : Nat) : k + 1 ≤ FiniteOrder.height (Finset (Fin k)) := by
  have hinj : Injective (fun i : Fin (k + 1) => above k i.val) := by
    intro a b hab
    apply Fin.ext
    by_contra hne
    have key : ∀ c d : Fin (k + 1), c.val < d.val ->
        above k c.val ≠ above k d.val := by
      intro c d hcd hcontra
      have hck : c.val < k := by have := d.isLt; omega
      have h1 : (⟨c.val, hck⟩ : Fin k) ∈ above k c.val := by simp
      rw [hcontra] at h1
      have h2 : d.val ≤ c.val := by simpa using h1
      omega
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact key a b hlt hab
    · exact key b a hgt hab.symm
  have hchain : FiniteOrder.Chain
      (Finset.univ.image (fun i : Fin (k + 1) => above k i.val)) := by
    intro x hx y hy
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hy
    rcases le_total a.val b.val with hab | hba
    · refine Or.inr (Finset.le_iff_subset.mpr ?_)
      intro j hj
      simp only [mem_above] at hj ⊢
      omega
    · refine Or.inl (Finset.le_iff_subset.mpr ?_)
      intro j hj
      simp only [mem_above] at hj ⊢
      omega
  have hcard := FiniteOrder.card_le_height hchain
  rwa [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hcard

theorem height_store (k : Nat) : FiniteOrder.height (Finset (Fin k)) = k + 1 :=
  le_antisymm (height_store_le k) (height_store_ge k)

theorem firstFit_inf_singleton (k : Nat) (V : Finset (Fin k)) (i : Fin k) :
    firstFit k (V ⊓ {i}) = if i ∈ V then (i : WithTop (Fin k)) else ⊤ := by
  by_cases h : i ∈ V
  · rw [if_pos h, firstFit, Finset.inf_eq_inter, Finset.inter_singleton_of_mem h,
      Finset.min_singleton]
  · rw [if_neg h, firstFit, Finset.inf_eq_inter, Finset.inter_singleton_of_notMem h,
      Finset.min_empty]

/-- Testing one candidate at a time, the least-survivor readout separates every
pair of survivor sets. -/
theorem firstFit_injective_mk (k : Nat) : Injective (Inference.mk (firstFit k)) := by
  intro V W h
  have heq : Inference.Eqv (firstFit k) V W := (Inference.mk_eq_mk _ V W).mp h
  ext i
  have hi := heq {i}
  rw [firstFit_inf_singleton, firstFit_inf_singleton] at hi
  by_cases hV : i ∈ V
  · by_cases hW : i ∈ W
    · exact iff_of_true hV hW
    · rw [if_pos hV, if_neg hW] at hi
      exact absurd hi WithTop.coe_ne_top
  · by_cases hW : i ∈ W
    · rw [if_neg hV, if_pos hW] at hi
      exact absurd hi.symm WithTop.coe_ne_top
    · exact iff_of_false hV hW

theorem height_state_firstFit (k : Nat) :
    FiniteOrder.height (Inference.State (firstFit k)) = k + 1 := by
  have hsurj : Surjective (Inference.projection (firstFit k)).toFun := by
    intro q
    refine Quotient.inductionOn q ?_
    intro V
    exact ⟨V, rfl⟩
  have h1 : FiniteOrder.height (Inference.State (firstFit k))
      ≤ FiniteOrder.height (Finset (Fin k)) :=
    FiniteOrder.height_le_of_surjective_meetHom (Inference.projection (firstFit k)) hsurj
  have h2 : FiniteOrder.height (Finset (Fin k))
      ≤ FiniteOrder.height (Inference.State (firstFit k)) :=
    FiniteOrder.height_le_of_injective_monotone (Inference.mk (firstFit k))
      (firstFit_injective_mk k) (Inference.projection (firstFit k)).monotone
  have h3 := height_store k
  omega

/-- The Boolean store attains the mind-change bound: the kill-from-bottom
history changes the answer `k` times, and its inference state has height
`k + 1`. -/
theorem boolean_firstFit_tight (k : Nat) :
    readoutChanges (firstFit k) id (killHistory k) = k ∧
      FiniteOrder.height (Inference.State (firstFit k)) = k + 1 :=
  ⟨boolean_firstFit_changes k, height_state_firstFit k⟩

end Boolean
end MindChange
end NeuralArtifacts

end -- noncomputable section

import NeuralArtifacts.Inference

/-!
# 9. Exact extraction, partition refinement, and finite abstractions

Paper: Theorem 6 and Appendix B. The machine being minimized is restricted
to reachable states. A finite state codebook is an operational interface;
its exact transition function and readout are the functions queried below.
-/

noncomputable section
open Classical Function
open scoped BigOperators
namespace NeuralArtifacts
namespace Extraction
variable {Q P Y : Type*} (A : Moore Q P Y)

/-- Output equivalence for continuations of bounded length. -/
def approx : Nat -> Q -> Q -> Prop
  | 0, q, r => A.out q = A.out r
  | n + 1, q, r => A.out q = A.out r ∧ ∀ p, approx n (A.step q p) (A.step r p)

theorem approx_equivalence (n : Nat) : Equivalence (approx A n) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro q; rfl
    · intro q r h; exact h.symm
    · intro q r s h1 h2; exact h1.trans h2
  | succ n ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro q; exact ⟨rfl, fun p => ih.refl _⟩
    · intro q r h; exact ⟨h.1.symm, fun p => ih.symm (h.2 p)⟩
    · intro q r s h1 h2; exact ⟨h1.1.trans h2.1, fun p => ih.trans (h1.2 p) (h2.2 p)⟩

def approxSetoid (n : Nat) : Setoid Q := ⟨approx A n, approx_equivalence A n⟩

theorem approx_out {n : Nat} {q r : Q} (h : approx A n q r) : A.out q = A.out r := by
  cases n with
  | zero => exact h
  | succ n => exact h.1

theorem approx_weaken (n : Nat) {q r : Q} : approx A (n + 1) q r -> approx A n q r := by
  induction n generalizing q r with
  | zero => exact fun h => h.1
  | succ n ih =>
    intro h
    exact ⟨h.1, fun p => ih (h.2 p)⟩

/-- The refinement definition is exactly bounded-continuation equivalence. -/
theorem approx_iff_words (n : Nat) (q r : Q) :
    approx A n q r ↔
      ∀ s : List P, s.length ≤ n -> A.out (A.runFrom q s) = A.out (A.runFrom r s) := by
  induction n generalizing q r with
  | zero =>
    constructor
    · intro h s hs
      have he : s = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hs)
      subst he
      exact h
    · intro h; exact h [] (by simp)
  | succ n ih =>
    constructor
    · rintro ⟨hout, hstep⟩ s hs
      cases s with
      | nil => exact hout
      | cons p s =>
        exact (ih (A.step q p) (A.step r p)).mp (hstep p) s (by simpa using hs)
    · intro h
      refine ⟨h [] (by simp), ?_⟩
      intro p
      apply (ih (A.step q p) (A.step r p)).mpr
      intro s hs
      exact h (p :: s) (by simpa using Nat.succ_le_succ hs)

def Stable (n : Nat) : Prop := ∀ q r, approx A (n + 1) q r ↔ approx A n q r

/-- Stabilization gives an actual bisimulation, hence all-horizon equivalence. -/
theorem stable_iff_obsEq (n : Nat) (hs : Stable A n) (q r : Q) :
    approx A n q r ↔ A.ObsEq q r := by
  constructor
  · intro h s
    induction s generalizing q r with
    | nil => exact approx_out A h
    | cons p s ih =>
      have ht := ((hs q r).mpr h).2 p
      exact ih (A.step q p) (A.step r p) ht
  · intro h
    exact (approx_iff_words A n q r).mpr (fun s _ => h s)

instance [Fintype Q] (n : Nat) : Fintype (Quotient (approxSetoid A n)) :=
  Fintype.ofFinite _

def blockCount [Fintype Q] (n : Nat) : Nat := Fintype.card (Quotient (approxSetoid A n))

def forgetLast (n : Nat) :
    Quotient (approxSetoid A (n + 1)) -> Quotient (approxSetoid A n) :=
  Quotient.lift (fun q => Quotient.mk (approxSetoid A n) q)
    (by intro q r h; exact Quotient.sound (approx_weaken A n h))

theorem forgetLast_surjective (n : Nat) : Surjective (forgetLast A n) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro r
  exact ⟨Quotient.mk (approxSetoid A (n + 1)) r, rfl⟩

theorem blockCount_le [Fintype Q] (n : Nat) : blockCount A n ≤ Fintype.card Q := by
  apply Fintype.card_le_of_surjective (Quotient.mk (approxSetoid A n))
  intro q; refine Quotient.inductionOn q ?_; intro r; exact ⟨r, rfl⟩

theorem blockCount_pos [Fintype Q] (n : Nat) : 1 ≤ blockCount A n := by
  letI : Nonempty (Quotient (approxSetoid A n)) :=
    ⟨Quotient.mk (approxSetoid A n) A.initial⟩
  exact Fintype.card_pos_iff.mpr inferInstance

theorem stable_of_equal_blockCount [Fintype Q] (n : Nat)
    (hc : blockCount A (n + 1) = blockCount A n) : Stable A n := by
  have hi : Injective (forgetLast A n) := injective_of_surjective_card_eq
    (forgetLast A n) (forgetLast_surjective A n) hc
  intro q r
  constructor
  · exact approx_weaken A n
  · intro h
    refine Quotient.exact (s := approxSetoid A (n + 1)) (hi ?_)
    exact Quotient.sound h

theorem strict_blockCount_of_not_stable [Fintype Q] (n : Nat) (hn : ¬ Stable A n) :
    blockCount A n < blockCount A (n + 1) := by
  have hle : blockCount A n ≤ blockCount A (n + 1) :=
    Fintype.card_le_of_surjective (forgetLast A n) (forgetLast_surjective A n)
  have hne : blockCount A n ≠ blockCount A (n + 1) := by
    intro h; exact hn (stable_of_equal_blockCount A n h.symm)
  omega

/-- At most `N-1` strict refinements are possible on `N` reachable states. -/
theorem stable_before_card [Fintype Q] : ∃ n, n < Fintype.card Q ∧ Stable A n := by
  by_contra! h
  have hinc : ∀ k, k < Fintype.card Q -> blockCount A k < blockCount A (k + 1) :=
    fun k hk => strict_blockCount_of_not_stable A k (h k hk)
  have hcount : ∀ k, k ≤ Fintype.card Q -> k + 1 ≤ blockCount A k := by
    intro k
    induction k with
    | zero => intro hk; exact blockCount_pos A 0
    | succ k ih =>
      intro hk
      have hk' : k < Fintype.card Q := by omega
      have hprev := ih (by omega)
      have hnext := hinc k hk'
      omega
  have hbad := hcount (Fintype.card Q) le_rfl
  have hbound := blockCount_le A (Fintype.card Q)
  omega

/-- Distinct final blocks carry a finite distinguishing-word certificate. -/
theorem separating_word_of_not_approx {n : Nat} {q r : Q}
    (h : ¬ approx A n q r) :
    ∃ s : List P, s.length ≤ n ∧ A.out (A.runFrom q s) ≠ A.out (A.runFrom r s) := by
  have hn : ¬ (∀ s : List P, s.length ≤ n ->
      A.out (A.runFrom q s) = A.out (A.runFrom r s)) := by
    simpa [<- approx_iff_words A n q r] using h
  push Not at hn
  exact hn

def obsSetoid : Setoid Q := ⟨A.ObsEq, A.obsEq_equivalence⟩
def MinState := Quotient (obsSetoid A)
instance [Finite Q] : Finite (MinState A) :=
  inferInstanceAs (Finite (Quotient (obsSetoid A)))

noncomputable instance [Fintype Q] : Fintype (MinState A) := Fintype.ofFinite _

def minStep (q : MinState A) (p : P) : MinState A :=
  Quotient.liftOn q (fun r => Quotient.mk (obsSetoid A) (A.step r p))
    (by intro r s h; exact Quotient.sound (A.obsEq_step h p))

def minOut : MinState A -> Y :=
  Quotient.lift A.out (by intro r s h; exact h [])

def minimalMachine : Moore (MinState A) P Y where
  initial := Quotient.mk (obsSetoid A) A.initial
  step := minStep A
  out := minOut A

theorem minimal_run (s : List P) :
    (minimalMachine A).run s = Quotient.mk (obsSetoid A) (A.run s) := by
  symm
  exact Moore.simulation_run A (minimalMachine A)
    (Quotient.mk (obsSetoid A)) rfl (fun _ _ => rfl) s

theorem minimal_outputs (s : List P) :
    (minimalMachine A).out ((minimalMachine A).run s) = A.out (A.run s) := by
  rw [minimal_run]
  rfl

/-- Restriction to the reachable interface precedes minimization. -/
def reachableMachine : Moore A.Reach P Y where
  initial := A.rInitial
  step := A.rStep
  out q := A.out q.val

theorem reachable_run_val (q : A.Reach) (s : List P) :
    ((reachableMachine A).runFrom q s).val = A.runFrom q.val s := by
  induction s generalizing q with
  | nil => rfl
  | cons p s ih => exact ih (A.rStep q p)

@[simp] theorem reachableMachine_out (q : A.Reach) :
    (reachableMachine A).out q = A.out q.val := rfl

theorem reachable_obsEq (q r : A.Reach) :
    (reachableMachine A).ObsEq q r ↔ A.ObsEq q.val r.val := by
  simp only [Moore.ObsEq, reachableMachine_out, reachable_run_val]

section Canonical
variable {R : Type*} [SemilatticeInf R] [OrderTop R]
variable (g : P -> R) (rho : R -> Y)
variable (hg : Inference.Generated g) (hc : Inference.Correct A g rho)

include hg hc in
/-- Equality of extracted semantics is exactly observational equivalence. -/
theorem delta_eq_iff_obsEq (q r : A.Reach) :
    Inference.delta A g rho q = Inference.delta A g rho r ↔ A.ObsEq q.val r.val := by
  obtain ⟨s, hs⟩ := q.property
  obtain ⟨t, ht⟩ := r.property
  have hq : q = A.rRun s := Subtype.ext hs.symm
  have hr : r = A.rRun t := Subtype.ext ht.symm
  rw [hq, hr, Inference.delta_rRun A g rho hg hc,
    Inference.delta_rRun A g rho hg hc, Inference.mk_eq_mk]
  constructor
  · intro he u
    have h := he (Inference.eval g u)
    rw [<- Inference.eval_append, <- Inference.eval_append, <- hc, <- hc] at h
    have hgoal : A.out (A.runFrom (A.run s) u) = A.out (A.runFrom (A.run t) u) := by
      simpa using h
    exact hgoal
  · intro he h
    obtain ⟨u, hu⟩ := hg h
    have hh := he u
    change A.out (A.runFrom (A.run s) u) = A.out (A.runFrom (A.run t) u) at hh
    rw [<- A.run_append, <- A.run_append, hc, hc,
      Inference.eval_append, Inference.eval_append, hu] at hh
    exact hh

include hg hc in
/-- The extracted minimal machine and the read-specific inference quotient
have the same states, up to a canonical equivalence. -/
def minimalCanonicalEquiv : MinState (reachableMachine A) ≃ Inference.State rho := by
  let f : MinState (reachableMachine A) -> Inference.State rho :=
    Quotient.lift (Inference.delta A g rho) (by
      intro q r h
      exact (delta_eq_iff_obsEq A g rho hg hc q r).mpr
        ((reachable_obsEq A q r).mp h))
  have hi : Injective f := by
    intro q r
    refine Quotient.inductionOn q ?_; intro x
    refine Quotient.inductionOn r ?_; intro y h
    apply Quotient.sound
    exact (reachable_obsEq A x y).mpr
      ((delta_eq_iff_obsEq A g rho hg hc x y).mp h)
  have hs : Surjective f := by
    intro q
    obtain ⟨r, hr⟩ := Inference.delta_surjective A g rho hg hc q
    exact ⟨Quotient.mk (obsSetoid (reachableMachine A)) r, hr⟩
  exact Equiv.ofBijective f ⟨hi, hs⟩
end Canonical

section Reachability
variable [Fintype Q] [Fintype P]

/-- The breadth-first sequence of discovered states, with memoized transitions. -/
def discovered : Nat -> Finset Q
  | 0 => {A.initial}
  | n + 1 => discovered n ∪
      (discovered n).biUnion (fun q => Finset.univ.image (A.step q))

omit [Fintype Q] in
theorem discovered_mono_step (n : Nat) : discovered A n ⊆ discovered A (n + 1) :=
  Finset.subset_union_left

omit [Fintype Q] in
theorem discovered_successor {n : Nat} {q : Q} (hq : q ∈ discovered A n) (p : P) :
    A.step q p ∈ discovered A (n + 1) := by
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨q, hq, Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩⟩

omit [Fintype Q] in
theorem discovered_reachable (n : Nat) {q : Q} (hq : q ∈ discovered A n) :
    ∃ s, A.run s = q := by
  induction n generalizing q with
  | zero =>
    have h : q = A.initial := by simpa [discovered] using hq
    exact ⟨[], h.symm⟩
  | succ n ih =>
    rcases Finset.mem_union.mp hq with hq | hq
    · exact ih hq
    · obtain ⟨r, hr, hp⟩ := Finset.mem_biUnion.mp hq
      obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hp
      obtain ⟨s, hs⟩ := ih hr
      exact ⟨s ++ [p], by simp [hs, he]⟩

omit [Fintype Q] in
theorem discovered_nonempty (n : Nat) : (discovered A n).Nonempty := by
  induction n with
  | zero => simp [discovered]
  | succ n ih => exact ih.mono (discovered_mono_step A n)

/-- Reachability exploration also stabilizes before the carrier cardinality. -/
theorem discovered_stabilizes : ∃ n, n < Fintype.card Q ∧
    discovered A (n + 1) = discovered A n := by
  by_contra! h
  have hinc : ∀ n, n < Fintype.card Q ->
      (discovered A n).card < (discovered A (n + 1)).card := by
    intro n hn
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨discovered_mono_step A n, ?_⟩
    exact fun he => h n hn he.symm
  have hcount : ∀ n, n ≤ Fintype.card Q -> n + 1 ≤ (discovered A n).card := by
    intro n
    induction n with
    | zero => simp [discovered]
    | succ n ih =>
      intro hn
      have hp := ih (by omega)
      have hs := hinc n (by omega)
      omega
  have h1 := hcount (Fintype.card Q) le_rfl
  have h2 := Finset.card_le_univ (discovered A (Fintype.card Q))
  omega

omit [Fintype Q] in
theorem discovered_complete {n : Nat}
    (hn : discovered A (n + 1) = discovered A n) (s : List P) :
    A.run s ∈ discovered A n := by
  have hinit : A.initial ∈ discovered A n := by
    clear hn
    induction n with
    | zero => simp [discovered]
    | succ n ih => exact discovered_mono_step A n ih
  have closed : ∀ q ∈ discovered A n, ∀ p, A.step q p ∈ discovered A n := by
    intro q hq p
    rw [<- hn]
    exact discovered_successor A hq p
  have hrun : ∀ q ∈ discovered A n, ∀ t, A.runFrom q t ∈ discovered A n := by
    intro q hq t
    induction t generalizing q with
    | nil => exact hq
    | cons p t ih => exact ih (A.step q p) (closed q hq p)
  exact hrun A.initial hinit s

/-- Number of distinct transition cells queried by memoized exploration. -/
theorem transition_evaluation_budget (n : Nat) :
    ((discovered A n).product (Finset.univ : Finset P)).card ≤
      Fintype.card Q * Fintype.card P := by
  have hp : ((discovered A n).product (Finset.univ : Finset P)).card
      = (discovered A n).card * (Finset.univ : Finset P).card :=
    Finset.card_product _ _
  rw [hp, Finset.card_univ]
  exact Nat.mul_le_mul_right _ (Finset.card_le_univ (discovered A n))
end Reachability

end Extraction

namespace FiniteAbstraction
variable {Z Q P Y : Type*}

/-- Region labels certify a finite abstraction of the complete persistent state. -/
structure Certificate (concrete : Moore Z P Y) (finite : Moore Q P Y) where
  label : Z -> Q
  initial : label concrete.initial = finite.initial
  transition : ∀ z p, label (concrete.step z p) = finite.step (label z) p
  readout : ∀ z, concrete.out z = finite.out (label z)

theorem all_histories (concrete : Moore Z P Y) (finite : Moore Q P Y)
    (c : Certificate concrete finite) (s : List P) :
    concrete.out (concrete.run s) = finite.out (finite.run s) :=
  Moore.simulation_outputs concrete finite c.label c.initial c.transition c.readout s

/-- A cover by disjoint invariant regions constructs, rather than assumes,
the label function used by the simulation theorem. -/
def ofRegions (concrete : Moore Z P Y) (finite : Moore Q P Y)
    (B : Q -> Set Z)
    (cover : ∀ z, ∃ q, z ∈ B q)
    (disjoint : ∀ z q r, z ∈ B q -> z ∈ B r -> q = r)
    (initial : concrete.initial ∈ B finite.initial)
    (transition : ∀ q z p, z ∈ B q -> concrete.step z p ∈ B (finite.step q p))
    (readout : ∀ q z, z ∈ B q -> concrete.out z = finite.out q) :
    Certificate concrete finite where
  label z := Classical.choose (cover z)
  initial := disjoint concrete.initial _ _ (Classical.choose_spec (cover _)) initial
  transition z p :=
    disjoint (concrete.step z p) _ _ (Classical.choose_spec (cover _))
      (transition _ z p (Classical.choose_spec (cover z)))
  readout z := readout _ z (Classical.choose_spec (cover z))

end FiniteAbstraction
end NeuralArtifacts

end -- noncomputable section

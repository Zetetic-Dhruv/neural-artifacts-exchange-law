import NeuralArtifacts.Queries

/-!
# 21. Artifact bits, adaptive table reconstruction, and routed growth

The oracle transcript is generated adaptively. Artifact contents include all
varying parameters and architecture choices; the decoder itself is fixed.
-/
noncomputable section
open Classical Function
open scoped BigOperators
namespace NeuralArtifacts.Information

/-- Halt is represented by `next = none`; subsequent steps are padding. -/
structure Algorithm (A X Y Q T : Type*) where
  initial : A -> Q
  next : Q -> Option X
  receive : Q -> X -> Y -> Q
  output : Q -> T

namespace Algorithm
variable {A X Y Q T : Type*} (alg : Algorithm A X Y Q T)

def step (f : X -> Y) (q : Q) : Q :=
  match alg.next q with | none => q | some x => alg.receive q x (f x)

def run (f : X -> Y) (a : A) : Nat -> Q
  | 0 => alg.initial a
  | n + 1 => alg.step f (run f a n)

/-- Response strings encode every deterministic adaptive execution. A default
symbol fills stopped steps without revealing any extra target information. -/
def answer [Inhabited Y] (f : X -> Y) (a : A) (i : Nat) : Y :=
  match alg.next (alg.run f a i) with | none => default | some x => f x

theorem run_equal_of_answers [Inhabited Y] (f g : X -> Y) (a : A) (t : Nat)
    (h : ∀ i, i < t -> alg.answer f a i = alg.answer g a i) :
    alg.run f a t = alg.run g a t := by
  revert h
  induction t with
  | zero =>
    intro h
    rfl
  | succ t ih =>
    intro h
    have he := ih (fun i hi => h i (by omega))
    simp only [run]
    rw [he]
    unfold step
    cases hn : alg.next (alg.run g a t) with
    | none => rfl
    | some x =>
      have ha := h t (by omega)
      simp only [answer, he, hn] at ha
      show alg.receive (alg.run g a t) x (f x) = alg.receive (alg.run g a t) x (g x)
      rw [ha]
end Algorithm

section Tables
variable {A X Y Q : Type*} [Fintype A] [Fintype X] [Fintype Y] [Inhabited Y]

/-- Exact combinatorial form, before taking logarithms. -/
theorem table_reconstruction_card (alg : Algorithm A X Y Q (X -> Y))
    (artifact : (X -> Y) -> A) (t : Nat)
    (correct : ∀ f, alg.output (alg.run f (artifact f) t) = f) :
    (Fintype.card Y) ^ Fintype.card X ≤ Fintype.card A * (Fintype.card Y) ^ t := by
  let encode : (X -> Y) -> A × (Fin t -> Y) :=
    fun f => (artifact f, fun i => alg.answer f (artifact f) i.val)
  have hi : Injective encode := by
    intro f g he
    have ha : artifact f = artifact g := congrArg Prod.fst he
    have ht := congrArg Prod.snd he
    have hr : alg.run f (artifact f) t = alg.run g (artifact f) t := by
      apply alg.run_equal_of_answers f g (artifact f) t
      intro i hi
      have hh : alg.answer f (artifact f) i = alg.answer g (artifact g) i :=
        congrFun ht ⟨i, hi⟩
      rw [<- ha] at hh
      exact hh
    rw [<- correct f, <- correct g, <- ha, hr]
  have hc := Fintype.card_le_of_injective encode hi
  simpa [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin] using hc

/-- The bit statement is a consequence of an actual cardinality bound. -/
theorem table_bits (alg : Algorithm A X Y Q (X -> Y))
    (artifact : (X -> Y) -> A) (t B : Nat) (budget : Fintype.card A ≤ 2 ^ B)
    (correct : ∀ f, alg.output (alg.run f (artifact f) t) = f) :
    (Fintype.card X : Real) * (Real.log (Fintype.card Y) / Real.log 2) ≤
      B + t * (Real.log (Fintype.card Y) / Real.log 2) := by
  have hq : 0 < Fintype.card Y := Fintype.card_pos_iff.mpr inferInstance
  have hcard := table_reconstruction_card alg artifact t correct
  have hpow : Fintype.card Y ^ Fintype.card X ≤ 2 ^ B * Fintype.card Y ^ t :=
    hcard.trans (Nat.mul_le_mul_right _ budget)
  have hr : (Fintype.card Y : Real) ^ Fintype.card X ≤
      (2 : Real) ^ B * (Fintype.card Y : Real) ^ t := by exact_mod_cast hpow
  have hqp : (0 : Real) < Fintype.card Y := by exact_mod_cast hq
  have hl := Real.log_le_log (pow_pos hqp _) hr
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow] at hl
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv := div_le_div_of_nonneg_right hl htwo.le
  have hne : Real.log 2 ≠ 0 := ne_of_gt htwo
  have he1 : (Fintype.card X : Real) * (Real.log (Fintype.card Y) / Real.log 2)
      = ((Fintype.card X : Real) * Real.log (Fintype.card Y)) / Real.log 2 := by
    ring
  have he2 : (B : Real) + (t : Real) * (Real.log (Fintype.card Y) / Real.log 2)
      = ((B : Real) * Real.log 2 + (t : Real) * Real.log (Fintype.card Y)) / Real.log 2 := by
    field_simp
  rw [he1, he2]
  exact hdiv
end Tables

namespace OracleNormalization
variable {A X Q T : Type*} [Fintype X] [DecidableEq X] [Inhabited X]
variable (alg : Algorithm A X X Q T)

structure Context (X Q : Type*) where
  state : Q
  used : Finset X
  cache : X -> X

def fallback (used : Finset X) : X :=
  if h : ∃ x, x ∉ used then Classical.choose h else default

theorem fallback_fresh (used : Finset X) (h : used.card < Fintype.card X) :
    fallback used ∉ used := by
  have hex : ∃ x, x ∉ used := by
    by_contra hn
    have hu : used = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro x
      by_contra hx
      exact hn ⟨x, hx⟩
    rw [hu] at h
    simp at h
  simp only [fallback, dif_pos hex]
  exact Classical.choose_spec hex

def fresh (c : Context X Q) : X :=
  match alg.next c.state with
  | none => fallback c.used
  | some x => if x ∈ c.used then fallback c.used else x

theorem fresh_not_used (c : Context X Q) (h : c.used.card < Fintype.card X) :
    fresh alg c ∉ c.used := by
  unfold fresh
  cases hn : alg.next c.state with
  | none => exact fallback_fresh c.used h
  | some x =>
    show (if x ∈ c.used then fallback c.used else x) ∉ c.used
    split_ifs with hx
    · exact fallback_fresh c.used h
    · exact hx

def advance (c : Context X Q) (response : X) : Context X Q :=
  let x := fresh alg c
  let cache := Function.update c.cache x response
  { state := match alg.next c.state with
      | none => c.state
      | some q => alg.receive c.state q (cache q)
    used := insert x c.used
    cache := cache }

def run (f : X -> X) (a : A) : Nat -> Context X Q
  | 0 => ⟨alg.initial a, ∅, fun _ => default⟩
  | k + 1 => advance alg (run f a k) (f (fresh alg (run f a k)))

/-- Cache consistency and original control-state agreement hold even on repeated
queries and halted steps. Normalization uses no target-dependent advice. -/
theorem invariant (f : X -> X) (a : A) : ∀ k,
    (run alg f a k).state = alg.run f a k ∧
    (∀ x ∈ (run alg f a k).used, (run alg f a k).cache x = f x) := by
  intro k
  induction k with
  | zero => simp [run, Algorithm.run]
  | succ k ih =>
    let c := run alg f a k
    let x := fresh alg c
    have hc : ∀ q ∈ c.used, c.cache q = f q := ih.2
    have hnew : ∀ q ∈ insert x c.used,
        Function.update c.cache x (f x) q = f q := by
      intro q hq
      by_cases hqx : q = x
      · subst q; simp
      · have hqold : q ∈ c.used := (Finset.mem_insert.mp hq).resolve_left hqx
        simp [Function.update_of_ne hqx, hc q hqold]
    constructor
    · change (advance alg c (f x)).state = alg.step f (alg.run f a k)
      rw [<- ih.1]
      dsimp [advance, Algorithm.step]
      cases hn : alg.next c.state with
      | none => rfl
      | some q =>
        have hmem : q ∈ insert x c.used := by
          by_cases hq : q ∈ c.used
          · exact Finset.mem_insert_of_mem hq
          · have hx : x = q := by simp [x, fresh, hn, hq]
            rw [hx]; simp
        show alg.receive c.state q (Function.update c.cache x (f x) q)
            = alg.receive c.state q (f q)
        rw [hnew q hmem]
    · exact hnew

theorem used_card (f : X -> X) (a : A) (k : Nat) (hk : k ≤ Fintype.card X) :
    (run alg f a k).used.card = k := by
  revert hk
  induction k with
  | zero =>
    intro hk
    simp [run]
  | succ k ih =>
    intro hk
    have hcard := ih (by omega)
    have hf := fresh_not_used alg (run alg f a k) (by omega)
    simp only [run, advance, Finset.card_insert_of_notMem hf, hcard]
theorem used_monotone (f : X -> X) (a : A) :
    Monotone (fun k => (run alg f a k).used) := by
  apply monotone_nat_of_le_succ
  intro k
  exact Finset.subset_insert _ _

def newAnswer (f : X -> X) (a : A) (k : Nat) : X :=
  f (fresh alg (run alg f a k))

theorem newAnswer_injective (f : X -> X) (hf : Injective f) (a : A)
    (t : Nat) (ht : t ≤ Fintype.card X) :
    Injective (fun k : Fin t => newAnswer alg f a k.val) := by
  have different (i j : Fin t) (hijord : i.val < j.val) :
      newAnswer alg f a i.val ≠ newAnswer alg f a j.val := by
    intro heq
    have hl : fresh alg (run alg f a i.val) ∈ (run alg f a (i.val + 1)).used := by
      simp [run, advance]
    have hin : fresh alg (run alg f a i.val) ∈ (run alg f a j.val).used :=
      used_monotone alg f a (by omega) hl
    have hnot := fresh_not_used alg (run alg f a j.val)
      (by rw [used_card alg f a j.val (by omega)]; omega)
    have hloc : fresh alg (run alg f a i.val) = fresh alg (run alg f a j.val) := hf heq
    exact hnot (hloc ▸ hin)
  intro i j hij
  apply Fin.ext
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · exact False.elim (different i j hlt hij)
  · exact heq
  · exact False.elim (different j i hgt hij.symm)

theorem normalized_run_equal (f g : X -> X) (a : A) (t : Nat)
    (h : ∀ i, i < t -> newAnswer alg f a i = newAnswer alg g a i) :
    run alg f a t = run alg g a t := by
  revert h
  induction t with
  | zero =>
    intro h
    rfl
  | succ t ih =>
    intro h
    have hp := ih (fun i hi => h i (by omega))
    have ha := h t (by omega)
    change advance alg (run alg f a t) (newAnswer alg f a t) =
      advance alg (run alg g a t) (newAnswer alg g a t)
    rw [hp, ha]
end OracleNormalization

section Permutations
variable {A X Q : Type*} [Fintype A] [Fintype X] [DecidableEq X] [Inhabited X]

/-- Repeated queries and early stopping are handled by the normalization above. -/
theorem permutation_reconstruction_card
    (alg : Algorithm A X X Q (Equiv.Perm X)) (artifact : Equiv.Perm X -> A)
    (t : Nat) (ht : t ≤ Fintype.card X)
    (correct : ∀ f : Equiv.Perm X, alg.output (alg.run f (artifact f) t) = f) :
    (Fintype.card X - t).factorial ≤ Fintype.card A := by
  let encode : Equiv.Perm X -> A × (Fin t ↪ X) := fun f =>
    (artifact f, ⟨fun i => OracleNormalization.newAnswer alg f (artifact f) i.val,
      OracleNormalization.newAnswer_injective alg f f.injective (artifact f) t ht⟩)
  have hi : Injective encode := by
    intro f g h
    have ha : artifact f = artifact g := congrArg Prod.fst h
    have hv := congrArg Prod.snd h
    have hc : OracleNormalization.run alg f (artifact f) t =
        OracleNormalization.run alg g (artifact f) t := by
      apply OracleNormalization.normalized_run_equal
      intro i hi
      have he : OracleNormalization.newAnswer alg f (artifact f) i
          = OracleNormalization.newAnswer alg g (artifact g) i :=
        congrArg (fun e : Fin t ↪ X => e ⟨i, hi⟩) hv
      rw [<- ha] at he
      exact he
    have hs := congrArg OracleNormalization.Context.state hc
    rw [(OracleNormalization.invariant alg f (artifact f) t).1,
      (OracleNormalization.invariant alg g (artifact f) t).1] at hs
    rw [<- correct f, <- correct g, <- ha, hs]
  have hc := Fintype.card_le_of_injective encode hi
  simp only [Fintype.card_perm, Fintype.card_prod, Fintype.card_embedding_eq, Fintype.card_fin] at hc
  have hfac : (Fintype.card X - t).factorial * (Fintype.card X).descFactorial t =
      (Fintype.card X).factorial := Nat.factorial_mul_descFactorial ht
  have hd : 0 < (Fintype.card X).descFactorial t := Nat.descFactorial_pos.mpr ht
  rw [<- hfac] at hc
  by_contra hnot
  have hstrict : Fintype.card A < (Fintype.card X - t).factorial := lt_of_not_ge hnot
  nlinarith

theorem permutation_bits (alg : Algorithm A X X Q (Equiv.Perm X))
    (artifact : Equiv.Perm X -> A) (t B : Nat) (ht : t ≤ Fintype.card X)
    (budget : Fintype.card A ≤ 2 ^ B)
    (correct : ∀ f : Equiv.Perm X, alg.output (alg.run f (artifact f) t) = f) :
    Real.log ((Fintype.card X - t).factorial) / Real.log 2 ≤ B := by
  have hc := (permutation_reconstruction_card alg artifact t ht correct).trans budget
  have hp : (0 : Real) < (Fintype.card X - t).factorial := by
    exact_mod_cast Nat.factorial_pos _
  have hr : ((Fintype.card X - t).factorial : Real) ≤ (2 : Real) ^ B := by exact_mod_cast hc
  have hl := Real.log_le_log hp hr
  rw [Real.log_pow] at hl
  exact (div_le_iff₀ (Real.log_pos (by norm_num : (1 : Real) < 2))).mpr hl
end Permutations

namespace RoutedGrowth
variable {Position Expert Label Route : Type*}
variable [Fintype Position] [Fintype Expert] [Fintype Label] [Fintype Route]
variable [DecidableEq Expert]

/-- Positions routed to one expert are the only positions it must describe. -/
def Assigned (routing : Route -> Position -> Expert) (r : Route) (i : Expert) :=
  {x : Position // routing r x = i}

def LocalTable (routing : Route -> Position -> Expert) (r : Route) (i : Expert) :=
  Assigned routing r i -> Label

/-- H(r,i) is the realized family of restrictions, not an arbitrary global bound. -/
def glue (routing : Route -> Position -> Expert)
    (H : (r : Route) -> (i : Expert) -> Finset (LocalTable (Label := Label) routing r i))
    (z : Sigma (fun r => (i : Expert) -> {h // h ∈ H r i})) : Position -> Label :=
  fun x => (z.2 (routing z.1 x)).val ⟨x, rfl⟩

omit [Fintype Position] [Fintype Label] in
theorem sample_local_growth (routing : Route -> Position -> Expert)
    (H : (r : Route) -> (i : Expert) -> Finset (LocalTable routing r i))
    (models : Finset (Position -> Label))
    (hmodels : ∀ f ∈ models, ∃ z, glue routing H z = f) :
    models.card ≤ ∑ r, ∏ i, (H r i).card := by
  let target : Type _ := {f // f ∈ models}
  let source : Type _ := Sigma (fun r => (i : Expert) -> {h // h ∈ H r i})
  let encode : target -> source := fun f => Classical.choose (hmodels f.val f.property)
  have he (f : target) : glue routing H (encode f) = f.val :=
    Classical.choose_spec (hmodels f.val f.property)
  have hi : Injective encode := by
    intro f g h
    apply Subtype.ext
    rw [<- he f, <- he g, h]
  have hc := Fintype.card_le_of_injective encode hi
  simpa [target, source, Fintype.card_sigma, Fintype.card_pi, Fintype.card_coe] using hc
end RoutedGrowth

end NeuralArtifacts.Information

end -- noncomputable section

import Mathlib

/-!
# Neural artifacts: proof notebook

This notebook accompanies *Model Inference from Neural Artifacts: An Exchange
Law for Structure and Memory*. The files are mathematical proof scripts, not
an assertion that a particular Lean/mathlib release has accepted them.

Conventions:
* All finite-state semantics are exact. No floating-point execution is used.
* Alphabet size and bit precision are different quantities.
* A finite-state interface contains every persistent register.
* Classical choice is used for quotient representatives and existence proofs,
  never as a claim of an effective real-algebraic decision procedure.
* `RealAlgebraBoundary` makes the external quantifier-elimination interface
  explicit. It is not needed by the central exchange theorem.

The construction below turns algebraic meet laws into the standard mathlib
order structure. This is used for operationally extracted state spaces and
for idempotents of commutative monoids.
-/

noncomputable section
open Classical Function
open scoped BigOperators
namespace NeuralArtifacts

universe u v w

/-- Algebraic presentation of a meet operation. -/
structure MeetLaws (A : Type u) where
  op : A -> A -> A
  assoc : ∀ a b c, op (op a b) c = op a (op b c)
  comm : ∀ a b, op a b = op b a
  idem : ∀ a, op a a = a

namespace MeetLaws
variable {A : Type u} (L : MeetLaws A)

@[reducible] def order : SemilatticeInf A where
  inf := L.op
  le a b := L.op a b = a
  le_refl a := L.idem a
  le_trans a b c hab hbc := by
    calc
      L.op a c = L.op (L.op a b) c := by rw [hab]
      _ = L.op a (L.op b c) := L.assoc a b c
      _ = L.op a b := by rw [hbc]
      _ = a := hab
  le_antisymm a b hab hba := by
    calc
      a = L.op a b := hab.symm
      _ = L.op b a := L.comm a b
      _ = b := hba
  inf_le_left a b := by
    calc
      L.op (L.op a b) a = L.op a (L.op b a) := L.assoc _ _ _
      _ = L.op a (L.op a b) := by rw [L.comm b a]
      _ = L.op (L.op a a) b := (L.assoc _ _ _).symm
      _ = L.op a b := by rw [L.idem]
  inf_le_right a b := by
    rw [L.assoc, L.idem]
  le_inf a b c hab hac := by
    rw [<- L.assoc, hab, hac]

end MeetLaws

/-- A meet homomorphism with an explicit top-preservation equation. -/
structure MeetHom (A : Type u) (B : Type v)
    [SemilatticeInf A] [OrderTop A]
    [SemilatticeInf B] [OrderTop B] where
  toFun : A -> B
  map_inf : ∀ a b, toFun (a ⊓ b) = toFun a ⊓ toFun b
  map_top : toFun ⊤ = ⊤

instance {A : Type u} {B : Type v}
    [SemilatticeInf A] [OrderTop A]
    [SemilatticeInf B] [OrderTop B] :
    CoeFun (MeetHom A B) (fun _ => A -> B) := ⟨MeetHom.toFun⟩

namespace MeetHom
variable {A : Type u} {B : Type v} {C : Type w}
variable [SemilatticeInf A] [OrderTop A]
variable [SemilatticeInf B] [OrderTop B]
variable [SemilatticeInf C] [OrderTop C]

@[simp] theorem inf_apply (f : MeetHom A B) (a b : A) :
    f (a ⊓ b) = f a ⊓ f b := f.map_inf a b
@[simp] theorem top_apply (f : MeetHom A B) : f ⊤ = ⊤ := f.map_top

theorem monotone (f : MeetHom A B) : Monotone f := by
  intro a b hab
  apply inf_eq_left.mp
  rw [<- f.map_inf, inf_eq_left.mpr hab]

def id (A : Type u) [SemilatticeInf A] [OrderTop A] : MeetHom A A :=
  ⟨fun a => a, fun _ _ => rfl, rfl⟩

def comp (g : MeetHom B C) (f : MeetHom A B) : MeetHom A C where
  toFun a := g (f a)
  map_inf a b := by rw [f.map_inf, g.map_inf]
  map_top := by rw [f.map_top, g.map_top]

theorem map_finset_inf {I : Type*} (f : MeetHom A B)
    (s : Finset I) (g : I -> A) :
    f (s.inf g) = s.inf (fun i => f (g i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [f.map_inf, ih]

end MeetHom

/-- A wrapper whose multiplication is meet. This avoids changing the usual
multiplication on numeric types such as `Fin n`. -/
structure MeetCarrier (A : Type u) where
  val : A
  deriving DecidableEq

namespace MeetCarrier
variable {A : Type u}
@[ext] theorem ext {x y : MeetCarrier A} (h : x.val = y.val) : x = y := by
  cases x; cases y; cases h; rfl

def equiv : MeetCarrier A ≃ A where
  toFun := val
  invFun := mk
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; rfl

instance [Fintype A] : Fintype (MeetCarrier A) := Fintype.ofEquiv A equiv.symm
@[simp] theorem card [Fintype A] :
    Fintype.card (MeetCarrier A) = Fintype.card A := Fintype.card_congr equiv

instance [SemilatticeInf A] [OrderTop A] : CommMonoid (MeetCarrier A) where
  mul x y := ⟨x.val ⊓ y.val⟩
  one := ⟨⊤⟩
  mul_assoc x y z := by apply ext; exact inf_assoc _ _ _
  one_mul x := by apply ext; exact top_inf_eq _
  mul_one x := by apply ext; exact inf_top_eq _
  mul_comm x y := by apply ext; exact inf_comm _ _

@[simp] theorem val_one [SemilatticeInf A] [OrderTop A] :
    (1 : MeetCarrier A).val = ⊤ := rfl
@[simp] theorem val_mul [SemilatticeInf A] [OrderTop A]
    (x y : MeetCarrier A) : (x * y).val = x.val ⊓ y.val := rfl
end MeetCarrier

/-- A fully explicit finite embedding from a cardinality inequality. -/
def finiteEmbedding {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (h : Fintype.card A ≤ Fintype.card B) : A ↪ B where
  toFun a := (Fintype.equivFin B).symm
    ⟨((Fintype.equivFin A) a).val,
      lt_of_lt_of_le ((Fintype.equivFin A) a).isLt h⟩
  inj' := by
    intro a b hab
    apply (Fintype.equivFin A).injective
    apply Fin.ext
    have hh := congrArg (fun x => ((Fintype.equivFin B) x).val) hab
    simpa using hh

/-- Equal finite cardinalities plus surjectivity imply injectivity. -/
theorem injective_of_surjective_card_eq {A : Type u} {B : Type v}
    [Fintype A] [Fintype B] (f : A -> B)
    (hs : Surjective f) (hc : Fintype.card A = Fintype.card B) :
    Injective f := by
  let e : B ≃ A := (Fintype.equivFin B).trans
    ((Equiv.cast (congrArg Fin hc.symm)).trans (Fintype.equivFin A).symm)
  have hs' : Surjective (e ∘ f) := e.surjective.comp hs
  have hi : Injective (e ∘ f) :=
    (Finite.injective_iff_surjective).mpr hs'
  intro a b hab
  exact hi (congrArg e hab)

/-- Every nonempty finite collection of natural numbers attains its supremum. -/
theorem finset_sup_attained {A : Type*} (s : Finset A) (f : A -> Nat)
    (hs : s.Nonempty) : ∃ a ∈ s, f a = s.sup f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
    by_cases hn : s.Nonempty
    · obtain ⟨b, hb, hmax⟩ := ih hn
      by_cases hab : f a ≤ s.sup f
      · refine ⟨b, Finset.mem_insert_of_mem hb, ?_⟩
        simpa [Finset.sup_insert, max_eq_right hab] using hmax
      · refine ⟨a, Finset.mem_insert_self _ _, ?_⟩
        simp [Finset.sup_insert, max_eq_left (le_of_lt (lt_of_not_ge hab))]
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      subst s
      exact ⟨a, by simp, by simp⟩

/-- A generic finite observation alphabet machine. -/
structure Moore (Q : Type u) (P : Type v) (Y : Type w) where
  initial : Q
  step : Q -> P -> Q
  out : Q -> Y

namespace Moore
variable {Q : Type u} {P : Type v} {Y : Type w}

def runFrom (A : Moore Q P Y) (q : Q) : List P -> Q
  | [] => q
  | p :: s => runFrom A (A.step q p) s

def run (A : Moore Q P Y) (s : List P) : Q := A.runFrom A.initial s

@[simp] theorem runFrom_nil (A : Moore Q P Y) (q : Q) :
    A.runFrom q [] = q := rfl
@[simp] theorem runFrom_cons (A : Moore Q P Y) (q : Q) (p : P) (s : List P) :
    A.runFrom q (p :: s) = A.runFrom (A.step q p) s := rfl
@[simp] theorem run_nil (A : Moore Q P Y) : A.run [] = A.initial := rfl

theorem runFrom_append (A : Moore Q P Y) (q : Q) (s t : List P) :
    A.runFrom q (s ++ t) = A.runFrom (A.runFrom q s) t := by
  induction s generalizing q with
  | nil => rfl
  | cons p s ih => exact ih (A.step q p)

@[simp] theorem run_append (A : Moore Q P Y) (s t : List P) :
    A.run (s ++ t) = A.runFrom (A.run s) t := A.runFrom_append _ _ _

@[simp] theorem run_snoc (A : Moore Q P Y) (s : List P) (p : P) :
    A.run (s ++ [p]) = A.step (A.run s) p := by simp [runFrom]

def Reach (A : Moore Q P Y) := {q : Q // ∃ s, A.run s = q}

instance (A : Moore Q P Y) [Finite Q] : Finite A.Reach :=
  inferInstanceAs (Finite {q : Q // ∃ s, A.run s = q})

noncomputable instance (A : Moore Q P Y) [Fintype Q] : Fintype A.Reach := Fintype.ofFinite _

def rInitial (A : Moore Q P Y) : A.Reach := ⟨A.initial, [], rfl⟩

def rStep (A : Moore Q P Y) (q : A.Reach) (p : P) : A.Reach :=
  ⟨A.step q.val p, by
    obtain ⟨s, hs⟩ := q.property
    exact ⟨s ++ [p], by simp [hs]⟩⟩

def rRun (A : Moore Q P Y) (s : List P) : A.Reach := ⟨A.run s, s, rfl⟩

@[simp] theorem rRun_nil (A : Moore Q P Y) : A.rRun [] = A.rInitial := rfl
@[simp] theorem rRun_snoc (A : Moore Q P Y) (s : List P) (p : P) :
    A.rRun (s ++ [p]) = A.rStep (A.rRun s) p := by
  apply Subtype.ext; simp [rRun, rStep]

def ObsEq (A : Moore Q P Y) (q r : Q) : Prop :=
  ∀ s, A.out (A.runFrom q s) = A.out (A.runFrom r s)

theorem obsEq_equivalence (A : Moore Q P Y) : Equivalence A.ObsEq := by
  refine ⟨?_, ?_, ?_⟩
  · intro q s; rfl
  · intro q r h s; exact (h s).symm
  · intro q r z hqr hrz s; exact (hqr s).trans (hrz s)

theorem obsEq_step (A : Moore Q P Y) {q r : Q} (h : A.ObsEq q r) (p : P) :
    A.ObsEq (A.step q p) (A.step r p) := by
  intro s
  exact h (p :: s)

theorem simulation_run {Q' : Type*} (A : Moore Q P Y) (B : Moore Q' P Y)
    (f : Q -> Q') (hi : f A.initial = B.initial)
    (hs : ∀ q p, f (A.step q p) = B.step (f q) p) (s : List P) :
    f (A.run s) = B.run s := by
  have aux : ∀ q s, f (A.runFrom q s) = B.runFrom (f q) s := by
    intro q s
    induction s generalizing q with
    | nil => rfl
    | cons p s ih => simpa [runFrom, hs] using ih (A.step q p)
  simpa [run, hi] using aux A.initial s

theorem simulation_outputs {Q' : Type*} (A : Moore Q P Y) (B : Moore Q' P Y)
    (f : Q -> Q') (hi : f A.initial = B.initial)
    (hs : ∀ q p, f (A.step q p) = B.step (f q) p)
    (ho : ∀ q, A.out q = B.out (f q)) (s : List P) :
    A.out (A.run s) = B.out (B.run s) := by
  rw [ho, simulation_run A B f hi hs]

end Moore
end NeuralArtifacts

end -- noncomputable section

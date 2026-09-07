import NeuralArtifacts.CutExchange

/-!
# 7. Compositional and one-shot residual information

Paper: Proposition 5, Proposition 10, equations (11)--(15).

The minimization is over actual congruences. Equality is a feasible residual,
so existence of the minimum is proved rather than postulated.
-/

noncomputable section
open Classical Function
open scoped BigOperators
namespace NeuralArtifacts
namespace Congruence
universe u v w
variable {R : Type u} [SemilatticeInf R] [OrderTop R]

structure Rel (R : Type u) [SemilatticeInf R] extends Setoid R where
  compatible : ∀ {a a' b b'}, r a a' -> r b b' -> r (a ⊓ b) (a' ⊓ b')

/-- A relation accessor, avoiding an implicit global setoid on `R`. -/
def Holds (c : Rel R) (a b : R) : Prop := c.toSetoid.r a b

omit [OrderTop R] in
@[refl] theorem holds_refl (c : Rel R) (r : R) : Holds c r r := c.toSetoid.iseqv.refl r
omit [OrderTop R] in
@[symm] theorem holds_symm (c : Rel R) {r s : R} : Holds c r s -> Holds c s r := c.toSetoid.iseqv.symm
omit [OrderTop R] in
@[trans] theorem holds_trans (c : Rel R) {r s t : R} :
    Holds c r s -> Holds c s t -> Holds c r t := c.toSetoid.iseqv.trans

def equality : Rel R where
  r := Eq
  iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  compatible := by intro a a' b b' ha hb; cases ha; cases hb; rfl

def kernel {A : Type v} [SemilatticeInf A] [OrderTop A] (f : MeetHom R A) : Rel R where
  r a b := f a = f b
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a; rfl
    · intro a b h; exact h.symm
    · intro a b c h1 h2; exact h1.trans h2
  compatible := by intro a a' b b' ha hb; rw [f.map_inf, f.map_inf, ha, hb]

def Quot (c : Rel R) := Quotient c.toSetoid
instance (c : Rel R) [Finite R] : Finite (Quot c) :=
  inferInstanceAs (Finite (Quotient c.toSetoid))

noncomputable instance (c : Rel R) [Fintype R] : Fintype (Quot c) := Fintype.ofFinite _
def proj (c : Rel R) (r : R) : Quot c := Quotient.mk c.toSetoid r

omit [OrderTop R] in
@[simp] theorem proj_eq (c : Rel R) (a b : R) : proj c a = proj c b ↔ Holds c a b :=
  Quotient.eq

def qInf (c : Rel R) (x y : Quot c) : Quot c :=
  Quotient.liftOn x
    (fun a => Quotient.liftOn y (fun b => proj c (a ⊓ b))
      (by intro b b' h; exact Quotient.sound (c.compatible (c.toSetoid.iseqv.refl a) h)))
    (by
      intro a a' h
      refine Quotient.inductionOn y ?_
      intro b
      exact Quotient.sound (c.compatible h (c.toSetoid.iseqv.refl b)))

omit [OrderTop R] in
@[simp] theorem qInf_proj (c : Rel R) (a b : R) :
    qInf c (proj c a) (proj c b) = proj c (a ⊓ b) := rfl

def laws (c : Rel R) : MeetLaws (Quot c) where
  op := qInf c
  assoc := by
    intro x y z
    refine Quotient.inductionOn x ?_; intro a
    refine Quotient.inductionOn y ?_; intro b
    refine Quotient.inductionOn z ?_; intro d
    exact congrArg (proj c) (inf_assoc a b d)
  comm := by
    intro x y
    refine Quotient.inductionOn x ?_; intro a
    refine Quotient.inductionOn y ?_; intro b
    exact congrArg (proj c) (inf_comm a b)
  idem := by
    intro x
    refine Quotient.inductionOn x ?_; intro a
    exact congrArg (proj c) (inf_idem a)

instance (c : Rel R) : SemilatticeInf (Quot c) := (laws c).order
instance (c : Rel R) : OrderTop (Quot c) where
  top := proj c ⊤
  le_top x := by
    refine Quotient.inductionOn x ?_
    intro a
    change proj c (a ⊓ ⊤) = proj c a
    simp

def quotientHom (c : Rel R) : MeetHom R (Quot c) :=
  ⟨proj c, fun _ _ => rfl, rfl⟩

omit [OrderTop R] in
theorem proj_surjective (c : Rel R) : Surjective (proj c) := by
  intro q; refine Quotient.inductionOn q ?_; intro r; exact ⟨r, rfl⟩

/-- The two representations have no common unidentified distinction. -/
def Joint (a b : Rel R) : Prop := ∀ r s, Holds a r s -> Holds b r s -> r = s

omit [OrderTop R] in
theorem joint_iff_pair_injective (a b : Rel R) :
    Joint a b ↔ Injective (fun r => (proj a r, proj b r)) := by
  constructor
  · intro h r s hrs
    exact h r s ((proj_eq a r s).mp (congrArg Prod.fst hrs))
      ((proj_eq b r s).mp (congrArg Prod.snd hrs))
  · intro h r s ha hb
    apply h
    exact Prod.ext ((proj_eq a r s).mpr ha) ((proj_eq b r s).mpr hb)

theorem kernels_joint_iff {A : Type v} {B : Type w}
    [SemilatticeInf A] [OrderTop A] [SemilatticeInf B] [OrderTop B]
    (a : MeetHom R A) (b : MeetHom R B) :
    Joint (kernel a) (kernel b) ↔ Injective (fun r => (a r, b r)) := by
  constructor
  · intro h r s he
    exact h r s (congrArg Prod.fst he) (congrArg Prod.snd he)
  · intro h r s ha hb
    exact h (Prod.ext ha hb)

/-- An exact inverse on the image, without requiring a default output value. -/
def imageDecoder {A : Type*} (f : R -> A) (_hi : Injective f) : Set.range f -> R :=
  fun x => Classical.choose x.property

omit [SemilatticeInf R] [OrderTop R] in
theorem imageDecoder_spec {A : Type*} (f : R -> A) (hi : Injective f) (r : R) :
    imageDecoder f hi ⟨f r, r, rfl⟩ = r := by
  apply hi
  exact Classical.choose_spec (show ∃ z, f z = f r from ⟨r, rfl⟩)

/-- An injective code can be read at every state. -/
def totalRead {A Y : Type*} (f : R -> A) (rho : R -> Y) (x : A) : Y :=
  if h : ∃ r, f r = x then rho (Classical.choose h) else rho ⊤

theorem totalRead_spec {A Y : Type*} (f : R -> A) (rho : R -> Y)
    (hi : Injective f) (r : R) : totalRead f rho (f r) = rho r := by
  unfold totalRead
  split_ifs with h
  · have he : Classical.choose h = r := hi (Classical.choose_spec h)
    rw [he]
  · exact False.elim (h ⟨r, rfl⟩)

/-- Proposition 10: preservation of the full continuation semantics is exactly
joint injectivity, once the target states are separated by continuations. -/
theorem readout_exists_iff {A B Y : Type*}
    [SemilatticeInf A] [OrderTop A] [SemilatticeInf B] [OrderTop B]
    (a : MeetHom R A) (b : MeetHom R B) (rho : R -> Y)
    (hsep : ∀ r s, (∀ h, rho (r ⊓ h) = rho (s ⊓ h)) -> r = s) :
    (∃ out : A × B -> Y, ∀ r, out (a r, b r) = rho r) ↔
      Injective (fun r => (a r, b r)) := by
  constructor
  · rintro ⟨out, hout⟩ r s hrs
    apply hsep r s
    intro h
    have ha := congrArg Prod.fst hrs
    have hb := congrArg Prod.snd hrs
    rw [<- hout, <- hout, a.map_inf, a.map_inf, b.map_inf, b.map_inf]
    simp only at ha hb
    rw [ha, hb]
  · intro hi
    exact ⟨totalRead (fun r => (a r, b r)) rho,
      fun r => totalRead_spec _ _ hi r⟩

def attainable [Fintype R] (a : Rel R) (m : Nat) : Prop :=
  ∃ b : Rel R, Joint a b ∧ Fintype.card (Quot b) = m

omit [OrderTop R] in
theorem attainable_exists [Fintype R] (a : Rel R) : ∃ m, attainable a m := by
  refine ⟨Fintype.card (Quot (equality : Rel R)), equality, ?_, rfl⟩
  intro r s ha hb
  exact hb

def minimumResidual [Fintype R] (a : Rel R) : Nat := Nat.find (attainable_exists a)

omit [OrderTop R] in
theorem minimumResidual_attained [Fintype R] (a : Rel R) :
    ∃ b : Rel R, Joint a b ∧ Fintype.card (Quot b) = minimumResidual a :=
  Nat.find_spec (attainable_exists a)

omit [OrderTop R] in
theorem minimumResidual_le [Fintype R] (a b : Rel R) (h : Joint a b) :
    minimumResidual a ≤ Fintype.card (Quot b) :=
  Nat.find_min' (attainable_exists a) ⟨b, h, rfl⟩

omit [OrderTop R] in
theorem residual_antitone [Fintype R] (a a' : Rel R)
    (h : ∀ r s, Holds a' r s -> Holds a r s) :
    minimumResidual a' ≤ minimumResidual a := by
  obtain ⟨b, hb, hc⟩ := minimumResidual_attained a
  have hj : Joint a' b := by intro r s ha hb'; exact hb r s (h r s ha) hb'
  rw [<- hc]
  exact minimumResidual_le a' b hj

/-- Kernel quotients are exactly the image when the homomorphism is surjective. -/
def kernelQuotientEquiv {A : Type*} [SemilatticeInf A] [OrderTop A]
    (f : MeetHom R A) (hf : Surjective f) : Quot (kernel f) ≃ A where
  toFun := Quotient.lift f (by intro r s h; exact h)
  invFun a := proj (kernel f) (Classical.choose (hf a))
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro r
    apply Quotient.sound
    exact Classical.choose_spec (hf (f r))
  right_inv a := Classical.choose_spec (hf a)

theorem kernel_quotient_card {A : Type*} [Fintype R] [Fintype A]
    [SemilatticeInf A] [OrderTop A] (f : MeetHom R A) (hf : Surjective f) :
    Fintype.card (Quot (kernel f)) = Fintype.card A :=
  Fintype.card_congr (kernelQuotientEquiv f hf)

end Congruence

namespace StaticResidual
variable {R A : Type*} [Fintype R]

def Fiber (f : R -> A) (a : A) := {r : R // f r = a}
instance (f : R -> A) (a : A) : Finite (Fiber f a) :=
  inferInstanceAs (Finite {r : R // f r = a})

noncomputable instance (f : R -> A) (a : A) : Fintype (Fiber f a) := Fintype.ofFinite _

def largest (f : R -> A) : Nat :=
  Finset.univ.sup (fun r : R => Fintype.card (Fiber f (f r)))

theorem fiber_le_largest (f : R -> A) (a : A) :
    Fintype.card (Fiber f a) ≤ largest f := by
  by_cases h : ∃ r, f r = a
  · obtain ⟨r, rfl⟩ := h
    exact Finset.le_sup (f := fun r' : R => Fintype.card (Fiber f (f r')))
      (Finset.mem_univ r)
  · haveI : IsEmpty (Fiber f a) := ⟨fun x => h ⟨x.val, x.property⟩⟩
    have hz : Fintype.card (Fiber f a) = 0 := Fintype.card_eq_zero
    omega

/-- One-shot residuals need enough distinct values inside every structural fibre. -/
theorem lower_bound {G : Type*} [Fintype G] (f : R -> A) (g : R -> G)
    (hi : Injective (fun r => (f r, g r))) : largest f ≤ Fintype.card G := by
  apply Finset.sup_le
  intro r hr
  let fg : Fiber f (f r) -> G := fun x => g x.val
  have hfg : Injective fg := by
    intro x y he
    apply Subtype.ext
    apply hi
    exact Prod.ext (x.property.trans y.property.symm) he
  exact Fintype.card_le_of_injective fg hfg

/-- Reuse the same labels in different fibres; no update law is imposed. -/
def labels (f : R -> A) : R -> Fin (largest f) :=
  fun r => finiteEmbedding (A := Fiber f (f r)) (B := Fin (largest f))
    (by simpa using fiber_le_largest f (f r)) ⟨r, rfl⟩

theorem labels_joint_injective (f : R -> A) :
    Injective (fun r => (f r, labels f r)) := by
  intro r s h
  have ha : f r = f s := congrArg Prod.fst h
  have hg : labels f r = labels f s := congrArg Prod.snd h
  let e : Fiber f (f r) ↪ Fin (largest f) :=
    finiteEmbedding (A := Fiber f (f r)) (B := Fin (largest f))
      (by simpa using fiber_le_largest f (f r))
  have htransport : e ⟨s, ha.symm⟩ = labels f s := by
    have key : ∀ (a : A) (hs : f s = a),
        finiteEmbedding (A := Fiber f a) (B := Fin (largest f))
          (by simpa using fiber_le_largest f a) ⟨s, hs⟩ = labels f s := by
      intro a hs
      subst hs
      rfl
    exact key (f r) ha.symm
  have he : e ⟨r, rfl⟩ = e ⟨s, ha.symm⟩ := hg.trans htransport.symm
  have hsub := e.injective he
  exact congrArg Subtype.val hsub

/-- Exact minimum: a residual with `m` labels exists precisely above the largest fibre. -/
theorem exists_labels_iff (f : R -> A) (m : Nat) :
    (∃ g : R -> Fin m, Injective (fun r => (f r, g r))) ↔ largest f ≤ m := by
  constructor
  · rintro ⟨g, hg⟩
    simpa using lower_bound f g hg
  · intro hm
    let e : Fin (largest f) ↪ Fin m := finiteEmbedding (by simpa using hm)
    refine ⟨fun r => e (labels f r), ?_⟩
    intro r s h
    have h' : (f r, e (labels f r)) = (f s, e (labels f s)) := h
    injection h' with h1 h2
    apply labels_joint_injective f
    show (f r, labels f r) = (f s, labels f s)
    exact Prod.ext h1 (e.injective h2)

end StaticResidual

namespace BooleanExchange
variable {A B : Type*} [SemilatticeInf A] [OrderTop A]
variable [SemilatticeInf B] [OrderTop B] [Fintype A] [Fintype B]

def fstHom : MeetHom (A × B) A := ⟨Prod.fst, fun _ _ => rfl, rfl⟩
def sndHom : MeetHom (A × B) B := ⟨Prod.snd, fun _ _ => rfl, rfl⟩

def fstFiberEquiv (a : A) : StaticResidual.Fiber (Prod.fst : A × B -> A) a ≃ B where
  toFun x := x.val.2
  invFun b := ⟨(a, b), rfl⟩
  left_inv := by
    rintro ⟨⟨a', b⟩, h⟩
    apply Subtype.ext
    exact Prod.ext h.symm rfl
  right_inv := by intro b; rfl

theorem static_exact :
    StaticResidual.largest (Prod.fst : A × B -> A) = Fintype.card B := by
  have hcard : ∀ a : A,
      Fintype.card (StaticResidual.Fiber (Prod.fst : A × B -> A) a) = Fintype.card B :=
    fun a => Fintype.card_congr (fstFiberEquiv a)
  apply le_antisymm
  · apply Finset.sup_le
    intro r hr
    rw [hcard]
  · have h := Finset.le_sup (f := fun r : A × B =>
        Fintype.card (StaticResidual.Fiber (Prod.fst : A × B -> A) r.1))
      (Finset.mem_univ (⊤, ⊤))
    simpa [hcard, StaticResidual.largest] using h

theorem compositional_exact :
    Congruence.minimumResidual (Congruence.kernel (fstHom : MeetHom (A × B) A)) =
      Fintype.card B := by
  let a := Congruence.kernel (fstHom : MeetHom (A × B) A)
  let b := Congruence.kernel (sndHom : MeetHom (A × B) B)
  have hj : Congruence.Joint a b := by
    intro r s h1 h2
    exact Prod.ext h1 h2
  have hb : Fintype.card (Congruence.Quot b) = Fintype.card B :=
    Congruence.kernel_quotient_card sndHom (fun y => ⟨(⊤, y), rfl⟩)
  apply le_antisymm
  · simpa [a, hb] using Congruence.minimumResidual_le a b hj
  · obtain ⟨c, hc, hcard⟩ := Congruence.minimumResidual_attained a
    have hi : Injective (fun r : A × B => (r.1, Congruence.proj c r)) := by
      intro r s h
      have h' : (r.1, Congruence.proj c r) = (s.1, Congruence.proj c s) := h
      injection h' with h1 h2
      apply hc r s h1
      exact (Congruence.proj_eq c r s).mp h2
    have hl := StaticResidual.lower_bound (Prod.fst : A × B -> A)
      (Congruence.proj c) hi
    rw [static_exact, hcard] at hl
    exact hl

/-- A Boolean store split into exposed and hidden coordinates.
`Fin s` and `Fin t` are the two parts of a coordinate partition. -/
theorem boolean_coordinate_law (s t : Nat) :
    Congruence.minimumResidual
      (Congruence.kernel
        (fstHom : MeetHom ((Fin s -> Bool) × (Fin t -> Bool)) (Fin s -> Bool))) = 2 ^ t := by
  simpa [Fintype.card_fun, Fintype.card_fin] using
    (compositional_exact (A := Fin s -> Bool) (B := Fin t -> Bool))

/-- In the paper's notation `k=s+t`, the residual has `2^(k-s)` states.
`k - s` is truncated subtraction, so no side condition is needed. -/
theorem boolean_coordinate_law_sub (k s : Nat) :
    Congruence.minimumResidual
      (Congruence.kernel
        (fstHom : MeetHom ((Fin s -> Bool) × (Fin (k-s) -> Bool)) (Fin s -> Bool))) =
      2 ^ (k - s) := boolean_coordinate_law s (k - s)

end BooleanExchange
end NeuralArtifacts

end -- noncomputable section

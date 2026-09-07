import NeuralArtifacts.Prelude

/-!
# 1. Version spaces and the canonical inference quotient

Paper: Definition 1, Theorem 2, Appendix A.1.

We first construct the meet-semilattice of reachable version spaces. The
quotient theorem is then proved for any generated meet-semilattice. Its
application to the version-space construction requires no separation
assumption on the candidate models or on the readout.
-/

noncomputable section
open Classical Function
open scoped BigOperators
namespace NeuralArtifacts
namespace VersionSpace
universe u v
variable {C : Type u} {P : Type v}

def version (K : P -> Set C) : List P -> Set C
  | [] => Set.univ
  | p :: s => K p ∩ version K s

@[simp] theorem version_nil (K : P -> Set C) : version K [] = Set.univ := rfl
@[simp] theorem version_cons (K : P -> Set C) (p : P) (s : List P) :
    version K (p :: s) = K p ∩ version K s := rfl

@[simp] theorem version_append (K : P -> Set C) (s t : List P) :
    version K (s ++ t) = version K s ∩ version K t := by
  induction s with
  | nil => simp [version]
  | cons p s ih => simp [version, ih, Set.inter_assoc]

def Reachable (K : P -> Set C) := {V : Set C // ∃ s, version K s = V}

instance (K : P -> Set C) [Finite C] : Finite (Reachable K) :=
  inferInstanceAs (Finite {V : Set C // ∃ s, version K s = V})

noncomputable instance (K : P -> Set C) [Fintype C] : Fintype (Reachable K) :=
  Fintype.ofFinite _

def inf (K : P -> Set C) (V W : Reachable K) : Reachable K :=
  ⟨V.val ∩ W.val, by
    obtain ⟨s, hs⟩ := V.property
    obtain ⟨t, ht⟩ := W.property
    exact ⟨s ++ t, by simp [hs, ht]⟩⟩

def laws (K : P -> Set C) : MeetLaws (Reachable K) where
  op := inf K
  assoc V W H := by apply Subtype.ext; exact Set.inter_assoc _ _ _
  comm V W := by apply Subtype.ext; exact Set.inter_comm _ _
  idem V := by apply Subtype.ext; exact Set.inter_self _

instance (K : P -> Set C) : SemilatticeInf (Reachable K) := (laws K).order
instance (K : P -> Set C) : OrderTop (Reachable K) where
  top := ⟨Set.univ, [], rfl⟩
  le_top V := by
    change inf K V ⟨Set.univ, [], rfl⟩ = V
    apply Subtype.ext
    exact Set.inter_univ _

@[simp] theorem val_inf (K : P -> Set C) (V W : Reachable K) :
    (V ⊓ W).val = V.val ∩ W.val := rfl
@[simp] theorem val_top (K : P -> Set C) :
    (⊤ : Reachable K).val = Set.univ := rfl

def generator (K : P -> Set C) (p : P) : Reachable K :=
  ⟨K p, [p], by simp [version]⟩

/-- Inference order is the usual inclusion order on survivor sets. -/
theorem le_iff_subset (K : P -> Set C) (V W : Reachable K) :
    V ≤ W ↔ V.val ⊆ W.val := by
  change inf K V W = V ↔ _
  constructor
  · intro h c hc
    have hh : V.val ∩ W.val = V.val := congrArg Subtype.val h
    have : c ∈ V.val ∩ W.val := by rw [hh]; exact hc
    exact this.2
  · intro h
    apply Subtype.ext
    exact Set.inter_eq_left.mpr h

end VersionSpace

namespace Inference
universe u v w z
variable {R : Type u} [SemilatticeInf R] [OrderTop R]
variable {P : Type v} {Y : Type w}

def eval (g : P -> R) : List P -> R
  | [] => ⊤
  | p :: s => g p ⊓ eval g s

@[simp] theorem eval_nil (g : P -> R) : eval g [] = ⊤ := rfl
@[simp] theorem eval_cons (g : P -> R) (p : P) (s : List P) :
    eval g (p :: s) = g p ⊓ eval g s := rfl

@[simp] theorem eval_append (g : P -> R) (s t : List P) :
    eval g (s ++ t) = eval g s ⊓ eval g t := by
  induction s with
  | nil => simp [eval]
  | cons p s ih => simp [eval, ih, inf_assoc]

@[simp] theorem eval_snoc (g : P -> R) (s : List P) (p : P) :
    eval g (s ++ [p]) = eval g s ⊓ g p := by simp [eval]

def Generated (g : P -> R) : Prop := ∀ r, ∃ s, eval g s = r

/-- Agreement after every possible additional meet. -/
def Eqv (rho : R -> Y) (r s : R) : Prop :=
  ∀ h, rho (r ⊓ h) = rho (s ⊓ h)

def setoid (rho : R -> Y) : Setoid R where
  r := Eqv rho
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro r h; rfl
    · intro r s hrs h; exact (hrs h).symm
    · intro r s t hrs hst h; exact (hrs h).trans (hst h)

omit [OrderTop R] in
theorem eqv_inf_right (rho : R -> Y) {r s : R}
    (hrs : Eqv rho r s) (w : R) : Eqv rho (r ⊓ w) (s ⊓ w) := by
  intro h
  simpa only [inf_assoc] using hrs (w ⊓ h)

omit [OrderTop R] in
theorem eqv_inf (rho : R -> Y) {r r' s s' : R}
    (hr : Eqv rho r r') (hs : Eqv rho s s') :
    Eqv rho (r ⊓ s) (r' ⊓ s') := by
  intro h
  calc
    rho ((r ⊓ s) ⊓ h) = rho ((r' ⊓ s) ⊓ h) :=
      eqv_inf_right rho hr s h
    _ = rho ((s ⊓ r') ⊓ h) := by rw [inf_comm r' s]
    _ = rho ((s' ⊓ r') ⊓ h) := eqv_inf_right rho hs r' h
    _ = rho ((r' ⊓ s') ⊓ h) := by rw [inf_comm s' r']

def State (rho : R -> Y) := Quotient (setoid rho)

instance (rho : R -> Y) [Finite R] : Finite (State rho) :=
  inferInstanceAs (Finite (Quotient (setoid rho)))

noncomputable instance (rho : R -> Y) [Fintype R] : Fintype (State rho) :=
  Fintype.ofFinite _

def mk (rho : R -> Y) (r : R) : State rho := Quotient.mk (setoid rho) r

omit [OrderTop R] in
@[simp] theorem mk_eq_mk (rho : R -> Y) (r s : R) :
    mk rho r = mk rho s ↔ Eqv rho r s := Quotient.eq

def qInf (rho : R -> Y) (x y : State rho) : State rho :=
  Quotient.liftOn x
    (fun r => Quotient.liftOn y (fun s => mk rho (r ⊓ s))
      (by intro s s' hs; exact Quotient.sound (eqv_inf rho (fun _ => rfl) hs)))
    (by
      intro r r' hr
      refine Quotient.inductionOn y ?_
      intro s
      exact Quotient.sound (eqv_inf rho hr (fun _ => rfl)))

omit [OrderTop R] in
@[simp] theorem qInf_mk (rho : R -> Y) (r s : R) :
    qInf rho (mk rho r) (mk rho s) = mk rho (r ⊓ s) := rfl

def qLaws (rho : R -> Y) : MeetLaws (State rho) where
  op := qInf rho
  assoc := by
    intro x y z
    refine Quotient.inductionOn x ?_
    intro r
    refine Quotient.inductionOn y ?_
    intro s
    refine Quotient.inductionOn z ?_
    intro t
    exact congrArg (mk rho) (inf_assoc r s t)
  comm := by
    intro x y
    refine Quotient.inductionOn x ?_
    intro r
    refine Quotient.inductionOn y ?_
    intro s
    exact congrArg (mk rho) (inf_comm r s)
  idem := by
    intro x
    refine Quotient.inductionOn x ?_
    intro r
    exact congrArg (mk rho) (inf_idem r)

instance (rho : R -> Y) : SemilatticeInf (State rho) := (qLaws rho).order
instance (rho : R -> Y) : OrderTop (State rho) where
  top := mk rho ⊤
  le_top x := by
    refine Quotient.inductionOn x ?_
    intro r
    change mk rho (r ⊓ ⊤) = mk rho r
    simp

omit [OrderTop R] in
@[simp] theorem mk_inf (rho : R -> Y) (r s : R) :
    mk rho (r ⊓ s) = mk rho r ⊓ mk rho s := rfl
@[simp] theorem mk_top (rho : R -> Y) : mk rho ⊤ = ⊤ := rfl

def projection (rho : R -> Y) : MeetHom R (State rho) where
  toFun := mk rho
  map_inf _ _ := rfl
  map_top := rfl

def read (rho : R -> Y) : State rho -> Y :=
  Quotient.lift rho (by
    intro r s h
    simpa using h (⊤ : R))

@[simp] theorem read_mk (rho : R -> Y) (r : R) : read rho (mk rho r) = rho r := rfl

theorem state_separated (rho : R -> Y) {q r : State rho}
    (h : ∀ t, read rho (q ⊓ t) = read rho (r ⊓ t)) : q = r := by
  revert h
  refine Quotient.inductionOn q ?_
  intro a
  refine Quotient.inductionOn r ?_
  intro b h
  apply Quotient.sound
  intro c
  exact h (mk rho c)

/-- A finite distinguishing continuation exists for distinct quotient states. -/
theorem distinguishing_continuation (rho : R -> Y) (g : P -> R)
    (hg : Generated g) {q r : State rho} (hqr : q ≠ r) :
    ∃ s, read rho (q ⊓ mk rho (eval g s)) ≠
      read rho (r ⊓ mk rho (eval g s)) := by
  by_contra! h
  apply hqr
  apply state_separated rho
  intro t
  refine Quotient.inductionOn t ?_
  intro a
  obtain ⟨s, hs⟩ := hg a
  simpa [hs, mk] using h s

variable {Q : Type z}

/-- Correctness on all histories. This is a semantic specification, not a
finitary testing assumption. -/
def Correct (A : Moore Q P Y) (g : P -> R) (rho : R -> Y) : Prop :=
  ∀ s, A.out (A.run s) = rho (eval g s)

theorem same_machine_state_eqv (A : Moore Q P Y) (g : P -> R)
    (rho : R -> Y) (hg : Generated g) (hc : Correct A g rho)
    {s t : List P} (hst : A.run s = A.run t) : Eqv rho (eval g s) (eval g t) := by
  intro h
  obtain ⟨u, hu⟩ := hg h
  rw [<- hu, <- eval_append, <- eval_append, <- hc, <- hc]
  simp only [Moore.run_append, hst]

/-- The interpretation is extracted from a reaching word. Independence of
that choice is proved below, rather than included as an assumption. -/
def delta (A : Moore Q P Y) (g : P -> R) (rho : R -> Y)
    (q : A.Reach) : State rho :=
  mk rho (eval g (Classical.choose q.property))

theorem delta_rRun (A : Moore Q P Y) (g : P -> R) (rho : R -> Y)
    (hg : Generated g) (hc : Correct A g rho) (s : List P) :
    delta A g rho (A.rRun s) = mk rho (eval g s) := by
  apply Quotient.sound
  apply same_machine_state_eqv A g rho hg hc
  exact Classical.choose_spec (A.rRun s).property

theorem delta_initial (A : Moore Q P Y) (g : P -> R) (rho : R -> Y)
    (hg : Generated g) (hc : Correct A g rho) :
    delta A g rho A.rInitial = ⊤ := by
  simpa using delta_rRun A g rho hg hc []

theorem delta_step (A : Moore Q P Y) (g : P -> R) (rho : R -> Y)
    (hg : Generated g) (hc : Correct A g rho) (q : A.Reach) (p : P) :
    delta A g rho (A.rStep q p) = delta A g rho q ⊓ mk rho (g p) := by
  obtain ⟨s, hs⟩ := q.property
  have hq : q = A.rRun s := Subtype.ext hs.symm
  rw [hq, <- Moore.rRun_snoc, delta_rRun A g rho hg hc,
    delta_rRun A g rho hg hc, eval_snoc, mk_inf]

theorem delta_read (A : Moore Q P Y) (g : P -> R) (rho : R -> Y)
    (hc : Correct A g rho) (q : A.Reach) :
    A.out q.val = read rho (delta A g rho q) := by
  have hq := Classical.choose_spec q.property
  change A.out q.val = rho (eval g (Classical.choose q.property))
  rw [<- hc, hq]

theorem delta_surjective (A : Moore Q P Y) (g : P -> R) (rho : R -> Y)
    (hg : Generated g) (hc : Correct A g rho) : Surjective (delta A g rho) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro r
  obtain ⟨s, hs⟩ := hg r
  exact ⟨A.rRun s, by rw [delta_rRun A g rho hg hc, hs]; rfl⟩

theorem delta_unique (A : Moore Q P Y) (g : P -> R) (rho : R -> Y)
    (hg : Generated g) (hc : Correct A g rho)
    (f : A.Reach -> State rho) (h0 : f A.rInitial = ⊤)
    (hstep : ∀ q p, f (A.rStep q p) = f q ⊓ mk rho (g p)) :
    f = delta A g rho := by
  have hrun : ∀ s, f (A.rRun s) = mk rho (eval g s) := by
    intro s
    induction s using List.reverseRecOn with
    | nil => simpa using h0
    | @append_singleton s p ih =>
      rw [Moore.rRun_snoc, hstep, ih, eval_snoc, mk_inf]
  funext q
  obtain ⟨s, hs⟩ := q.property
  have hq : q = A.rRun s := Subtype.ext hs.symm
  rw [hq, hrun, delta_rRun A g rho hg hc]

theorem cardinal_lower_bound [Fintype R] [Fintype Q]
    (A : Moore Q P Y) (g : P -> R) (rho : R -> Y)
    (hg : Generated g) (hc : Correct A g rho) :
    Fintype.card (State rho) ≤ Fintype.card Q := by
  calc
    Fintype.card (State rho) ≤ Fintype.card A.Reach :=
      Fintype.card_le_of_surjective _ (delta_surjective A g rho hg hc)
    _ ≤ Fintype.card Q := Fintype.card_le_of_injective Subtype.val Subtype.val_injective

/-- The matching implementation. -/
def canonicalMachine (g : P -> R) (rho : R -> Y) : Moore (State rho) P Y where
  initial := ⊤
  step q p := q ⊓ mk rho (g p)
  out := read rho

theorem canonical_runFrom (g : P -> R) (rho : R -> Y)
    (q : State rho) (s : List P) :
    (canonicalMachine g rho).runFrom q s = q ⊓ mk rho (eval g s) := by
  induction s generalizing q with
  | nil => simp [Moore.runFrom, eval]
  | cons p s ih =>
    show (canonicalMachine g rho).runFrom (q ⊓ mk rho (g p)) s = _
    rw [ih, eval_cons, mk_inf]
    exact inf_assoc _ _ _

@[simp] theorem canonical_run (g : P -> R) (rho : R -> Y) (s : List P) :
    (canonicalMachine g rho).run s = mk rho (eval g s) := by
  have h := canonical_runFrom g rho ⊤ s
  rw [top_inf_eq] at h
  exact h

theorem canonical_correct (g : P -> R) (rho : R -> Y) :
    Correct (canonicalMachine g rho) g rho := by
  intro s
  show read rho ((canonicalMachine g rho).run s) = rho (eval g s)
  rw [canonical_run]
  exact read_mk rho (eval g s)

/-- A locally checkable simulation certificate proves all-horizon correctness. -/
theorem correctness_of_certificate (A : Moore Q P Y) (g : P -> R)
    (rho : R -> Y) (f : Q -> State rho)
    (h0 : f A.initial = ⊤)
    (hs : ∀ q p, f (A.step q p) = f q ⊓ mk rho (g p))
    (ho : ∀ q, A.out q = read rho (f q)) : Correct A g rho := by
  intro s
  have h := Moore.simulation_outputs A (canonicalMachine g rho) f h0 hs ho s
  rw [show ((canonicalMachine g rho).run s) = mk rho (eval g s) from
    canonical_run g rho s] at h
  exact h

omit [OrderTop R] in
/-- Constant reports erase every semantic distinction, including future ones. -/
theorem constant_readout_eqv (y : Y) (r s : R) : Eqv (fun _ : R => y) r s := by
  intro h; rfl

omit [OrderTop R] in
theorem constant_state_subsingleton (y : Y) : Subsingleton (State (fun _ : R => y)) := by
  refine ⟨?_⟩
  intro q r
  refine Quotient.inductionOn q ?_
  intro a
  refine Quotient.inductionOn r ?_
  intro b
  exact Quotient.sound (constant_readout_eqv y a b)

/-- Injective readout means no quotienting beyond equality. -/
theorem eqv_iff_eq_of_injective (rho : R -> Y) (hr : Injective rho) (r s : R) :
    Eqv rho r s ↔ r = s := by
  constructor
  · intro h; apply hr; simpa using h (⊤ : R)
  · intro h; subst s; intro w; rfl

omit [OrderTop R] in
/-- Richer reports preserve at least all distinctions of a coarsening. -/
theorem eqv_coarsen {Y' : Type*} (rho : R -> Y) (f : Y -> Y')
    {r s : R} (h : Eqv rho r s) : Eqv (f ∘ rho) r s := by
  intro w; exact congrArg f (h w)

end Inference

namespace VersionSpace
variable {C : Type*} {P : Type*}

@[simp] theorem eval_generator (K : P -> Set C) (s : List P) :
    (Inference.eval (generator K) s).val = version K s := by
  induction s with
  | nil => rfl
  | cons p s ih => simp [Inference.eval, generator, version, ih]

theorem generated (K : P -> Set C) : Inference.Generated (generator K) := by
  intro V
  obtain ⟨s, hs⟩ := V.property
  refine ⟨s, ?_⟩
  apply Subtype.ext
  simpa using (eval_generator K s).trans hs

end VersionSpace
end NeuralArtifacts

end -- noncomputable section

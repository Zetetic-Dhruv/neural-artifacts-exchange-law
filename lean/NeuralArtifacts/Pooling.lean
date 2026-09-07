import NeuralArtifacts.Inference
import NeuralArtifacts.FiniteMonoid

/-!
# 4. From an operational pooled artifact to the exchange inequality

A channel state is the product of its observation embeddings. Different
histories are allowed to have different pooled states even when they have
the same semantic state. The reachable image, rather than an assumed
minimal implementation, is the source of the canonical homomorphism.
-/

noncomputable section
open Classical Function
open scoped BigOperators
namespace NeuralArtifacts
namespace Pooling
universe u v w z
variable {P : Type u} {Y : Type v} {M : Type w} [CommMonoid M]

def aggregate (e : P -> M) (s : List P) : M := (s.map e).prod

@[simp] theorem aggregate_nil (e : P -> M) : aggregate e [] = 1 := rfl
@[simp] theorem aggregate_cons (e : P -> M) (p : P) (s : List P) :
    aggregate e (p :: s) = e p * aggregate e s := rfl
@[simp] theorem aggregate_append (e : P -> M) (s t : List P) :
    aggregate e (s ++ t) = aggregate e s * aggregate e t := by
  simp [aggregate]

def machine (e : P -> M) (out : M -> Y) : Moore M P Y where
  initial := 1
  step m p := m * e p
  out := out

theorem runFrom_eq (e : P -> M) (out : M -> Y) (m : M) (s : List P) :
    (machine e out).runFrom m s = m * aggregate e s := by
  induction s generalizing m with
  | nil => simp [Moore.runFrom]
  | cons p s ih =>
    simpa only [Moore.runFrom_cons, machine, aggregate_cons, mul_assoc] using ih (m * e p)

@[simp] theorem machine_out (e : P -> M) (out : M -> Y) :
    (machine e out).out = out := rfl

@[simp] theorem run_eq (e : P -> M) (out : M -> Y) (s : List P) :
    (machine e out).run s = aggregate e s := by
  simpa [Moore.run, machine] using runFrom_eq e out 1 s

def reachable (e : P -> M) : Submonoid M where
  carrier := {m | ∃ s, aggregate e s = m}
  one_mem' := ⟨[], rfl⟩
  mul_mem' := by
    intro m n hm hn
    obtain ⟨s, hs⟩ := hm
    obtain ⟨t, ht⟩ := hn
    exact ⟨s ++ t, by simp [hs, ht]⟩

def reached (e : P -> M) (s : List P) : reachable e :=
  ⟨aggregate e s, s, rfl⟩

@[simp] theorem reached_nil (e : P -> M) : reached e [] = 1 := rfl
@[simp] theorem reached_append (e : P -> M) (s t : List P) :
    reached e (s ++ t) = reached e s * reached e t := by
  apply Subtype.ext; simp [reached]

variable {R : Type z} [SemilatticeInf R] [OrderTop R]

/-- State semantics from any reaching word. -/
def interpret (e : P -> M) (g : P -> R) (rho : R -> Y)
    (m : reachable e) : Inference.State rho :=
  Inference.mk rho (Inference.eval g (Classical.choose m.property))

theorem interpret_reached (e : P -> M) (out : M -> Y)
    (g : P -> R) (rho : R -> Y) (hg : Inference.Generated g)
    (hc : ∀ s, out (aggregate e s) = rho (Inference.eval g s)) (s : List P) :
    interpret e g rho (reached e s) = Inference.mk rho (Inference.eval g s) := by
  apply Quotient.sound
  apply Inference.same_machine_state_eqv (machine e out) g rho hg
  · intro t; simpa using hc t
  · simp only [run_eq]
    exact Classical.choose_spec (reached e s).property

def interpretationHom (e : P -> M) (out : M -> Y)
    (g : P -> R) (rho : R -> Y) (hg : Inference.Generated g)
    (hc : ∀ s, out (aggregate e s) = rho (Inference.eval g s)) :
    FiniteMonoid.ToMeet (reachable e) (Inference.State rho) where
  toFun := interpret e g rho
  map_one := by simpa using interpret_reached e out g rho hg hc []
  map_mul m n := by
    obtain ⟨s, hs⟩ := m.property
    obtain ⟨t, ht⟩ := n.property
    have hm : m = reached e s := Subtype.ext hs.symm
    have hn : n = reached e t := Subtype.ext ht.symm
    rw [hm, hn, <- reached_append, interpret_reached e out g rho hg hc,
      interpret_reached e out g rho hg hc, interpret_reached e out g rho hg hc,
      Inference.eval_append, Inference.mk_inf]

theorem interpretation_surjective (e : P -> M) (out : M -> Y)
    (g : P -> R) (rho : R -> Y) (hg : Inference.Generated g)
    (hc : ∀ s, out (aggregate e s) = rho (Inference.eval g s)) :
    Surjective (interpretationHom e out g rho hg hc) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro r
  obtain ⟨s, hs⟩ := hg r
  refine ⟨reached e s, ?_⟩
  change interpret e g rho (reached e s) = Inference.mk rho r
  rw [interpret_reached e out g rho hg hc, hs]

section Independent
variable {J : Type*} [Fintype J]
variable {Channels : J -> Type*}
variable [∀ j, CommMonoid (Channels j)] [∀ j, Fintype (Channels j)]
variable [Fintype R]

/-- Theorem 3: the stronger idempotent-height inequality. -/
theorem independent_height (e : P -> ∀ j, Channels j)
    (out : (∀ j, Channels j) -> Y) (g : P -> R) (rho : R -> Y)
    (hg : Inference.Generated g)
    (hc : ∀ s, out (aggregate e s) = rho (Inference.eval g s)) :
    FiniteOrder.height (Inference.State rho) - 1 ≤
      ∑ j, (FiniteOrder.height (FiniteMonoid.Idem (Channels j)) - 1) := by
  exact FiniteMonoid.exchange_height (reachable e)
    (interpretationHom e out g rho hg hc)
    (interpretation_surjective e out g rho hg hc)

/-- Theorem 3: the channel-cardinality consequence. -/
theorem independent_card_height (e : P -> ∀ j, Channels j)
    (out : (∀ j, Channels j) -> Y) (g : P -> R) (rho : R -> Y)
    (hg : Inference.Generated g)
    (hc : ∀ s, out (aggregate e s) = rho (Inference.eval g s)) :
    FiniteOrder.height (Inference.State rho) - 1 ≤
      ∑ j, (Fintype.card (Channels j) - 1) := by
  exact FiniteMonoid.exchange_card (reachable e)
    (interpretationHom e out g rho hg hc)
    (interpretation_surjective e out g rho hg hc)

theorem independent_state_card (e : P -> ∀ j, Channels j)
    (out : (∀ j, Channels j) -> Y) (g : P -> R) (rho : R -> Y)
    (hg : Inference.Generated g)
    (hc : ∀ s, out (aggregate e s) = rho (Inference.eval g s)) :
    Fintype.card (Inference.State rho) ≤ ∏ j, Fintype.card (Channels j) := by
  have h := Inference.cardinal_lower_bound (machine e out) g rho hg
    (by intro s; simpa using hc s)
  simpa [Fintype.card_pi] using h

/-- When the readout is injective, the whole meet state survives minimization. -/
theorem independent_height_of_injective (e : P -> ∀ j, Channels j)
    (out : (∀ j, Channels j) -> Y) (g : P -> R) (rho : R -> Y)
    (hg : Inference.Generated g) (hr : Injective rho)
    (hc : ∀ s, out (aggregate e s) = rho (Inference.eval g s)) :
    FiniteOrder.height R - 1 ≤ ∑ j, (Fintype.card (Channels j) - 1) := by
  have hi : Injective (Inference.mk rho) := by
    intro r s h
    exact (Inference.eqv_iff_eq_of_injective rho hr r s).mp
      ((Inference.mk_eq_mk rho r s).mp h)
  have hh := FiniteOrder.height_le_of_injective_monotone
    (Inference.mk rho) hi (Inference.projection rho).monotone
  have hb := independent_card_height e out g rho hg hc
  omega
end Independent
end Pooling
end NeuralArtifacts

end -- noncomputable section

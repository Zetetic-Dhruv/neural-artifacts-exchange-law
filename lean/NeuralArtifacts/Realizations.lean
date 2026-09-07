import NeuralArtifacts.OperationalMeet
import NeuralArtifacts.CutExchange
import NeuralArtifacts.CoupledWidth
import NeuralArtifacts.ResidualChain

/-!
# 26. Concrete model stores and exact numerical corollaries

These constructions show that the exchange laws are realized by genuine
candidate/observation tables. They are not conditional claims about a
hypothetical semilattice that no inference problem can realize.
-/
noncomputable section
open Classical Function
open scoped BigOperators
namespace NeuralArtifacts.Realizations

variable {R : Type*} [Fintype R] [SemilatticeInf R] [OrderTop R]

/-- Binary evaluators; each positive observation requests an order bound. -/
def evaluates (candidate observation : R) : Bool := decide (candidate ≤ observation)

def consistent (observation : R) : Set R := {c | evaluates c observation = true}

omit [Fintype R] [OrderTop R] in
theorem consistent_eq_ideal (p : R) : consistent p = OperationalMeet.ideal p := by
  ext c
  simp [consistent, evaluates, OperationalMeet.ideal]

omit [Fintype R] in
theorem realized_history (s : List R) :
    VersionSpace.version consistent s = OperationalMeet.ideal (Inference.eval id s) := by
  have hfun : (consistent : R -> Set R) = fun p => OperationalMeet.ideal p := by
    funext p
    exact consistent_eq_ideal p
  rw [hfun]
  exact OperationalMeet.principal_ideal_realization id s

omit [Fintype R] in
/-- Every state is realized by a single observation, including the top state. -/
theorem generated_identity : Inference.Generated (id : R -> R) := by
  intro r
  exact ⟨[r], by simp [Inference.eval]⟩

def realizedVersionEquiv : VersionSpace.Reachable (consistent (R := R)) ≃ R where
  toFun v := Classical.choose (show ∃ r, OperationalMeet.ideal r = v.val from by
    obtain ⟨s, hs⟩ := v.property
    exact ⟨Inference.eval id s, (realized_history s).symm.trans hs⟩)
  invFun r := ⟨OperationalMeet.ideal r, [r], by simpa [Inference.eval] using realized_history [r]⟩
  left_inv v := by
    apply Subtype.ext
    exact Classical.choose_spec (show ∃ r, OperationalMeet.ideal r = v.val from by
      obtain ⟨s, hs⟩ := v.property
      exact ⟨Inference.eval id s, (realized_history s).symm.trans hs⟩)
  right_inv r := by
    apply OperationalMeet.ideal_injective
    exact Classical.choose_spec
      (⟨r, rfl⟩ : ∃ q : R, OperationalMeet.ideal q = OperationalMeet.ideal r)

theorem reachable_count :
    Fintype.card (VersionSpace.Reachable (consistent (R := R))) = Fintype.card R :=
  Fintype.card_congr realizedVersionEquiv

theorem chain_store_count (n : Nat) :
    Fintype.card (VersionSpace.Reachable (consistent (R := Fin (n + 1)))) = n + 1 := by
  rw [reachable_count, Fintype.card_fin]

theorem boolean_store_count (k : Nat) :
    Fintype.card (VersionSpace.Reachable (consistent (R := Fin k -> Bool))) = 2 ^ k := by
  rw [reachable_count]
  simp

/-- The precision parameter b counts values. p bits means b=2^p. -/
theorem bit_precision_bound (states W p : Nat)
    (h : states ≤ (2 ^ p) ^ W) : states ≤ 2 ^ (p * W) := by
  simpa [pow_mul] using h

/-- The chain residual lower bound also holds for an arbitrary independent
finite commutative monoid, not just a normalized quotient of the chain. -/
theorem arbitrary_residual_lower {n : Nat} (a : Congruence.Rel (Fin (n + 1)))
    {M : Type*} [Fintype M] [CommMonoid M]
    (embed : Fin (n + 1) -> M) (read : Congruence.Quot a -> M -> Fin (n + 1))
    (correct : ∀ s : List (Fin (n + 1)),
      read (Congruence.proj a (Inference.eval id s)) ((s.map embed).prod) = Inference.eval id s) :
    n + 2 - Fintype.card (Congruence.Quot a) ≤ Fintype.card M := by
  let Channels : Bool -> Type _ :=
    fun b => if b then M else ULift (MeetCarrier (Congruence.Quot a))
  letI : ∀ b, Fintype (Channels b) := by intro b; cases b <;> dsimp [Channels] <;> infer_instance
  letI : ∀ b, CommMonoid (Channels b) := by intro b; cases b <;> dsimp [Channels] <;> infer_instance
  let e : Fin (n + 1) -> (b : Bool) -> Channels b := fun r b => by
    cases b
    · exact ULift.up ⟨Congruence.proj a r⟩
    · exact embed r
  let out : ((b : Bool) -> Channels b) -> Fin (n + 1) :=
    fun v => read (v false).down.val (v true)
  have hleft (s : List (Fin (n + 1))) :
      ((Pooling.aggregate e s) false).down.val
        = Congruence.proj a (Inference.eval id s) := by
    induction s with
    | nil => rfl
    | cons r s ih =>
      have hef : ((e r) false).down.val = Congruence.proj a r := rfl
      have hstep : ((Pooling.aggregate e (r :: s)) false).down.val
          = ((e r false).down.val) ⊓ (((Pooling.aggregate e s) false).down.val) := rfl
      have hres : Congruence.proj a (Inference.eval id (r :: s))
          = Congruence.proj a r ⊓ Congruence.proj a (Inference.eval id s) := rfl
      rw [hstep, hres, ih, hef]
  have hright (s : List (Fin (n + 1))) : (Pooling.aggregate e s) true = (s.map embed).prod := by
    induction s with
    | nil => rfl
    | cons r s ih =>
      have het : e r true = embed r := rfl
      have hstep : (Pooling.aggregate e (r :: s)) true
          = (e r true) * ((Pooling.aggregate e s) true) := rfl
      have hres : ((r :: s).map embed).prod = embed r * ((s.map embed).prod) := rfl
      rw [hstep, hres, ih, het]
      rfl
  have hc (s : List (Fin (n + 1))) : out (Pooling.aggregate e s) = Inference.eval id s := by
    change read ((Pooling.aggregate e s) false).down.val ((Pooling.aggregate e s) true) = _
    rw [hleft, hright]
    exact correct s
  have hh := Pooling.independent_height_of_injective e out id id
    (generated_identity (R := Fin (n + 1))) (fun _ _ h => h) hc
  simp only [FiniteOrder.height_fin, Fintype.sum_bool, Channels, Bool.false_eq_true,
    if_false, if_true, Fintype.card_ulift, MeetCarrier.card] at hh
  have ha : 0 < Fintype.card (Congruence.Quot a) := Fintype.card_pos_iff.mpr inferInstance
  have hm : 0 < Fintype.card M := Fintype.card_pos_iff.mpr inferInstance
  omega

end NeuralArtifacts.Realizations

end -- noncomputable section

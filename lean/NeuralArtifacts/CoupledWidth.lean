import NeuralArtifacts.CutExchange

/-!
# 6. Coupled width and the exponential separation

The independent and coupled interfaces differ in the operation, not in a
counting convention. Here the monoid operation is transported to the whole
`W`-coordinate alphabet. Unused codes lie below the reachable chain, so the
reachable top remains the actual monoid identity.
-/

noncomputable section
open Classical Function
open scoped BigOperators
namespace NeuralArtifacts
namespace CoupledWidth

/-- Transport a monoid operation along an actual equivalence of carriers. -/
@[reducible] def transportCommMonoid {A B : Type*} [CommMonoid B] (e : A ≃ B) :
    CommMonoid A where
  one := e.symm 1
  mul x y := e.symm (e x * e y)
  mul_assoc x y z := by
    show e.symm (e (e.symm (e x * e y)) * e z)
      = e.symm (e x * e (e.symm (e y * e z)))
    simp only [Equiv.apply_symm_apply, mul_assoc]
  one_mul x := by
    show e.symm (e (e.symm 1) * e x) = x
    simp
  mul_one x := by
    show e.symm (e x * e (e.symm 1)) = x
    simp
  mul_comm x y := by
    show e.symm (e x * e y) = e.symm (e y * e x)
    rw [mul_comm]

/-- The complete coordinate box admits an arbitrary coupled pooling operation. -/
def Feasible (n b W : Nat) : Prop :=
  ∃ cm : CommMonoid (Fin W -> Fin b),
    letI := cm
    ∃ (e : Fin (n + 1) -> (Fin W -> Fin b))
      (out : (Fin W -> Fin b) -> Fin (n + 1)),
      ∀ s, out (Pooling.aggregate e s) = Inference.eval id s

/-- Every selected code is a high rank; unused ranks lie below every selected code. -/
def shiftCode {n K : Nat} (hK : n + 1 ≤ K) (r : Fin (n + 1)) : Fin K :=
  ⟨K - (n + 1) + r.val, by have := r.isLt; omega⟩

theorem shiftCode_injective {n K : Nat} (hK : n + 1 ≤ K) :
    Injective (shiftCode hK) := by
  intro r s h
  apply Fin.ext
  have hh := congrArg Fin.val h
  dsimp [shiftCode] at hh
  omega

theorem shiftCode_monotone {n K : Nat} (hK : n + 1 ≤ K) :
    Monotone (shiftCode hK) := by
  intro r s hrs
  change K - (n + 1) + r.val ≤ K - (n + 1) + s.val
  omega

theorem shiftCode_inf {n K : Nat} (hK : n + 1 ≤ K) (r s : Fin (n + 1)) :
    shiftCode hK (r ⊓ s) = shiftCode hK r ⊓ shiftCode hK s := by
  rcases le_total r s with hrs | hsr
  · rw [inf_eq_left.mpr hrs, inf_eq_left.mpr (shiftCode_monotone hK hrs)]
  · rw [inf_eq_right.mpr hsr, inf_eq_right.mpr (shiftCode_monotone hK hsr)]

theorem shiftCode_top {n K : Nat} [NeZero K] (hK : n + 1 ≤ K) :
    shiftCode hK (⊤ : Fin (n + 1)) = ⊤ := by
  apply Fin.ext
  change K - (n + 1) + n = K - 1
  omega

/-- Corollary 4, without real-valued rounding conventions. -/
theorem feasible_iff (n b W : Nat) :
    Feasible n b W ↔ n + 1 ≤ b ^ W := by
  constructor
  · rintro ⟨cm, e, out, hc⟩
    letI := cm
    have hi : Injective e := by
      intro r s hrs
      have hr := hc [r]
      have hs := hc [s]
      simp [Pooling.aggregate, Inference.eval] at hr hs
      rw [hrs] at hr
      exact hr.symm.trans hs
    have hcard := Fintype.card_le_of_injective e hi
    simpa [Fintype.card_fun, Fintype.card_fin] using hcard
  · intro hK
    let K := b ^ W
    have hpos : 0 < K := by dsimp [K]; omega
    letI : NeZero K := ⟨ne_of_gt hpos⟩
    let Digits := Fin W -> Fin b
    have hcard : Fintype.card Digits = K := by
      simp [Digits, K, Fintype.card_fin]
    let ebox : Digits ≃ MeetCarrier (Fin K) :=
      (Fintype.equivFin Digits).trans
        ((Equiv.cast (congrArg Fin hcard)).trans MeetCarrier.equiv.symm)
    let cm : CommMonoid Digits := transportCommMonoid ebox
    letI := cm
    let code : Fin (n + 1) -> Digits :=
      fun r => ebox.symm ⟨shiftCode hK r⟩
    have hi : Injective code := by
      intro r s h
      apply shiftCode_injective hK
      have hh := congrArg (fun x => (ebox x).val) h
      simpa [code] using hh
    refine ⟨cm, code, CutExchange.decode code, ?_⟩
    intro s
    refine CutExchange.decoded_aggregate code hi ?_ ?_ s
    · show ebox.symm ⟨shiftCode hK ⊤⟩ = ebox.symm ⟨⊤⟩
      rw [shiftCode_top hK]
    · intro r t
      show ebox.symm ⟨shiftCode hK (r ⊓ t)⟩ =
        ebox.symm (ebox (ebox.symm ⟨shiftCode hK r⟩) *
          ebox (ebox.symm ⟨shiftCode hK t⟩))
      simp only [Equiv.apply_symm_apply]
      congr 1
      apply MeetCarrier.ext
      exact shiftCode_inf hK r t

/-- Elementary exponent monotonicity, proved here to keep the integer-width
formulas independent of the real-logarithm API. -/
theorem one_le_pow (b : Nat) (hb : 1 ≤ b) (k : Nat) : 1 ≤ b ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; nlinarith

theorem pow_mono {b u v : Nat} (hb : 1 ≤ b) (huv : u ≤ v) : b ^ u ≤ b ^ v := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le huv
  rw [pow_add]
  calc b ^ u = b ^ u * 1 := (mul_one _).symm
    _ ≤ b ^ u * b ^ k := Nat.mul_le_mul_left _ (one_le_pow b hb k)

theorem pow_strict {b u v : Nat} (hb : 2 ≤ b) (huv : u < v) : b ^ u < b ^ v := by
  have huv' : u + 1 ≤ v := Nat.succ_le_of_lt huv
  have hm := pow_mono (b := b) (by omega) huv'
  have hp := one_le_pow b (by omega) u
  rw [pow_succ] at hm
  nlinarith

theorem pow_le_iff_exponent_le {b u v : Nat} (hb : 2 ≤ b) :
    b ^ u ≤ b ^ v ↔ u ≤ v := by
  constructor
  · intro h
    by_contra hn
    exact (not_le_of_gt (pow_strict hb (lt_of_not_ge hn))) h
  · exact pow_mono (by omega)

theorem exponent_exists (N b : Nat) (hb : 2 ≤ b) : ∃ W, N ≤ b ^ W := by
  refine ⟨N, ?_⟩
  induction N with
  | zero => simp
  | succ N ih =>
    have hp := one_le_pow b (by omega) N
    rw [pow_succ]
    nlinarith

/-- This is the exact integer meaning of `ceil(log_b N)`, including `N=1`. -/
def leastWidth (N b : Nat) (hb : 2 ≤ b) : Nat :=
  Nat.find (exponent_exists N b hb)

theorem leastWidth_le_iff (N b W : Nat) (hb : 2 ≤ b) :
    leastWidth N b hb ≤ W ↔ N ≤ b ^ W := by
  constructor
  · intro h
    have hs := Nat.find_spec (exponent_exists N b hb)
    exact hs.trans (pow_mono (by omega) h)
  · intro h
    exact Nat.find_min' (exponent_exists N b hb) h

theorem coupled_width_minimum (n b W : Nat) (hb : 2 ≤ b) :
    Feasible n b W ↔ leastWidth (n + 1) b hb ≤ W := by
  rw [feasible_iff, leastWidth_le_iff]

/-- The exact exponential separation, stated as feasibility equivalences. -/
theorem independent_binary_power (k W : Nat) :
    CutExchange.Feasible (J := Fin W) (2 ^ k - 1) (fun _ => 2) ↔
      2 ^ k - 1 ≤ W := by
  simpa using CutExchange.uniform_feasible_iff (2 ^ k - 1) 2 W (by omega)

theorem coupled_binary_power (k W : Nat) :
    Feasible (2 ^ k - 1) 2 W ↔ k ≤ W := by
  have hp : 1 ≤ 2 ^ k := one_le_pow 2 (by omega) k
  rw [feasible_iff, Nat.sub_add_cancel hp]
  exact pow_le_iff_exponent_le (by omega)

end CoupledWidth
end NeuralArtifacts

end -- noncomputable section

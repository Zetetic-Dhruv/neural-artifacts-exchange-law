import NeuralArtifacts.CoupledWidth

/-!
# 29. Width for an arbitrary inference state

The coupled construction of the chain corollary extends to every finite
meet-semilattice with top: the unused codes of a `W`-coordinate `b`-value
memory are attached below the inference state as an absorbing chain, so a
coupled realization exists exactly when the state fits in `b ^ W` codes. An
independent pooling of `W` channels of `b` values obeys both the cardinality
bound and the height bound. On the Boolean store of `k` candidates the two
coincide at `k`.
-/

noncomputable section
open Classical Function
open scoped BigOperators
namespace NeuralArtifacts
namespace GeneralWidth
universe u v

section Adjoin
variable {R : Type u} [SemilatticeInf R] [OrderTop R] {m : Nat}

/-- Meet on `R` with `m` further elements attached as a chain below all of `R`. -/
def sumOp : R ⊕ Fin m -> R ⊕ Fin m -> R ⊕ Fin m
  | Sum.inl r, Sum.inl s => Sum.inl (r ⊓ s)
  | Sum.inl _, Sum.inr j => Sum.inr j
  | Sum.inr i, Sum.inl _ => Sum.inr i
  | Sum.inr i, Sum.inr j => Sum.inr (max i j)

omit [OrderTop R] in
theorem sumOp_assoc (x y z : R ⊕ Fin m) :
    sumOp (sumOp x y) z = sumOp x (sumOp y z) := by
  cases x <;> cases y <;> cases z <;> simp [sumOp, inf_assoc, max_assoc]

omit [OrderTop R] in
theorem sumOp_comm (x y : R ⊕ Fin m) : sumOp x y = sumOp y x := by
  cases x <;> cases y <;> simp [sumOp, inf_comm, max_comm]

omit [OrderTop R] in
theorem sumOp_idem (x : R ⊕ Fin m) : sumOp x x = x := by
  cases x <;> simp [sumOp]

theorem sumOp_top (x : R ⊕ Fin m) : sumOp x (Sum.inl ⊤) = x := by
  cases x <;> simp [sumOp]

/-- The inference state with `t` unused codes attached below it. -/
def Adjoin (S : Type u) (t : Nat) := S ⊕ Fin t

def adjoinLaws (S : Type u) [SemilatticeInf S] (t : Nat) : MeetLaws (Adjoin S t) where
  op := sumOp
  assoc := sumOp_assoc
  comm := sumOp_comm
  idem := sumOp_idem

instance : SemilatticeInf (Adjoin R m) := (adjoinLaws R m).order

instance : OrderTop (Adjoin R m) where
  top := (Sum.inl ⊤ : R ⊕ Fin m)
  le_top x := by
    show sumOp x (Sum.inl ⊤) = x
    exact sumOp_top x

instance [Fintype R] : Fintype (Adjoin R m) :=
  inferInstanceAs (Fintype (R ⊕ Fin m))

theorem card_adjoin (S : Type u) [Fintype S] (t : Nat) :
    Fintype.card (Adjoin S t) = Fintype.card S + t := by
  show Fintype.card (S ⊕ Fin t) = _
  simp

/-- The inference state sits at the top of the adjoined carrier. -/
def emb (r : R) : Adjoin R m := Sum.inl r

omit [SemilatticeInf R] [OrderTop R] in
theorem emb_injective : Injective (emb (R := R) (m := m)) :=
  fun _ _ h => Sum.inl_injective h

omit [OrderTop R] in
theorem emb_inf (r s : R) : (emb (r ⊓ s) : Adjoin R m) = emb r ⊓ emb s := rfl

theorem emb_top : (emb ⊤ : Adjoin R m) = ⊤ := rfl
end Adjoin

section Coupled
variable (R : Type u) [SemilatticeInf R] [OrderTop R]

/-- A coupled realization of an arbitrary inference state on a `W`-coordinate
`b`-value memory, under an arbitrary commutative pooling operation. -/
def FeasibleGeneral (b W : Nat) : Prop :=
  ∃ cm : CommMonoid (Fin W -> Fin b),
    letI := cm
    ∃ (e : R -> (Fin W -> Fin b)) (out : (Fin W -> Fin b) -> R),
      ∀ s : List R, out (Pooling.aggregate e s) = Inference.eval id s

/-- Coupled width for an arbitrary finite inference state: the memory must hold
the state and nothing more. -/
theorem coupled_feasible_general [Fintype R] (b W : Nat) :
    FeasibleGeneral R b W ↔ Fintype.card R ≤ b ^ W := by
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
    let m := b ^ W - Fintype.card R
    have hcardA : Fintype.card (MeetCarrier (Adjoin R m)) = b ^ W := by
      rw [MeetCarrier.card, card_adjoin]
      omega
    have hcardD : Fintype.card (Fin W -> Fin b) = b ^ W := by
      simp
    let ebox : (Fin W -> Fin b) ≃ MeetCarrier (Adjoin R m) :=
      Fintype.equivOfCardEq (hcardD.trans hcardA.symm)
    let cm : CommMonoid (Fin W -> Fin b) := CoupledWidth.transportCommMonoid ebox
    letI := cm
    let code : R -> (Fin W -> Fin b) := fun r => ebox.symm ⟨emb r⟩
    have hi : Injective code := by
      intro r s h
      apply emb_injective (m := m)
      have hh := congrArg (fun x => (ebox x).val) h
      simpa [code] using hh
    refine ⟨cm, code, CutExchange.decode code, ?_⟩
    intro s
    refine CutExchange.decoded_aggregate code hi ?_ ?_ s
    · show ebox.symm ⟨emb ⊤⟩ = ebox.symm ⟨⊤⟩
      rw [emb_top]
    · intro r t
      show ebox.symm ⟨emb (r ⊓ t)⟩ =
        ebox.symm (ebox (ebox.symm ⟨emb r⟩) * ebox (ebox.symm ⟨emb t⟩))
      simp only [Equiv.apply_symm_apply]
      exact congrArg ebox.symm (MeetCarrier.ext (emb_inf r t))

/-- The chain corollary is the case `R = Fin (n+1)` of the general one. -/
theorem coupledWidth_feasible_eq (n b W : Nat) :
    CoupledWidth.Feasible n b W ↔ FeasibleGeneral (Fin (n + 1)) b W := Iff.rfl
end Coupled

section Independent
variable {R : Type u} [SemilatticeInf R] [OrderTop R]

/-- An independent realization of an arbitrary inference state by `W` channels
of at most `b` values, under arbitrary commutative pooling. -/
def IndFeasible (R : Type u) [SemilatticeInf R] [OrderTop R] (W b : Nat) : Prop :=
  ∃ (Channels : Fin W -> Type u) (cm : ∀ j, CommMonoid (Channels j))
      (ft : ∀ j, Fintype (Channels j)),
    letI := cm
    letI := ft
    ∃ (e : R -> ∀ j, Channels j) (out : (∀ j, Channels j) -> R),
      (∀ j, Fintype.card (Channels j) ≤ b) ∧
      (∀ s : List R, out (Pooling.aggregate e s) = Inference.eval id s)

theorem generated_id : Inference.Generated (id : R -> R) :=
  fun r => ⟨[r], by simp [Inference.eval]⟩

/-- Both bounds on an independently pooled memory: the state must fit in the
coordinate box, and the chain height must fit in the coordinate ranks. -/
theorem independent_width_general [Fintype R] {b W : Nat} {Channels : Fin W -> Type v}
    [∀ j, CommMonoid (Channels j)] [∀ j, Fintype (Channels j)]
    (hb : ∀ j, Fintype.card (Channels j) ≤ b)
    (e : R -> ∀ j, Channels j) (out : (∀ j, Channels j) -> R)
    (hc : ∀ s : List R, out (Pooling.aggregate e s) = Inference.eval id s) :
    Fintype.card R ≤ b ^ W ∧ FiniteOrder.height R - 1 ≤ W * (b - 1) := by
  have he : ∀ r : R, out (e r) = r := by
    intro r
    simpa [Pooling.aggregate, Inference.eval] using hc [r]
  have hi : Injective e := by
    intro r s h
    rw [<- he r, <- he s, h]
  constructor
  · have hcard := Fintype.card_le_of_injective e hi
    have hprod : Fintype.card ((j : Fin W) -> Channels j) ≤ b ^ W := by
      rw [Fintype.card_pi]
      calc ∏ j, Fintype.card (Channels j) ≤ ∏ _j : Fin W, b :=
            Finset.prod_le_prod' (fun j _ => hb j)
        _ = b ^ W := by simp
    exact hcard.trans hprod
  · have hh := Pooling.independent_height_of_injective e out id id
      generated_id (fun _ _ h => h) hc
    have hs : (∑ j, (Fintype.card (Channels j) - 1)) ≤ ∑ _j : Fin W, (b - 1) :=
      Finset.sum_le_sum (fun j _ => Nat.sub_le_sub_right (hb j) 1)
    have hconst : (∑ _j : Fin W, (b - 1)) = W * (b - 1) := by simp
    omega

/-- One binary channel per candidate: channel `j` records whether candidate `j`
is still consistent with the evidence. -/
def boolEncode (k W : Nat) (_h : k ≤ W) (V : Finset (Fin k)) : Fin W -> MeetCarrier Bool :=
  fun j => if hj : j.val < k then ⟨decide ((⟨j.val, hj⟩ : Fin k) ∈ V)⟩ else 1

/-- Read the survivor set off the first `k` channels. -/
def boolDecode (k W : Nat) (h : k ≤ W) (c : Fin W -> MeetCarrier Bool) : Finset (Fin k) :=
  Finset.univ.filter (fun i : Fin k => (c ⟨i.val, lt_of_lt_of_le i.isLt h⟩).val = true)

theorem boolEncode_aggregate (k W : Nat) (h : k ≤ W) (s : List (Finset (Fin k)))
    (j : Fin W) (hj : j.val < k) :
    (Pooling.aggregate (boolEncode k W h) s j).val
      = decide ((⟨j.val, hj⟩ : Fin k) ∈ Inference.eval id s) := by
  induction s with
  | nil =>
    show (1 : MeetCarrier Bool).val = _
    simp [Inference.eval]
  | cons V s ih =>
    have hstep : (Pooling.aggregate (boolEncode k W h) (V :: s) j).val
        = ((boolEncode k W h V j).val && (Pooling.aggregate (boolEncode k W h) s j).val) := rfl
    have hV : (boolEncode k W h V j).val = decide ((⟨j.val, hj⟩ : Fin k) ∈ V) := by
      simp only [boolEncode, dif_pos hj]
    rw [hstep, hV, ih, <- Bool.decide_and, decide_eq_decide]
    simp [Finset.inf_eq_inter]

theorem boolDecode_aggregate (k W : Nat) (h : k ≤ W) (s : List (Finset (Fin k))) :
    boolDecode k W h (Pooling.aggregate (boolEncode k W h) s) = Inference.eval id s := by
  ext i
  simp only [boolDecode, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [boolEncode_aggregate k W h s ⟨i.val, lt_of_lt_of_le i.isLt h⟩ i.isLt]
  simp

/-- On a Boolean store of `k` independently eliminated candidates, independent
pooling into `W` binary channels is possible exactly when `k ≤ W`. -/
theorem boolean_independent_exact (k W : Nat) :
    IndFeasible (Finset (Fin k)) W 2 ↔ k ≤ W := by
  constructor
  · rintro ⟨Channels, cm, ft, hrest⟩
    letI := cm
    letI := ft
    obtain ⟨e, out, hb, hc⟩ := hrest
    have hg := independent_width_general (R := Finset (Fin k)) hb e out hc
    rw [Fintype.card_finset, Fintype.card_fin] at hg
    exact (CoupledWidth.pow_le_iff_exponent_le (by omega)).mp hg.1
  · intro h
    exact ⟨fun _ => MeetCarrier Bool, fun _ => inferInstance, fun _ => inferInstance,
      boolEncode k W h, boolDecode k W h, fun _ => by simp,
      boolDecode_aggregate k W h⟩

/-- Any independent pooling of the Boolean store into `W` channels of at most
two values forces `k ≤ W`, for channels in any universe. -/
theorem boolean_lower_bound {k W : Nat} {Channels : Fin W -> Type v}
    [∀ j, CommMonoid (Channels j)] [∀ j, Fintype (Channels j)]
    (hb : ∀ j, Fintype.card (Channels j) ≤ 2)
    (e : Finset (Fin k) -> ∀ j, Channels j)
    (out : (∀ j, Channels j) -> Finset (Fin k))
    (hc : ∀ s : List (Finset (Fin k)),
      out (Pooling.aggregate e s) = Inference.eval id s) : k ≤ W := by
  have hg := independent_width_general hb e out hc
  rw [Fintype.card_finset, Fintype.card_fin] at hg
  exact (CoupledWidth.pow_le_iff_exponent_le (by omega)).mp hg.1

/-- The coupled width of the same Boolean store is also exactly `k`. -/
theorem boolean_coupled_exact (k W : Nat) :
    FeasibleGeneral (Finset (Fin k)) 2 W ↔ k ≤ W := by
  rw [coupled_feasible_general, Fintype.card_finset, Fintype.card_fin]
  exact CoupledWidth.pow_le_iff_exponent_le (by omega)
end Independent

end GeneralWidth
end NeuralArtifacts

end -- noncomputable section

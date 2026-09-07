import NeuralArtifacts.FiniteOrder

/-!
# 3. Idempotent powers and surjective lifting

Paper: Theorem 3 and Appendix A.2.

The positive-power lemma is proved by a finite pigeonhole argument followed
by eventual periodicity. It does not assume cancellation, commutativity, or
that the original monoid element is idempotent.
-/

noncomputable section
open Classical Function
open scoped BigOperators
namespace NeuralArtifacts
namespace FiniteMonoid
universe u v

section Powers
variable {M : Type u} [Monoid M] [Fintype M]

/-- Among the first `card M + 1` positive powers, two are equal. -/
theorem positive_power_collision (x : M) :
    ∃ a b : Nat, 0 < a ∧ 0 < b ∧ x ^ a = x ^ (a + b) := by
  let N := Fintype.card M
  let f : Fin (N + 1) -> M := fun i => x ^ (i.val + 1)
  have hn : ¬ Injective f := by
    intro hf
    have hc := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_fin] at hc
    dsimp [N] at hc
    omega
  have hex : ∃ i j, f i = f j ∧ i ≠ j := by
    simpa only [Function.Injective, not_forall, Classical.not_imp, exists_prop,
      ne_eq] using hn
  obtain ⟨i, j, hij, hne⟩ := hex
  have hv : i.val ≠ j.val := by
    intro h; exact hne (Fin.ext h)
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · refine ⟨i.val + 1, j.val - i.val, by omega, by omega, ?_⟩
    have he : i.val + 1 + (j.val - i.val) = j.val + 1 := by omega
    simpa [f, he] using hij
  · refine ⟨j.val + 1, i.val - j.val, by omega, by omega, ?_⟩
    have he : j.val + 1 + (i.val - j.val) = i.val + 1 := by omega
    simpa [f, he] using hij.symm

omit [Fintype M] in
/-- An equality at the beginning of the periodic tail propagates forward. -/
theorem power_periodic_tail (x : M) {a b : Nat}
    (h : x ^ a = x ^ (a + b)) {t : Nat} (ht : a ≤ t) :
    x ^ (t + b) = x ^ t := by
  have he : a + (t - a) = t := Nat.add_sub_of_le ht
  calc
    x ^ (t + b) = x ^ ((a + b) + (t - a)) := by congr 1; omega
    _ = x ^ (a + b) * x ^ (t - a) := pow_add _ _ _
    _ = x ^ a * x ^ (t - a) := by rw [<- h]
    _ = x ^ (a + (t - a)) := (pow_add _ _ _).symm
    _ = x ^ t := by rw [he]

omit [Fintype M] in
theorem power_periodic_multiple (x : M) {a b : Nat}
    (h : x ^ a = x ^ (a + b)) {t : Nat} (ht : a ≤ t) (k : Nat) :
    x ^ (t + k * b) = x ^ t := by
  induction k with
  | zero => simp
  | succ k ih =>
    have htk : a ≤ t + k * b := le_trans ht (Nat.le_add_right _ _)
    calc
      x ^ (t + (k + 1) * b) = x ^ ((t + k * b) + b) := by
        congr 1
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      _ = x ^ (t + k * b) := power_periodic_tail x h htk
      _ = x ^ t := ih

/-- Every finite monoid element has a positive idempotent power. -/
theorem exists_positive_idempotent_power (x : M) :
    ∃ r : Nat, 0 < r ∧ (x ^ r) * (x ^ r) = x ^ r := by
  obtain ⟨a, b, ha, hb, hab⟩ := positive_power_collision x
  let r := a * b
  have hr : 0 < r := Nat.mul_pos ha hb
  have har : a ≤ r := by
    dsimp [r]
    nlinarith
  refine ⟨r, hr, ?_⟩
  calc
    x ^ r * x ^ r = x ^ (r + r) := (pow_add _ _ _).symm
    _ = x ^ (r + a * b) := by rfl
    _ = x ^ r := power_periodic_multiple x hab har a
end Powers

/-- The idempotents form a submonoid precisely because multiplication commutes. -/
def idempotents (M : Type u) [CommMonoid M] : Submonoid M where
  carrier := {x | x * x = x}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change (x * y) * (x * y) = x * y
    calc
      (x * y) * (x * y) = (x * x) * (y * y) := by ac_rfl
      _ = x * y := by rw [hx, hy]

abbrev Idem (M : Type u) [CommMonoid M] := idempotents M

instance {M : Type u} [CommMonoid M] [Fintype M] : Fintype (Idem M) :=
  Fintype.ofFinite _

def idemLaws (M : Type u) [CommMonoid M] : MeetLaws (Idem M) where
  op x y := x * y
  assoc := mul_assoc
  comm := mul_comm
  idem x := by apply Subtype.ext; exact x.property

instance {M : Type u} [CommMonoid M] : SemilatticeInf (Idem M) := (idemLaws M).order
instance {M : Type u} [CommMonoid M] : OrderTop (Idem M) where
  top := 1
  le_top x := by change x * 1 = x; exact mul_one x

@[simp] theorem idem_le_iff {M : Type u} [CommMonoid M] (x y : Idem M) :
    x ≤ y ↔ x * y = x := Iff.rfl
@[simp] theorem idem_inf_val {M : Type u} [CommMonoid M] (x y : Idem M) :
    (x ⊓ y).val = x.val * y.val := rfl
@[simp] theorem idem_top_val {M : Type u} [CommMonoid M] :
    (⊤ : Idem M).val = 1 := rfl

theorem idem_height_le_card {M : Type u} [CommMonoid M] [Fintype M] :
    FiniteOrder.height (Idem M) ≤ Fintype.card M := by
  calc
    FiniteOrder.height (Idem M) ≤ Fintype.card (Idem M) :=
      FiniteOrder.height_le_card
    _ ≤ Fintype.card M := Fintype.card_le_of_injective Subtype.val Subtype.val_injective

/-- A homomorphism from multiplication to meet. It need not identify redundant
states in its source. -/
structure ToMeet (M : Type u) (R : Type v) [Monoid M]
    [SemilatticeInf R] [OrderTop R] where
  toFun : M -> R
  map_one : toFun 1 = ⊤
  map_mul : ∀ x y, toFun (x * y) = toFun x ⊓ toFun y

instance {M : Type u} {R : Type v} [Monoid M]
    [SemilatticeInf R] [OrderTop R] :
    CoeFun (ToMeet M R) (fun _ => M -> R) := ⟨ToMeet.toFun⟩

namespace ToMeet
variable {M : Type u} {R : Type v} [Monoid M]
variable [SemilatticeInf R] [OrderTop R]

/-- Positive powers all have the same image in a meet-semilattice. -/
theorem map_positive_power (f : ToMeet M R) (x : M) {n : Nat} (hn : 0 < n) :
    f (x ^ n) = f x := by
  cases n with
  | zero => omega
  | succ k =>
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, f.map_mul, ih (Nat.succ_pos k), inf_idem]

end ToMeet

section Idempotents
variable {M : Type u} {R : Type v} [CommMonoid M]
variable [SemilatticeInf R] [OrderTop R]

namespace ToMeet

def onIdempotents (f : ToMeet M R) : MeetHom (Idem M) R where
  toFun e := f e.val
  map_inf x y := by
    show f.toFun ((x ⊓ y).val) = f.toFun x.val ⊓ f.toFun y.val
    rw [idem_inf_val]
    exact f.map_mul x.val y.val
  map_top := by
    show f.toFun ((⊤ : Idem M).val) = ⊤
    rw [idem_top_val]
    exact f.map_one

/-- Surjectivity survives restriction to idempotents. -/
theorem onIdempotents_surjective [Fintype M]
    (f : ToMeet M R) (hf : Surjective f) : Surjective f.onIdempotents := by
  intro r
  obtain ⟨x, hx⟩ := hf r
  obtain ⟨n, hn, hi⟩ := exists_positive_idempotent_power x
  refine ⟨⟨x ^ n, hi⟩, ?_⟩
  change f (x ^ n) = r
  rw [f.map_positive_power x hn, hx]

theorem height_le_idempotents [Fintype M] [Fintype R]
    (f : ToMeet M R) (hf : Surjective f) :
    FiniteOrder.height R ≤ FiniteOrder.height (Idem M) :=
  FiniteOrder.height_le_of_surjective_meetHom f.onIdempotents
    (f.onIdempotents_surjective hf)
end ToMeet
end Idempotents

section Product
variable {J : Type*} [Fintype J]
variable {M : J -> Type*} [∀ j, CommMonoid (M j)] [∀ j, Fintype (M j)]

/-- Coordinatewise exposure of idempotents of a reachable submonoid. -/
def exposeIdempotents (S : Submonoid (∀ j, M j)) :
    Idem S -> ∀ j, Idem (M j) := fun e j =>
  ⟨e.val.val j, by
    have h := congrArg (fun x : S => x.val j) e.property
    exact h⟩

omit [Fintype J] [∀ j, Fintype (M j)] in
theorem exposeIdempotents_injective (S : Submonoid (∀ j, M j)) :
    Injective (exposeIdempotents S) := by
  intro e f hef
  apply Subtype.ext
  apply Subtype.ext
  funext j
  exact congrArg (fun x => (x j).val) hef

omit [Fintype J] [∀ j, Fintype (M j)] in
theorem exposeIdempotents_monotone (S : Submonoid (∀ j, M j)) :
    Monotone (exposeIdempotents S) := by
  intro e f hef j
  change _ * _ = _
  apply Subtype.ext
  have h := congrArg (fun x : Idem S => x.val.val j) hef
  exact h

/-- The central algebraic inequality, before any neural specialization. -/
theorem exchange_height {R : Type*} [SemilatticeInf R] [OrderTop R] [Fintype R]
    (S : Submonoid (∀ j, M j))
    (f : ToMeet S R) (hf : Surjective f) :
    FiniteOrder.height R - 1 ≤
      ∑ j, (FiniteOrder.height (Idem (M j)) - 1) := by
  have h1 := f.height_le_idempotents hf
  have h2 := FiniteOrder.height_le_of_injective_monotone
    (exposeIdempotents S) (exposeIdempotents_injective S)
    (exposeIdempotents_monotone S)
  have h3 := FiniteOrder.product_height (B := fun j => Idem (M j))
  have h := h1.trans (h2.trans h3)
  omega

theorem exchange_card {R : Type*} [SemilatticeInf R] [OrderTop R] [Fintype R]
    (S : Submonoid (∀ j, M j))
    (f : ToMeet S R) (hf : Surjective f) :
    FiniteOrder.height R - 1 ≤ ∑ j, (Fintype.card (M j) - 1) := by
  apply le_trans (exchange_height S f hf)
  apply Finset.sum_le_sum
  intro j hj
  exact Nat.sub_le_sub_right idem_height_le_card 1

end Product

/-- A finite group has no idempotent other than the identity. -/
theorem group_idempotent_eq_one {G : Type*} [Group G] {x : G}
    (hx : x * x = x) : x = 1 := by
  have h : x * x = x * 1 := by simpa using hx
  exact mul_left_cancel h

theorem commGroup_idempotents_subsingleton {G : Type*} [CommGroup G] :
    Subsingleton (Idem G) := by
  refine ⟨?_⟩
  intro x y
  apply Subtype.ext
  rw [group_idempotent_eq_one x.property, group_idempotent_eq_one y.property]

end FiniteMonoid
end NeuralArtifacts

end -- noncomputable section

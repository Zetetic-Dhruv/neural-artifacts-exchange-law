import NeuralArtifacts.Congruence

/-!
# 8. Exact residual exchange for an arbitrary structural chain quotient

The proof counts changes in a monotone sequence of quotient states. The
residual cuts precisely where the structural sequence does not change.
This treats every structural meet quotient, not just equally sized blocks.
-/

noncomputable section
open Classical Function
open scoped BigOperators
namespace NeuralArtifacts
namespace ResidualChain

/-- A useful two-factor form of the product-height theorem. -/
theorem product_height_two {A B : Type*} [PartialOrder A] [PartialOrder B]
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    FiniteOrder.height (A × B) ≤ FiniteOrder.height A + FiniteOrder.height B - 1 := by
  have ha := FiniteOrder.height_pos (A := A)
  have hb := FiniteOrder.height_pos (A := B)
  have key : FiniteOrder.height (A × B) ≤
      (FiniteOrder.height A - 1) + (FiniteOrder.height B - 1) + 1 := by
    apply Finset.sup_le
    intro s hs
    have hc := (FiniteOrder.mem_chains s).mp hs
    set cap := (FiniteOrder.height A - 1) + (FiniteOrder.height B - 1) with hcap
    let pot : A × B -> Nat :=
      fun p => FiniteOrder.excessRank p.1 + FiniteOrder.excessRank p.2
    have hpotle : ∀ p : A × B, pot p ≤ cap := fun p =>
      Nat.add_le_add (FiniteOrder.excessRank_le p.1) (FiniteOrder.excessRank_le p.2)
    have hpotstrict : ∀ {p q : A × B}, p < q -> pot p < pot q := by
      intro p q hpq
      have h1 : p.1 ≤ q.1 := hpq.le.1
      have h2 : p.2 ≤ q.2 := hpq.le.2
      have hsplit : p.1 ≠ q.1 ∨ p.2 ≠ q.2 := by
        by_contra hcon
        push Not at hcon
        exact hpq.ne (Prod.ext hcon.1 hcon.2)
      rcases hsplit with hd | hd
      · have hs1 := FiniteOrder.excessRank_strict (lt_of_le_of_ne h1 hd)
        have hs2 := FiniteOrder.excessRank_mono h2
        simp only [pot]
        omega
      · have hs1 := FiniteOrder.excessRank_mono h1
        have hs2 := FiniteOrder.excessRank_strict (lt_of_le_of_ne h2 hd)
        simp only [pot]
        omega
    let f : {x // x ∈ s} -> Fin (cap + 1) :=
      fun x => ⟨pot x.val, Nat.lt_succ_of_le (hpotle x.val)⟩
    have hf : Injective f := by
      intro x y hxy
      apply Subtype.ext
      have heq : pot x.val = pot y.val := congrArg Fin.val hxy
      by_contra hne
      rcases hc x.val x.property y.val y.property with hle | hle
      · exact (ne_of_lt (hpotstrict (lt_of_le_of_ne hle hne))) heq
      · exact (ne_of_lt (hpotstrict (lt_of_le_of_ne hle (Ne.symm hne)))) heq.symm
    have hcard := Fintype.card_le_of_injective f hf
    simpa using hcard
  omega

/-- Counting distinct values of a monotone sequence by its change points. -/
def changes {A : Type*} (f : Nat -> A) (n : Nat) : Finset Nat :=
  (Finset.range n).filter (fun i => f i ≠ f (i + 1))

theorem next_mem_image_iff {A : Type*} [PartialOrder A]
    (f : Nat -> A) (hf : Monotone f) (n : Nat) :
    f (n + 1) ∈ (Finset.range (n + 1)).image f ↔ f n = f (n + 1) := by
  constructor
  · intro h
    obtain ⟨i, hi, hei⟩ := Finset.mem_image.mp h
    have hin : i ≤ n := by simpa using Finset.mem_range.mp hi
    apply le_antisymm (hf (by omega))
    have hh := hf hin
    rw [hei] at hh
    exact hh
  · intro h
    exact Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (by omega), h⟩

theorem image_card_eq_changes {A : Type*} [PartialOrder A]
    (f : Nat -> A) (hf : Monotone f) (n : Nat) :
    ((Finset.range (n + 1)).image f).card = (changes f n).card + 1 := by
  induction n with
  | zero => simp [changes]
  | succ n ih =>
    have hn : n ∉ changes f n := by simp [changes]
    by_cases he : f n = f (n + 1)
    · have hm := (next_mem_image_iff f hf n).mpr he
      have hc : changes f (n + 1) = changes f n := by
        simp [changes, Finset.range_add_one, Finset.filter_insert, he]
      rw [hc, Finset.range_add_one, Finset.image_insert,
        Finset.insert_eq_self.mpr hm]
      exact ih
    · have hm : f (n + 1) ∉ (Finset.range (n + 1)).image f := by
        intro h; exact he ((next_mem_image_iff f hf n).mp h)
      have hc : changes f (n + 1) = insert n (changes f n) := by
        simp [changes, Finset.range_add_one, Finset.filter_insert, he]
      rw [hc, Finset.card_insert_of_notMem hn, Finset.range_add_one,
        Finset.image_insert, Finset.card_insert_of_notMem hm, ih]

/-- Saturating extension of a finite chain map to natural indices. -/
def clamp (n i : Nat) : Fin (n + 1) := ⟨min i n, Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem clamp_monotone (n : Nat) : Monotone (clamp n) := by
  intro i j hij
  change min i n ≤ min j n
  omega

@[simp] theorem clamp_val (n : Nat) (r : Fin (n + 1)) : clamp n r.val = r := by
  apply Fin.ext
  dsimp [clamp]
  have hr : r.val ≤ n := by have := r.isLt; omega
  exact min_eq_left hr

/-- Convert bounded natural cut positions to `Fin` positions, preserving their count. -/
def finCuts {n : Nat} (B : Finset Nat) (hb : ∀ i ∈ B, i < n) : Finset (Fin n) :=
  B.attach.map ⟨fun i => ⟨i.val, hb i.val i.property⟩, by
    intro i j h
    apply Subtype.ext
    exact congrArg Fin.val h⟩

@[simp] theorem finCuts_card {n : Nat} (B : Finset Nat) (hb : ∀ i ∈ B, i < n) :
    (finCuts B hb).card = B.card := by simp [finCuts]

@[simp] theorem mem_finCuts {n : Nat} (B : Finset Nat) (hb : ∀ i ∈ B, i < n)
    (c : Fin n) : c ∈ finCuts B hb ↔ c.val ∈ B := by
  constructor
  · intro h
    obtain ⟨i, hi, he⟩ := Finset.mem_map.mp h
    have hh : i.val = c.val := congrArg Fin.val he
    exact hh ▸ i.property
  · intro h
    refine Finset.mem_map.mpr ⟨⟨c.val, h⟩, by simp, ?_⟩
    apply Fin.ext; rfl

section Chain
variable (n : Nat) (a : Congruence.Rel (Fin (n + 1)))

/-- Congruence classes on a chain are intervals. -/
theorem interval_classes {r s t : Fin (n + 1)}
    (hrs : r ≤ s) (hst : s ≤ t) (h : Congruence.Holds a r t) :
    Congruence.Holds a r s := by
  have hh : Congruence.Holds a (r ⊓ s) (t ⊓ s) :=
    a.compatible h (Congruence.holds_refl a s)
  rw [inf_eq_left.mpr hrs, inf_eq_right.mpr hst] at hh
  exact hh

/-- A natural-indexed structural sequence. -/
def structuralSequence : Nat -> Congruence.Quot a :=
  fun i => Congruence.proj a (clamp n i)

theorem structuralSequence_monotone : Monotone (structuralSequence n a) :=
  (Congruence.quotientHom a).monotone.comp (clamp_monotone n)

theorem structural_image_univ :
    (Finset.range (n + 1)).image (structuralSequence n a) = Finset.univ := by
  ext q
  constructor
  · intro h; exact Finset.mem_univ q
  · intro h
    obtain ⟨r, rfl⟩ := Congruence.proj_surjective a q
    exact Finset.mem_image.mpr ⟨r.val, Finset.mem_range.mpr r.isLt, by
      simp [structuralSequence]⟩

theorem structural_cut_count :
    (changes (structuralSequence n a) n).card + 1 = Fintype.card (Congruence.Quot a) := by
  have h := image_card_eq_changes (structuralSequence n a)
    (structuralSequence_monotone n a) n
  rw [structural_image_univ] at h
  simpa using h.symm

/-- The residual cuts where the structural representation remains equal. -/
def residualBoundaries : Finset Nat :=
  Finset.range n \ changes (structuralSequence n a) n

theorem residualBoundaries_lt (i : Nat) (hi : i ∈ residualBoundaries n a) : i < n :=
  Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1

def residualCuts : Finset (Fin n) :=
  finCuts (residualBoundaries n a) (residualBoundaries_lt n a)

theorem residual_cut_count :
    (residualCuts n a).card + Fintype.card (Congruence.Quot a) = n + 1 := by
  have hsub : changes (structuralSequence n a) n ⊆ Finset.range n := Finset.filter_subset _ _
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  have hq := structural_cut_count n a
  simp only [Finset.card_range] at hc
  rw [residualCuts, finCuts_card]
  dsimp [residualBoundaries]
  omega

/-- Structural equality across an interval forces every intervening boundary
into the residual cut set. -/
theorem boundary_in_residual {r s : Fin (n + 1)} (hrs : r < s)
    (ha : Congruence.proj a r = Congruence.proj a s) :
    ∃ c : Fin n, c.val = r.val ∧ c ∈ residualCuts n a := by
  have hrn : r.val < n := by have := s.isLt; omega
  let c : Fin n := ⟨r.val, hrn⟩
  have hmono := structuralSequence_monotone n a
  have hrnext : structuralSequence n a r.val = structuralSequence n a (r.val + 1) := by
    apply le_antisymm (hmono (by omega))
    have hh := hmono (show r.val + 1 ≤ s.val by omega)
    simpa [structuralSequence, ha] using hh
  refine ⟨c, rfl, ?_⟩
  rw [residualCuts, mem_finCuts]
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_range.mpr hrn, ?_⟩
  simp only [changes, Finset.mem_filter, ne_eq, not_and, not_not]
  exact fun _ => hrnext

theorem structural_residual_injective :
    Injective (fun r : Fin (n + 1) =>
      (Congruence.proj a r, CutExchange.cutCode (residualCuts n a) r)) := by
  intro r s h
  have ha := congrArg Prod.fst h
  have hb := congrArg (fun p => p.2.val) h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hrs | hsr
  · obtain ⟨c, hcr, hc⟩ := boundary_in_residual n a hrs ha
    have hstrict := CutExchange.cutRank_strict (residualCuts n a) hc
      (r := r) (s := s) (by omega) (by omega)
    exact (ne_of_lt hstrict) hb
  · obtain ⟨c, hcs, hc⟩ := boundary_in_residual n a hsr ha.symm
    have hstrict := CutExchange.cutRank_strict (residualCuts n a) hc
      (r := s) (s := r) (by omega) (by omega)
    exact (ne_of_lt hstrict) hb.symm

/-- Every jointly injective pair of normalized views obeys the additive bound. -/
theorem joint_lower (b : Congruence.Rel (Fin (n + 1))) (hj : Congruence.Joint a b) :
    n + 1 ≤ Fintype.card (Congruence.Quot a) + Fintype.card (Congruence.Quot b) - 1 := by
  let pair := fun r => (Congruence.proj a r, Congruence.proj b r)
  have hi : Injective pair := (Congruence.joint_iff_pair_injective a b).mp hj
  have hm : Monotone pair := by
    intro r s hrs
    exact ⟨(Congruence.quotientHom a).monotone hrs,
      (Congruence.quotientHom b).monotone hrs⟩
  have h1 := FiniteOrder.height_le_of_injective_monotone pair hi hm
  have h2 := product_height_two (A := Congruence.Quot a) (B := Congruence.Quot b)
  have h3 := FiniteOrder.height_le_card (A := Congruence.Quot a)
  have h4 := FiniteOrder.height_le_card (A := Congruence.Quot b)
  simp only [FiniteOrder.height_fin] at h1
  omega

/-- Proposition 5: every structural quotient with `a` states leaves exactly
`n+2-a` residual states on an `(n+1)`-state chain. -/
theorem exact_residual :
    Congruence.minimumResidual a = n + 2 - Fintype.card (Congruence.Quot a) := by
  have haPos : 1 ≤ Fintype.card (Congruence.Quot a) := Fintype.card_pos_iff.mpr inferInstance
  have haLe : Fintype.card (Congruence.Quot a) ≤ n + 1 := by
    simpa using Fintype.card_le_of_surjective _ (Congruence.proj_surjective a)
  apply le_antisymm
  · let f := CutExchange.cutHom (residualCuts n a)
    let b := Congruence.kernel f
    have hj : Congruence.Joint a b := by
      intro r s har hbr
      apply structural_residual_injective n a
      exact Prod.ext ((Congruence.proj_eq a r s).mpr har) hbr
    let qread : Congruence.Quot b -> Fin ((residualCuts n a).card + 1) :=
      Quotient.lift f (by intro r s h; exact h)
    have hqi : Injective qread := by
      intro q r
      refine Quotient.inductionOn q ?_; intro x
      refine Quotient.inductionOn r ?_; intro y h
      exact Quotient.sound h
    have hbcard := Fintype.card_le_of_injective qread hqi
    have hm := Congruence.minimumResidual_le a b hj
    have hcuts := residual_cut_count n a
    simp only [Fintype.card_fin] at hbcard
    omega
  · obtain ⟨b, hb, hc⟩ := Congruence.minimumResidual_attained a
    have hl := joint_lower n a b hb
    omega
end Chain

/-- The one-shot parity encoding of the four-state chain is injective. -/
theorem parity_pair_injective :
    Injective (fun r : Fin 4 => (r.val / 2, r.val % 2)) := by
  intro r s h
  apply Fin.ext
  have hq : r.val / 2 = s.val / 2 := congrArg Prod.fst h
  have hr : r.val % 2 = s.val % 2 := congrArg Prod.snd h
  omega

/-- The same parity map does not preserve the meet operation. -/
theorem parity_not_meet_determined :
    ¬ (∃ op : Nat -> Nat -> Nat,
      ∀ r s : Fin 4, (min r s).val % 2 = op (r.val % 2) (s.val % 2)) := by
  rintro ⟨op, h⟩
  have h01 := h (0 : Fin 4) (1 : Fin 4)
  have h21 := h (2 : Fin 4) (1 : Fin 4)
  norm_num at h01 h21
  omega

end ResidualChain
end NeuralArtifacts

end -- noncomputable section

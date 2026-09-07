import NeuralArtifacts.Prelude

/-!
# 2. Finite height and product bounds

We define height by an actual finite maximum over chains. In particular the
proof does not assume that a state-count bound is an order-height bound.
The coordinate potential is the sum of longest-chain ranks minus one.
-/

noncomputable section
open Classical Function
open scoped BigOperators
namespace NeuralArtifacts
namespace FiniteOrder
universe u v
variable {A : Type u} [PartialOrder A] [Fintype A]

def Chain (s : Finset A) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≤ y ∨ y ≤ x

def chains (A : Type u) [PartialOrder A] [Fintype A] : Finset (Finset A) :=
  Finset.univ.powerset.filter Chain

def height (A : Type u) [PartialOrder A] [Fintype A] : Nat :=
  (chains A).sup Finset.card

@[simp] theorem mem_chains (s : Finset A) : s ∈ chains A ↔ Chain s := by
  simp [chains]

theorem card_le_height {s : Finset A} (hs : Chain s) : s.card ≤ height A := by
  exact Finset.le_sup (f := Finset.card) (mem_chains s |>.mpr hs)

theorem height_le_card : height A ≤ Fintype.card A := by
  apply Finset.sup_le
  intro s hs
  exact Finset.card_le_univ s

theorem height_pos [Nonempty A] : 0 < height A := by
  let x : A := Classical.arbitrary A
  have h : Chain ({x} : Finset A) := by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst a; subst b
    exact Or.inl le_rfl
  have hh := card_le_height h
  have h1 : 1 ≤ height A := by simpa using hh
  omega

theorem chains_nonempty : (chains A).Nonempty := by
  refine ⟨∅, ?_⟩
  simp [Chain]

theorem height_attained : ∃ s : Finset A, Chain s ∧ s.card = height A := by
  obtain ⟨s, hs, hm⟩ := finset_sup_attained (chains A) Finset.card chains_nonempty
  exact ⟨s, (mem_chains s).mp hs, hm⟩

def lowerChains (x : A) : Finset (Finset A) :=
  (chains A).filter (fun s => ∀ y ∈ s, y ≤ x)

def rank (x : A) : Nat := (lowerChains x).sup Finset.card

@[simp] theorem mem_lowerChains (x : A) (s : Finset A) :
    s ∈ lowerChains x ↔ Chain s ∧ (∀ y ∈ s, y ≤ x) := by
  simp [lowerChains]

theorem lowerChains_nonempty (x : A) : (lowerChains x).Nonempty := by
  refine ⟨∅, ?_⟩
  simp [Chain]

theorem rank_attained (x : A) :
    ∃ s : Finset A, Chain s ∧ (∀ y ∈ s, y ≤ x) ∧ s.card = rank x := by
  obtain ⟨s, hs, hm⟩ := finset_sup_attained (lowerChains x) Finset.card
    (lowerChains_nonempty x)
  exact ⟨s, (mem_lowerChains x s).mp hs |>.1,
    (mem_lowerChains x s).mp hs |>.2, hm⟩

theorem card_le_rank {x : A} {s : Finset A}
    (hc : Chain s) (hb : ∀ y ∈ s, y ≤ x) : s.card ≤ rank x := by
  exact Finset.le_sup (f := Finset.card) ((mem_lowerChains x s).mpr ⟨hc, hb⟩)

theorem rank_le_height (x : A) : rank x ≤ height A := by
  apply Finset.sup_le
  intro s hs
  exact card_le_height ((mem_lowerChains x s).mp hs).1

theorem rank_pos (x : A) : 1 ≤ rank x := by
  have hc : Chain ({x} : Finset A) := by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst a; subst b; exact Or.inl le_rfl
  have hb : ∀ y ∈ ({x} : Finset A), y ≤ x := by simp
  simpa using card_le_rank hc hb

/-- Appending a strictly larger point increases the attainable chain length. -/
theorem rank_strict {x y : A} (hxy : x < y) : rank x < rank y := by
  obtain ⟨s, hchain, hbound, hcard⟩ := rank_attained x
  have hy : y ∉ s := by
    intro hy
    exact (not_le_of_gt hxy) (hbound y hy)
  have hi : Chain (insert y s) := by
    intro a ha b hb
    rcases Finset.mem_insert.mp ha with rfl | ha'
    · rcases Finset.mem_insert.mp hb with rfl | hb'
      · exact Or.inl le_rfl
      · exact Or.inr ((hbound b hb').trans hxy.le)
    · rcases Finset.mem_insert.mp hb with rfl | hb'
      · exact Or.inl ((hbound a ha').trans hxy.le)
      · exact hchain a ha' b hb'
  have hib : ∀ z ∈ insert y s, z ≤ y := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact le_rfl
    · exact (hbound z hz).trans hxy.le
  have h := card_le_rank hi hib
  rw [Finset.card_insert_of_notMem hy, hcard] at h
  omega

theorem rank_monotone : Monotone (@rank A _ _) := by
  intro x y hxy
  by_cases he : x = y
  · subst y; exact le_rfl
  · have hl : x < y := lt_iff_le_not_ge.mpr
      ⟨hxy, fun hyx => he (le_antisymm hxy hyx)⟩
    exact (rank_strict hl).le

/-- A zero-based rank, useful because product heights add excess height. -/
def excessRank (x : A) : Nat := rank x - 1

theorem excessRank_mono : Monotone (@excessRank A _ _) := by
  intro x y hxy
  exact Nat.sub_le_sub_right (rank_monotone hxy) 1

theorem excessRank_strict {x y : A} (hxy : x < y) :
    excessRank x < excessRank y := by
  have h := rank_strict hxy
  have hx := rank_pos x
  have hy := rank_pos y
  unfold excessRank
  omega

theorem excessRank_le (x : A) : excessRank x ≤ height A - 1 := by
  exact Nat.sub_le_sub_right (rank_le_height x) 1

/-- Height is monotone under an injective monotone map. -/
theorem height_le_of_injective_monotone {B : Type v} [PartialOrder B] [Fintype B]
    (f : A -> B) (hi : Injective f) (hm : Monotone f) : height A ≤ height B := by
  apply Finset.sup_le
  intro s hs
  have hc := (mem_chains s).mp hs
  have himage : Chain (s.image f) := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    rcases hc a ha b hb with hab | hba
    · exact Or.inl (hm hab)
    · exact Or.inr (hm hba)
  have hcard : (s.image f).card = s.card := Finset.card_image_iff.mpr
    (fun a _ b _ hab => hi hab)
  rw [<- hcard]
  exact card_le_height himage

section Product
variable {J : Type*} [Fintype J]
variable {B : J -> Type*} [∀ j, PartialOrder (B j)] [∀ j, Fintype (B j)]

def potential (x : ∀ j, B j) : Nat := ∑ j, excessRank (x j)

theorem potential_le (x : ∀ j, B j) :
    potential x ≤ ∑ j, (height (B j) - 1) := by
  exact Finset.sum_le_sum (fun j _ => excessRank_le (x j))

theorem potential_strict {x y : ∀ j, B j} (hxy : x < y) :
    potential x < potential y := by
  have hle : ∀ j, x j ≤ y j := hxy.le
  have hne : ∃ j, x j ≠ y j := by
    by_contra! h
    exact hxy.ne (funext h)
  obtain ⟨j, hj⟩ := hne
  have hjlt : x j < y j := lt_iff_le_not_ge.mpr
    ⟨hle j, fun hh => hj (le_antisymm (hle j) hh)⟩
  apply Finset.sum_lt_sum
  · intro k hk; exact excessRank_mono (hle k)
  · exact ⟨j, Finset.mem_univ j, excessRank_strict hjlt⟩

theorem product_height :
    height (∀ j, B j) ≤ 1 + ∑ j, (height (B j) - 1) := by
  apply Finset.sup_le
  intro s hs
  have hc := (mem_chains s).mp hs
  let cap := ∑ j, (height (B j) - 1)
  let f : {x // x ∈ s} -> Fin (cap + 1) :=
    fun x => ⟨potential x.val, Nat.lt_succ_of_le (potential_le x.val)⟩
  have hf : Injective f := by
    intro x y hxy
    apply Subtype.ext
    have heq : potential x.val = potential y.val := congrArg Fin.val hxy
    by_contra hne
    rcases hc x.val x.property y.val y.property with hle | hle
    · have hlt : x.val < y.val := lt_iff_le_not_ge.mpr
        ⟨hle, fun hh => hne (le_antisymm hle hh)⟩
      exact (ne_of_lt (potential_strict hlt)) heq
    · have hlt : y.val < x.val := lt_iff_le_not_ge.mpr
        ⟨hle, fun hh => hne (le_antisymm hh hle)⟩
      exact (ne_of_lt (potential_strict hlt)) heq.symm
  have hcard := Fintype.card_le_of_injective f hf
  simpa [cap, Nat.add_comm] using hcard
end Product

section Lift
variable {B : Type v} [SemilatticeInf B] [OrderTop B] [Fintype B]
variable {A₀ : Type u} [SemilatticeInf A₀] [OrderTop A₀] [Fintype A₀]

/-- Meet-surjections lift each finite chain. The lift is built by taking all
chosen preimages above the target point, not by assuming an order section. -/
theorem height_le_of_surjective_meetHom (f : MeetHom A₀ B) (hf : Surjective f) :
    height B ≤ height A₀ := by
  let choosePre : B -> A₀ := fun b => Classical.choose (hf b)
  have hpre : ∀ b, f (choosePre b) = b := fun b => Classical.choose_spec (hf b)
  apply Finset.sup_le
  intro s hs
  have hc := (mem_chains s).mp hs
  let lift : B -> A₀ := fun b => (s.filter (fun t => b ≤ t)).inf choosePre
  have hlift : ∀ b ∈ s, f (lift b) = b := by
    intro b hb
    dsimp [lift]
    rw [f.map_finset_inf]
    simp only [hpre]
    apply le_antisymm
    · exact Finset.inf_le (Finset.mem_filter.mpr ⟨hb, le_rfl⟩)
    · exact Finset.le_inf (fun t ht => (Finset.mem_filter.mp ht).2)
  have hmono : Monotone lift := by
    intro b c hbc
    apply Finset.le_inf
    intro t ht
    exact Finset.inf_le (Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp ht).1, hbc.trans (Finset.mem_filter.mp ht).2⟩)
  have hinj : Set.InjOn lift (s : Set B) := by
    intro b hb c hc heq
    calc
      b = f (lift b) := (hlift b hb).symm
      _ = f (lift c) := congrArg f heq
      _ = c := hlift c hc
  have hchain : Chain (s.image lift) := by
    intro x hx y hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨c, hc', rfl⟩ := Finset.mem_image.mp hy
    rcases hc b hb c hc' with hbc | hcb
    · exact Or.inl (hmono hbc)
    · exact Or.inr (hmono hcb)
  have hcard : (s.image lift).card = s.card := Finset.card_image_iff.mpr hinj
  rw [<- hcard]
  exact card_le_height hchain
end Lift

@[simp] theorem height_fin (n : Nat) : height (Fin n) = n := by
  apply le_antisymm
  · simpa using (height_le_card (A := Fin n))
  · have hc : Chain (Finset.univ : Finset (Fin n)) := by
      intro x hx y hy; exact le_total x y
    simpa using card_le_height hc

end FiniteOrder
end NeuralArtifacts

end -- noncomputable section

import NeuralArtifacts.Pooling

/-!
# 5. Matching constructions: allocating adjacent cuts

An `(n+1)`-state chain has exactly `n` adjacent boundaries. We construct a
representation for arbitrary channel budgets by injecting those boundaries
into the disjoint union of available channel slots. No divisibility or
uniform-budget hypothesis is used.
-/

noncomputable section
open Classical Function
open scoped BigOperators
namespace NeuralArtifacts
namespace CutExchange

/-- Number of selected boundaries strictly below a chain state. -/
def cutRank {n : Nat} (B : Finset (Fin n)) (r : Fin (n + 1)) : Nat :=
  (B.filter (fun c => c.val < r.val)).card

theorem cutRank_le {n : Nat} (B : Finset (Fin n)) (r : Fin (n + 1)) :
    cutRank B r ≤ B.card := Finset.card_le_card (Finset.filter_subset _ _)

def cutCode {n : Nat} (B : Finset (Fin n)) (r : Fin (n + 1)) : Fin (B.card + 1) :=
  ⟨cutRank B r, Nat.lt_succ_of_le (cutRank_le B r)⟩

theorem cutRank_monotone {n : Nat} (B : Finset (Fin n)) : Monotone (cutRank B) := by
  intro r s hrs
  apply Finset.card_le_card
  intro c hc
  rcases Finset.mem_filter.mp hc with ⟨hc, hcr⟩
  exact Finset.mem_filter.mpr ⟨hc, lt_of_lt_of_le hcr hrs⟩

theorem cutCode_monotone {n : Nat} (B : Finset (Fin n)) : Monotone (cutCode B) := by
  intro r s hrs
  exact cutRank_monotone B hrs

theorem cutCode_inf {n : Nat} (B : Finset (Fin n)) (r s : Fin (n + 1)) :
    cutCode B (r ⊓ s) = cutCode B r ⊓ cutCode B s := by
  rcases le_total r s with hrs | hsr
  · rw [inf_eq_left.mpr hrs, inf_eq_left.mpr (cutCode_monotone B hrs)]
  · rw [inf_eq_right.mpr hsr, inf_eq_right.mpr (cutCode_monotone B hsr)]

theorem cutCode_top {n : Nat} (B : Finset (Fin n)) :
    cutCode B (⊤ : Fin (n + 1)) = ⊤ := by
  apply Fin.ext
  change (B.filter (fun c => c.val < n)).card = B.card
  congr 1
  ext c
  simp

def cutHom {n : Nat} (B : Finset (Fin n)) :
    MeetHom (Fin (n + 1)) (Fin (B.card + 1)) :=
  ⟨cutCode B, cutCode_inf B, cutCode_top B⟩

/-- A selected boundary separates every pair straddling it. -/
theorem cutRank_strict {n : Nat} (B : Finset (Fin n))
    {r s : Fin (n + 1)} {c : Fin n}
    (hc : c ∈ B) (hr : r.val ≤ c.val) (hs : c.val < s.val) :
    cutRank B r < cutRank B s := by
  have hrs : r ≤ s := Fin.le_def.mpr (by omega)
  have hsub : (B.filter (fun d => d.val < r.val)) ⊆
      (B.filter (fun d => d.val < s.val)) := by
    intro d hd
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hd).1,
      lt_of_lt_of_le (Finset.mem_filter.mp hd).2 hrs⟩
  have hnot : c ∉ B.filter (fun d => d.val < r.val) := by
    simp only [Finset.mem_filter, not_and]
    intro _
    exact not_lt_of_ge hr
  have hinsert : insert c (B.filter (fun d => d.val < r.val)) ⊆
      B.filter (fun d => d.val < s.val) := by
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact Finset.mem_filter.mpr ⟨hc, hs⟩
    · exact hsub hd
  have hcard := Finset.card_le_card hinsert
  rw [Finset.card_insert_of_notMem hnot] at hcard
  exact Nat.lt_of_succ_le hcard

/-- Covering the adjacent boundaries makes the complete code injective. -/
theorem cut_family_injective {n : Nat} {J : Type*}
    (B : J -> Finset (Fin n)) (hcover : ∀ c, ∃ j, c ∈ B j) :
    Injective (fun r : Fin (n + 1) => fun j => cutCode (B j) r) := by
  intro r s hrs
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hrn : r.val < n := by have := s.isLt; omega
    let c : Fin n := ⟨r.val, hrn⟩
    obtain ⟨j, hj⟩ := hcover c
    have hstrict := cutRank_strict (B j) hj (r := r) (s := s) le_rfl hlt
    have heq := congrArg (fun f => (f j).val) hrs
    exact (ne_of_lt hstrict) heq
  · have hsn : s.val < n := by have := r.isLt; omega
    let c : Fin n := ⟨s.val, hsn⟩
    obtain ⟨j, hj⟩ := hcover c
    have hstrict := cutRank_strict (B j) hj (r := s) (s := r) le_rfl hgt
    have heq := congrArg (fun f => (f j).val) hrs
    exact (ne_of_lt hstrict) heq.symm

/-- The fibre of a sigma type at a fixed first coordinate. -/
def sigmaFiberEquiv {J : Type*} (D : J -> Type*) (j : J) :
    {x : Sigma D // x.1 = j} ≃ D j where
  toFun x := by
    rcases x with ⟨⟨i, v⟩, h⟩
    cases h
    exact v
  invFun v := ⟨⟨j, v⟩, rfl⟩
  left_inv := by rintro ⟨⟨i, v⟩, h⟩; cases h; rfl
  right_inv := by intro v; rfl

/-- Allocate boundary slots without assuming uniform capacities. -/
theorem allocate_cuts {J : Type*} [Fintype J] (n : Nat) (cap : J -> Nat)
    (hcap : n ≤ ∑ j, cap j) :
    ∃ B : J -> Finset (Fin n),
      (∀ c, ∃ j, c ∈ B j) ∧ (∀ j, (B j).card ≤ cap j) := by
  have hcard : Fintype.card (Fin n) ≤ Fintype.card (Sigma (fun j => Fin (cap j))) := by
    simpa [Fintype.card_sigma, Fintype.card_fin] using hcap
  let slots : Fin n ↪ Sigma (fun j => Fin (cap j)) := finiteEmbedding hcard
  let B : J -> Finset (Fin n) := fun j => Finset.univ.filter (fun c => (slots c).1 = j)
  refine ⟨B, ?_, ?_⟩
  · intro c
    exact ⟨(slots c).1, by simp [B]⟩
  · intro j
    let f : {c // c ∈ B j} ->
        {x : Sigma (fun i => Fin (cap i)) // x.1 = j} :=
      fun c => ⟨slots c.val, (Finset.mem_filter.mp c.property).2⟩
    have hf : Injective f := by
      intro c d h
      apply Subtype.ext
      apply slots.injective
      exact congrArg Subtype.val h
    have hc := Fintype.card_le_of_injective f hf
    have he := Fintype.card_congr (sigmaFiberEquiv (fun i => Fin (cap i)) j)
    rw [he] at hc
    simpa using hc

section Decoder
variable {R : Type*} [SemilatticeInf R] [OrderTop R]
variable {M : Type*} [CommMonoid M]

/-- Decode only reachable codes. The default is never used in the proof. -/
def decode (code : R -> M) (m : M) : R :=
  if h : ∃ r, code r = m then Classical.choose h else ⊤

omit [CommMonoid M] in
theorem decode_code (code : R -> M) (hi : Injective code) (r : R) :
    decode code (code r) = r := by
  unfold decode
  split_ifs with h
  · exact hi (Classical.choose_spec h)
  · exact False.elim (h ⟨r, rfl⟩)

theorem aggregate_code (code : R -> M)
    (h0 : code ⊤ = 1) (hm : ∀ r s, code (r ⊓ s) = code r * code s)
    (s : List R) :
    Pooling.aggregate code s = code (Inference.eval id s) := by
  induction s with
  | nil => simpa using h0.symm
  | cons r s ih => simp [Pooling.aggregate_cons, Inference.eval, ih, hm]

theorem decoded_aggregate (code : R -> M) (hi : Injective code)
    (h0 : code ⊤ = 1) (hm : ∀ r s, code (r ⊓ s) = code r * code s)
    (s : List R) :
    decode code (Pooling.aggregate code s) = Inference.eval id s := by
  rw [aggregate_code code h0 hm, decode_code code hi]
end Decoder

/-- Feasibility permits arbitrary finite commutative channels and redundant
history states. Only correctness and the stated channel budgets are required. -/
def Feasible {J : Type*} [Fintype J] (n : Nat) (budget : J -> Nat) : Prop :=
  ∃ (M : J -> Type) (cm : ∀ j, CommMonoid (M j)) (ft : ∀ j, Fintype (M j)),
    letI := cm
    letI := ft
    ∃ (e : Fin (n + 1) -> ∀ j, M j) (out : (∀ j, M j) -> Fin (n + 1)),
      (∀ j, Fintype.card (M j) ≤ budget j) ∧
      (∀ s, out (Pooling.aggregate e s) = Inference.eval id s)

/-- The sharp capacity region, with `n` boundaries and `n+1` states. -/
theorem feasible_iff {J : Type*} [Fintype J] (n : Nat) (budget : J -> Nat)
    (hpos : ∀ j, 1 ≤ budget j) :
    Feasible n budget ↔ n ≤ ∑ j, (budget j - 1) := by
  constructor
  · rintro ⟨M, cm, ft, h⟩
    letI := cm
    letI := ft
    obtain ⟨e, out, hbudget, hc⟩ := h
    have hg : Inference.Generated (id : Fin (n + 1) -> Fin (n + 1)) := by
      intro r; exact ⟨[r], by simp [Inference.eval]⟩
    have hl := Pooling.independent_height_of_injective e out id id hg
      (fun _ _ h => h) hc
    have hs : (∑ j, (Fintype.card (M j) - 1)) ≤
        ∑ j, (budget j - 1) := by
      apply Finset.sum_le_sum
      intro j hj
      exact Nat.sub_le_sub_right (hbudget j) 1
    simpa using hl.trans hs
  · intro hcap
    obtain ⟨B, hcover, hb⟩ := allocate_cuts n (fun j => budget j - 1) hcap
    let M : J -> Type := fun j => MeetCarrier (Fin ((B j).card + 1))
    let code : Fin (n + 1) -> ∀ j, M j :=
      fun r j => ⟨cutCode (B j) r⟩
    have hi : Injective code := by
      intro r s hrs
      apply cut_family_injective B hcover
      funext j
      exact congrArg (fun f => (f j).val) hrs
    have htop : code ⊤ = 1 := by
      funext j
      apply MeetCarrier.ext
      exact cutCode_top (B j)
    have hmeet : ∀ r s, code (r ⊓ s) = code r * code s := by
      intro r s
      funext j
      apply MeetCarrier.ext
      exact cutCode_inf (B j) r s
    refine ⟨M, (fun j => inferInstance), (fun j => inferInstance),
      code, decode code, ?_, ?_⟩
    · intro j
      have hj := hb j
      have hp := hpos j
      simp only [M, MeetCarrier.card, Fintype.card_fin]
      omega
    · intro s
      exact decoded_aggregate code hi htop hmeet s

/-- Uniform alphabets: the exact finite arithmetic characterization. -/
theorem uniform_feasible_iff (n b W : Nat) (hb : 1 ≤ b) :
    Feasible (J := Fin W) n (fun _ => b) ↔ n ≤ W * (b - 1) := by
  simpa [Finset.sum_const, Nat.mul_comm] using
    feasible_iff (J := Fin W) n (fun _ => b) (fun _ => hb)

/-- Integer ceiling division, without introducing real logarithms or rounding. -/
def ceilDiv (n d : Nat) : Nat := n / d + if n % d = 0 then 0 else 1

theorem ceilDiv_le_iff {n d W : Nat} (hd : 0 < d) :
    ceilDiv n d ≤ W ↔ n ≤ W * d := by
  have hdecomp := Nat.mod_add_div n d
  have hmod := Nat.mod_lt n hd
  unfold ceilDiv
  by_cases hz : n % d = 0
  · simp only [hz, if_pos, Nat.add_zero]
    constructor
    · intro h
      have hm := Nat.mul_le_mul_right d h
      nlinarith
    · intro h
      by_contra hn
      have hlt : W < n / d := by omega
      have hm := Nat.mul_le_mul_right d (Nat.succ_le_of_lt hlt)
      nlinarith
  · simp only [hz, if_false]
    have hp : 0 < n % d := Nat.pos_of_ne_zero hz
    constructor
    · intro h
      have hm := Nat.mul_le_mul_right d h
      nlinarith
    · intro h
      by_contra hn
      have hle : W ≤ n / d := by omega
      have hm := Nat.mul_le_mul_right d hle
      nlinarith

/-- Corollary 4, exact independent width for an `(n+1)`-state chain. -/
theorem independent_width_minimum (n b W : Nat) (hb : 2 ≤ b) :
    Feasible (J := Fin W) n (fun _ => b) ↔ ceilDiv n (b - 1) ≤ W := by
  rw [uniform_feasible_iff n b W (by omega)]
  exact (ceilDiv_le_iff (n := n) (d := b - 1) (W := W) (by omega)).symm

/-- The four-state example: two binary channels cannot preserve the chain. -/
theorem four_chain_not_two_binary :
    ¬ Feasible (J := Fin 2) 3 (fun _ => 2) := by
  rw [uniform_feasible_iff 3 2 2 (by omega)]
  omega

theorem four_chain_three_binary :
    Feasible (J := Fin 3) 3 (fun _ => 2) := by
  rw [uniform_feasible_iff 3 2 3 (by omega)]

end CutExchange
end NeuralArtifacts

end -- noncomputable section

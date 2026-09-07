import NeuralArtifacts.Measurability

/-!
# 23. A direct Borel projection proof for finite-dimensional neural constraints

We prove more than the finite-parameter statement without using real
quantifier elimination. Boolean combinations of finitely many continuous
real comparisons in a sigma-compact Hausdorff domain are sigma-compact,
and their continuous images are Borel in a Hausdorff Borel target.

This covers finite-dimensional affine/ReLU/hard-attention graph constraints,
including finitely many network copies used to form a finite-support loss.
It proves Borel regularity, not that a projection has a computable polynomial
quantifier-free description. That separate algorithmic issue is isolated in
RealAlgebraBoundary.
-/
noncomputable section
open Classical Function Set MeasureTheory
namespace NeuralArtifacts.Regularity

section SigmaOperations
variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem sigma_inter {A B : Set X} (hA : IsSigmaCompact A) (hB : IsSigmaCompact B) :
    IsSigmaCompact (A ∩ B) := by
  obtain ⟨K, hK, heK⟩ := hA
  obtain ⟨L, hL, heL⟩ := hB
  have hcompact (n m : Nat) : IsCompact (K n ∩ L m) :=
    (hK n).inter_right (hL m).isClosed
  have hs := isSigmaCompact_iUnion (fun n => iUnion (fun m => K n ∩ L m))
    (fun n => isSigmaCompact_iUnion_of_isCompact _ (hcompact n))
  convert hs using 1
  rw [<- heK, <- heL]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion]
  aesop

omit [T2Space X] in
theorem sigma_union {A B : Set X} (hA : IsSigmaCompact A) (hB : IsSigmaCompact B) :
    IsSigmaCompact (A ∪ B) := by
  have hs := isSigmaCompact_iUnion (fun b : Bool => if b then A else B)
    (by intro b; cases b <;> assumption)
  convert hs using 1
  ext x
  simp only [Set.mem_union, Set.mem_iUnion]
  constructor
  · rintro (h | h)
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  · rintro ⟨b, h⟩
    cases b
    · exact Or.inr h
    · exact Or.inl h

variable [SigmaCompactSpace X]

omit [T2Space X] in
theorem closed_sigma {A : Set X} (hA : IsClosed A) : IsSigmaCompact A :=
  isSigmaCompact_univ.of_isClosed_subset hA (Set.subset_univ _)

omit [T2Space X] in
/-- Strict inequalities are countable unions of closed separated inequalities. -/
theorem continuous_lt_sigma (f g : X -> Real) (hf : Continuous f) (hg : Continuous g) :
    IsSigmaCompact {x | f x < g x} := by
  let K : Nat -> Set X := fun n => {x | f x + 1 / ((n : Real) + 1) ≤ g x}
  have hc (n : Nat) : IsSigmaCompact (K n) :=
    closed_sigma (isClosed_le (hf.add continuous_const) hg)
  have he : {x | f x < g x} = iUnion K := by
    ext x
    constructor
    · intro hx
      have hd : 0 < g x - f x := sub_pos.mpr hx
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (g x - f x))
      have hmul : 1 < (n : Real) * (g x - f x) := (div_lt_iff₀ hd).mp hn
      apply Set.mem_iUnion.mpr
      refine ⟨n, ?_⟩
      change f x + 1 / ((n : Real) + 1) ≤ g x
      have hden : (0 : Real) < (n : Real) + 1 := by positivity
      have hfrac : 1 / ((n : Real) + 1) ≤ g x - f x := by
        apply (div_le_iff₀ hden).mpr
        nlinarith
      linarith
    · intro hx
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      have hpos : (0 : Real) < 1 / ((n : Real) + 1) := by positivity
      change f x + 1 / ((n : Real) + 1) ≤ g x at hn
      show f x < g x
      linarith
  rw [he]
  exact isSigmaCompact_iUnion K hc
end SigmaOperations

/-- Continuous scalar expressions may contain arbitrary continuous operations,
not only polynomials. Finite guarded graphs remain covered. -/
inductive Guard (X : Type*) [TopologicalSpace X] where
  | le (f g : X -> Real) (hf : Continuous f) (hg : Continuous g)
  | and (p q : Guard X)
  | or (p q : Guard X)
  | not (p : Guard X)

namespace Guard
variable {X : Type*} [TopologicalSpace X]

def holds : Guard X -> X -> Prop
  | le f g _ _, x => f x ≤ g x
  | and p q, x => holds p x ∧ holds q x
  | or p q, x => holds p x ∨ holds q x
  | not p, x => ¬ holds p x

def eq (f g : X -> Real) (hf : Continuous f) (hg : Continuous g) : Guard X :=
  and (le f g hf hg) (le g f hg hf)

def lt (f g : X -> Real) (hf : Continuous f) (hg : Continuous g) : Guard X :=
  not (le g f hg hf)

@[simp] theorem holds_eq (f g : X -> Real) (hf : Continuous f) (hg : Continuous g) (x : X) :
    holds (eq f g hf hg) x ↔ f x = g x := by simp [eq, holds, le_antisymm_iff]
@[simp] theorem holds_lt (f g : X -> Real) (hf : Continuous f) (hg : Continuous g) (x : X) :
    holds (lt f g hf hg) x ↔ f x < g x := by simp [lt, holds, not_le]

/-- Simultaneous induction is essential: arbitrary sigma-compact sets are not
closed under complement. The finite guard grammar supplies both directions. -/
theorem sigma_both [T2Space X] [SigmaCompactSpace X] (p : Guard X) :
    IsSigmaCompact {x | p.holds x} ∧ IsSigmaCompact {x | ¬ p.holds x} := by
  induction p with
  | le f g hf hg =>
    constructor
    · exact closed_sigma (isClosed_le hf hg)
    · simpa [holds, not_le] using continuous_lt_sigma g f hg hf
  | and p q ihp ihq =>
    constructor
    · exact sigma_inter ihp.1 ihq.1
    · have he : {x | ¬ (p.holds x ∧ q.holds x)} =
          {x | ¬ p.holds x} ∪ {x | ¬ q.holds x} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_union, not_and_or]
      rw [show {x | ¬ (Guard.and p q).holds x} = _ from he]
      exact sigma_union ihp.2 ihq.2
  | or p q ihp ihq =>
    constructor
    · exact sigma_union ihp.1 ihq.1
    · have he : {x | ¬ (p.holds x ∨ q.holds x)} =
          {x | ¬ p.holds x} ∩ {x | ¬ q.holds x} := by ext x; simp
      rw [show {x | ¬ (Guard.or p q).holds x} = _ from he]
      exact sigma_inter ihp.2 ihq.2
  | not p ih =>
    exact ⟨ih.2, by simpa [holds, not_not] using ih.1⟩
end Guard

/-- A countable union of compact sets is Borel in a Hausdorff Borel space. -/
theorem measurable_of_sigma {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] {S : Set Y} (hs : IsSigmaCompact S) :
    MeasurableSet S := by
  obtain ⟨K, hK, he⟩ := hs
  rw [<- he]
  exact MeasurableSet.iUnion (fun n => (hK n).measurableSet)

theorem projected_guard_borel {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [SigmaCompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    (p : Guard X) (projection : X -> Y) (hp : Continuous projection) :
    MeasurableSet (projection '' {x | p.holds x}) := by
  apply measurable_of_sigma
  exact IsSigmaCompact.image hp (p.sigma_both).1

/-- Parameters and finitely many intermediate activations are projected out.
No countability assumption is imposed on their real values. -/
theorem finite_dimensional_existential_borel (parameters vars samples : Nat)
    (p : Guard ((Fin parameters -> Real) ×
      (Fin vars -> Real) × (Fin samples -> Real))) :
    MeasurableSet {z : Fin samples -> Real |
      ∃ theta v, p.holds (theta, v, z)} := by
  have h := projected_guard_borel p (fun x => x.2.2) (continuous_snd.comp continuous_snd)
  convert h using 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨theta, v, hp⟩
    exact ⟨(theta, v, z), hp, rfl⟩
  · rintro ⟨⟨theta, v, z'⟩, hp, hz⟩
    have hz' : z' = z := hz
    subst hz'
    exact ⟨theta, v, hp⟩

/-- The graph of ReLU is represented by an explicit finite guard. -/
def reluGraph : Guard (Real × Real) :=
  Guard.or
    (Guard.and (Guard.le Prod.fst (fun _ => 0) continuous_fst continuous_const)
      (Guard.eq Prod.snd (fun _ => 0) continuous_snd continuous_const))
    (Guard.and (Guard.le (fun _ => 0) Prod.fst continuous_const continuous_fst)
      (Guard.eq Prod.snd Prod.fst continuous_snd continuous_fst))

theorem reluGraph_exact (x y : Real) : reluGraph.holds (x, y) ↔ y = Neural.relu x := by
  have hg : reluGraph.holds (x, y) ↔
      (x ≤ 0 ∧ y = 0) ∨ (0 ≤ x ∧ y = x) := by
    change ((x ≤ 0 ∧ (y ≤ 0 ∧ 0 ≤ y)) ∨
      (0 ≤ x ∧ (y ≤ x ∧ x ≤ y))) ↔ _
    simp only [<- le_antisymm_iff]
  rw [hg]
  by_cases hx : x ≤ 0
  · rw [Neural.relu_of_nonpos hx]
    constructor
    · rintro (⟨_, hy⟩ | ⟨hpos, hy⟩)
      · exact hy
      · have hzero : x = 0 := le_antisymm hx hpos
        exact hy.trans hzero
    · intro hy
      exact Or.inl ⟨hx, hy⟩
  · have hpos : 0 ≤ x := le_of_lt (lt_of_not_ge hx)
    rw [Neural.relu_of_nonneg hpos]
    constructor
    · rintro (⟨hneg, _⟩ | ⟨_, hy⟩)
      · exact False.elim (hx hneg)
      · exact hy
    · intro hy
      exact Or.inr ⟨hpos, hy⟩

end NeuralArtifacts.Regularity

end -- noncomputable section

import NeuralArtifacts.Observation

/-!
# 19. Query-relative experimentation and stored-evidence exchange
-/
noncomputable section
open Classical Function
namespace NeuralArtifacts.Queries
variable {C P Y T : Type*}
variable (D : C -> P -> Y) (query : C -> T) (truth : C)

def survive (V : Set C) (E : Set P) : Set C :=
  {c | c ∈ V ∧ ∀ e ∈ E, D c e = D truth e}

def bad (V : Set C) : Set C := {c | c ∈ V ∧ query c ≠ query truth}

def killed (e : P) : Set C := {c | D c e ≠ D truth e}

def Certifies (V : Set C) (E : Set P) : Prop :=
  ∀ c ∈ survive D truth V E, query c = query truth

def Covers (V : Set C) (E : Set P) : Prop :=
  ∀ c ∈ bad query truth V, ∃ e ∈ E, c ∈ killed D truth e

theorem truth_survives (V : Set C) (E : Set P) (h : truth ∈ V) :
    truth ∈ survive D truth V E := ⟨h, by intros; rfl⟩

theorem certificate_iff_cover (V : Set C) (E : Set P) :
    Certifies D query truth V E ↔ Covers D query truth V E := by
  constructor
  · intro hc c hbad
    by_contra hnone
    have heq : ∀ e ∈ E, D c e = D truth e := by
      intro e he
      by_contra hn
      exact hnone ⟨e, he, hn⟩
    exact hbad.2 (hc c ⟨hbad.1, heq⟩)
  · intro hcover c hc
    by_contra hquery
    obtain ⟨e, he, hk⟩ := hcover c ⟨hc.1, hquery⟩
    exact hk (hc.2 e he)

theorem surviving_bad_exact (V : Set C) (E : Set P) :
    bad query truth (survive D truth V E) =
      {c | c ∈ bad query truth V ∧ ¬ ∃ e ∈ E, c ∈ killed D truth e} := by
  ext c
  constructor
  · rintro ⟨ ⟨hV, hEq⟩, hQ⟩
    refine ⟨⟨hV, hQ⟩, ?_⟩
    rintro ⟨e, he, hne⟩
    exact hne (hEq e he)
  · rintro ⟨ ⟨hV, hQ⟩, hnot⟩
    refine ⟨⟨hV, ?_⟩, hQ⟩
    intro e he
    by_contra hne
    exact hnot ⟨e, he, hne⟩

/-- Stored and online evidence have exactly the same extensional update. -/
theorem evidence_exchange (V : Set C) (stored online : Set P) :
    survive D truth V (stored ∪ online) =
      survive D truth (survive D truth V stored) online := by
  ext c
  simp only [survive, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨hV, h⟩
    exact ⟨⟨hV, fun e he => h e (Or.inl he)⟩, fun e he => h e (Or.inr he)⟩
  · rintro ⟨ ⟨hV, hs⟩, ho⟩
    exact ⟨hV, fun e he => he.elim (hs e) (ho e)⟩

theorem stored_query_certificate (V : Set C) (stored online : Set P) :
    Certifies D query truth V (stored ∪ online) ↔
    Covers D query truth (survive D truth V stored) online := by
  rw [Certifies, evidence_exchange]
  exact certificate_iff_cover D query truth _ online

theorem certificate_monotone_store {V W : Set C} {E : Set P} (hWV : W ⊆ V)
    (h : Certifies D query truth V E) : Certifies D query truth W E := by
  intro c hc
  exact h c ⟨hWV hc.1, hc.2⟩

theorem certificate_monotone_evidence {V : Set C} {E F : Set P} (hEF : E ⊆ F)
    (h : Certifies D query truth V E) : Certifies D query truth V F := by
  intro c hc
  exact h c ⟨hc.1, fun e he => hc.2 e (hEF he)⟩

/-- Minimum query certificate and minimum set cover have literally identical
feasible cardinalities. No claim about adaptive policy optimality is hidden here. -/
theorem optimum_cardinality_iff [DecidableEq P] (V : Set C) (n : Nat) :
    (∃ E : Finset P, E.card ≤ n ∧ Certifies D query truth V (E : Set P)) ↔
    (∃ E : Finset P, E.card ≤ n ∧ Covers D query truth V (E : Set P)) := by
  simp only [certificate_iff_cover]

inductive Policy (P Y T : Type*) where
  | done (answer : T)
  | ask (probe : P) (next : Y -> Policy P Y T)

namespace Policy

def run (c : C) : Policy P Y T -> T
  | done t => t
  | ask e next => run c (next (D c e))

def probes (c : C) : Policy P Y T -> Set P
  | done _ => ∅
  | ask e next => {e} ∪ probes c (next (D c e))

/-- A matching transcript follows the same adaptive path. -/
theorem same_transcript (policy : Policy P Y T) (c : C)
    (h : ∀ e ∈ probes D truth policy, D c e = D truth e) :
    run D c policy = run D truth policy := by
  revert h
  induction policy with
  | done t =>
    intro h
    rfl
  | ask e next ih =>
    intro h
    have he : D c e = D truth e := h e (Or.inl (Set.mem_singleton e))
    simp only [run, he]
    apply ih (D truth e)
    intro p hp
    exact h p (Or.inr hp)
/-- Every correct adaptive policy has a covering certificate at each reached leaf. -/
theorem leaf_certificate (policy : Policy P Y T) (V : Set C)
    (htruth : truth ∈ V) (correct : ∀ c ∈ V, run D c policy = query c) :
    Covers D query truth V (probes D truth policy) := by
  apply (certificate_iff_cover D query truth V _).mp
  intro c hc
  rw [<- correct c hc.1, same_transcript D truth policy c hc.2, correct truth htruth]
end Policy

end NeuralArtifacts.Queries

end -- noncomputable section

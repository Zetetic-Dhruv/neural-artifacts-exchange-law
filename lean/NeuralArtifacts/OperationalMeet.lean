import NeuralArtifacts.Extraction

/-!
# 11. Recovering meet from the operational transition table

This is the converse to version-space compilation. The starting data are
only a reachable Moore machine and the commuting/idempotent equations of
its input transitions. No candidate model store is assumed.
-/
noncomputable section
open Classical Function
namespace NeuralArtifacts.OperationalMeet
universe u v w
variable {Q : Type u} {P : Type v} {Y : Type w}
variable (A : Moore Q P Y)

def Commutes : Prop :=
  ∀ q p r, A.step (A.step q p) r = A.step (A.step q r) p

def Idempotent : Prop := ∀ q p, A.step (A.step q p) p = A.step q p

def AllReachable : Prop := ∀ q, ∃ s, A.run s = q

theorem step_word_commute (hc : Commutes A) (q : Q) (p : P) (s : List P) :
    A.runFrom (A.step q p) s = A.step (A.runFrom q s) p := by
  induction s generalizing q with
  | nil => rfl
  | cons r s ih =>
    simp only [Moore.runFrom_cons]
    rw [hc q p r]
    exact ih (A.step q r)

theorem words_commute (hc : Commutes A) (q : Q) (s t : List P) :
    A.runFrom (A.runFrom q s) t = A.runFrom (A.runFrom q t) s := by
  induction s generalizing q with
  | nil => rfl
  | cons p s ih =>
    simp only [Moore.runFrom_cons]
    rw [ih, step_word_commute A hc]

theorem word_idempotent (hc : Commutes A) (hi : Idempotent A)
    (q : Q) (s : List P) :
    A.runFrom (A.runFrom q s) s = A.runFrom q s := by
  induction s generalizing q with
  | nil => rfl
  | cons p s ih =>
    simp only [Moore.runFrom_cons]
    rw [<- step_word_commute A hc, hi, ih]

/-- Equality at the initial state determines the entire word transformation. -/
theorem word_maps_ext (hc : Commutes A) (hr : AllReachable A)
    {s t : List P} (h : A.run s = A.run t) (q : Q) :
    A.runFrom q s = A.runFrom q t := by
  obtain ⟨u, hu⟩ := hr q
  rw [<- hu]
  change A.runFrom (A.runFrom A.initial u) s =
    A.runFrom (A.runFrom A.initial u) t
  calc
    A.runFrom (A.runFrom A.initial u) s =
        A.runFrom (A.runFrom A.initial s) u := words_commute A hc A.initial u s
    _ = A.runFrom (A.runFrom A.initial t) u :=
      congrArg (fun z => A.runFrom z u) h
    _ = A.runFrom (A.runFrom A.initial u) t :=
      (words_commute A hc A.initial u t).symm

def access (hr : AllReachable A) (q : Q) : List P := Classical.choose (hr q)

@[simp] theorem access_spec (hr : AllReachable A) (q : Q) :
    A.run (access A hr q) = q := Classical.choose_spec (hr q)

def meet (hr : AllReachable A) (q r : Q) : Q :=
  A.runFrom q (access A hr r)

theorem meet_from_any_word (hc : Commutes A) (hr : AllReachable A)
    {s : List P} {r : Q} (hs : A.run s = r) (q : Q) :
    meet A hr q r = A.runFrom q s := by
  apply word_maps_ext A hc hr
  exact (access_spec A hr r).trans hs.symm

theorem meet_run (hc : Commutes A) (hr : AllReachable A)
    (q : Q) (s : List P) : meet A hr q (A.run s) = A.runFrom q s :=
  meet_from_any_word A hc hr rfl q

theorem meet_comm (hc : Commutes A) (hr : AllReachable A) (q r : Q) :
    meet A hr q r = meet A hr r q := by
  change A.runFrom q (access A hr r) = A.runFrom r (access A hr q)
  conv_lhs => rw [<- access_spec A hr q]
  rw [Moore.run, words_commute A hc]
  rw [<- Moore.run, access_spec]

theorem meet_assoc (hc : Commutes A) (hr : AllReachable A) (q r z : Q) :
    meet A hr (meet A hr q r) z = meet A hr q (meet A hr r z) := by
  have hword : A.run (access A hr r ++ access A hr z) = meet A hr r z := by
    rw [Moore.run_append, access_spec]
    rfl
  rw [meet_from_any_word A hc hr hword]
  exact (A.runFrom_append q (access A hr r) (access A hr z)).symm

theorem meet_idem (hc : Commutes A) (hi : Idempotent A)
    (hr : AllReachable A) (q : Q) : meet A hr q q = q := by
  change A.runFrom q (access A hr q) = q
  calc
    A.runFrom q (access A hr q) =
        A.runFrom (A.run (access A hr q)) (access A hr q) := by
      rw [access_spec A hr q]
    _ = A.run (access A hr q) := word_idempotent A hc hi A.initial _
    _ = q := access_spec A hr q

theorem meet_initial (hc : Commutes A) (hr : AllReachable A) (q : Q) :
    meet A hr q A.initial = q := by
  exact meet_from_any_word A hc hr (s := []) rfl q

def recoveredLaws (hc : Commutes A) (hi : Idempotent A)
    (hr : AllReachable A) : MeetLaws Q where
  op := meet A hr
  assoc := meet_assoc A hc hr
  comm := meet_comm A hc hr
  idem := meet_idem A hc hi hr

@[reducible] def recoveredTop (hc : Commutes A) (hi : Idempotent A) (hr : AllReachable A) :
    letI := (recoveredLaws A hc hi hr).order
    OrderTop Q := by
  letI := (recoveredLaws A hc hi hr).order
  exact { top := A.initial, le_top := meet_initial A hc hr }

theorem transition_is_meet (hc : Commutes A) (hr : AllReachable A)
    (q : Q) (p : P) : A.step q p = meet A hr q (A.step A.initial p) := by
  exact (meet_from_any_word A hc hr (s := [p]) rfl q).symm

/-- Uniqueness includes the operation, not just the associated order.
Commutativity is needed only for existence (`meet_comm`/`meet_assoc`), not for
uniqueness. -/
theorem meet_unique (hr : AllReachable A)
    (L : MeetLaws Q) (hunit : ∀ q, L.op q A.initial = q)
    (hstep : ∀ q p, A.step q p = L.op q (A.step A.initial p)) :
    ∀ q r, L.op q r = meet A hr q r := by
  have aux : ∀ q s, A.runFrom q s = L.op q (A.run s) := by
    intro q s
    induction s using List.reverseRecOn with
    | nil => simpa [Moore.run] using (hunit q).symm
    | @append_singleton s p ih =>
      rw [A.runFrom_append, Moore.run_snoc]
      simp only [Moore.runFrom_cons, Moore.runFrom_nil]
      rw [ih, hstep, hstep (A.run s) p, L.assoc]
  intro q r
  have h := aux q (access A hr r)
  simpa [meet] using h.symm

section Ideals
variable [SemilatticeInf Q] [OrderTop Q]

def ideal (q : Q) : Set Q := {r | r ≤ q}

omit [OrderTop Q] in
theorem ideal_injective : Injective (ideal (Q := Q)) := by
  intro q r h
  apply le_antisymm
  · have hq : q ∈ ideal q := le_rfl
    rw [h] at hq
    exact hq
  · have hr : r ∈ ideal r := le_rfl
    rw [<- h] at hr
    exact hr

omit [OrderTop Q] in
@[simp] theorem ideal_inf (q r : Q) : ideal (q ⊓ r) = ideal q ∩ ideal r := by
  ext z
  exact le_inf_iff

@[simp] theorem ideal_top : ideal (⊤ : Q) = Set.univ := by
  ext q
  simp [ideal]

/-- The recovered states themselves provide a concrete version-space store. -/
theorem principal_ideal_realization (g : P -> Q) (s : List P) :
    VersionSpace.version (fun p => ideal (g p)) s = ideal (Inference.eval g s) := by
  induction s with
  | nil => simp [VersionSpace.version, Inference.eval]
  | cons p s ih => simp [VersionSpace.version, Inference.eval, ih]
end Ideals

/-- Observable permutation/idempotence laws force transition equations after
minimization. The suffix is quantified: a single current output is insufficient. -/
theorem commuting_of_behavior (hr : AllReachable A)
    (hminimal : ∀ q r, A.ObsEq q r -> q = r)
    (hswap : ∀ s p r t,
      A.out (A.run (s ++ [p, r] ++ t)) = A.out (A.run (s ++ [r, p] ++ t))) :
    Commutes A := by
  intro q p r
  obtain ⟨s, hs⟩ := hr q
  apply hminimal
  intro t
  simpa [Moore.run_append, Moore.runFrom, hs] using hswap s p r t

theorem idempotent_of_behavior (hr : AllReachable A)
    (hminimal : ∀ q r, A.ObsEq q r -> q = r)
    (hrepeat : ∀ s p t,
      A.out (A.run (s ++ [p, p] ++ t)) = A.out (A.run (s ++ [p] ++ t))) :
    Idempotent A := by
  intro q p
  obtain ⟨s, hs⟩ := hr q
  apply hminimal
  intro t
  simpa [Moore.run_append, Moore.runFrom, hs] using hrepeat s p t

/-- Conversely the operational equations imply the observable exchange laws. -/
theorem behavior_swap (hc : Commutes A) (s : List P) (p r : P) (t : List P) :
    A.out (A.run (s ++ [p, r] ++ t)) = A.out (A.run (s ++ [r, p] ++ t)) := by
  simp only [Moore.run_append, Moore.runFrom_cons, Moore.runFrom_nil]
  rw [hc]

theorem behavior_repeat (hi : Idempotent A) (s : List P) (p : P) (t : List P) :
    A.out (A.run (s ++ [p, p] ++ t)) = A.out (A.run (s ++ [p] ++ t)) := by
  simp only [Moore.run_append, Moore.runFrom_cons, Moore.runFrom_nil]
  rw [hi]

end NeuralArtifacts.OperationalMeet

end -- noncomputable section

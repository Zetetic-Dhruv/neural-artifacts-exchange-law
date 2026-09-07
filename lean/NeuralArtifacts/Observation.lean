import NeuralArtifacts.Inference

/-!
# 18. Observation-relative identification and sound exchange of constraints
-/
noncomputable section
open Classical Function
namespace NeuralArtifacts

namespace Observation
variable {Theta O A T : Type*}

def fibre (obs : Theta -> O) (theta : Theta) : Set Theta :=
  {theta' | obs theta' = obs theta}

def Recoverable (obs : Theta -> O) (target : Theta -> T) : Prop :=
  ∃ read : O -> T, ∀ theta, read (obs theta) = target theta

def FibreConstant (obs : Theta -> O) (target : Theta -> T) : Prop :=
  ∀ x y, obs x = obs y -> target x = target y

theorem recoverable_iff [Nonempty T] (obs : Theta -> O) (target : Theta -> T) :
    Recoverable obs target ↔ FibreConstant obs target := by
  constructor
  · rintro ⟨read, hread⟩ x y hxy
    rw [<- hread x, <- hread y, hxy]
  · intro h
    let read : O -> T := fun o =>
      if ho : ∃ theta, obs theta = o then target (Classical.choose ho)
      else Classical.choice inferInstance
    refine ⟨read, ?_⟩
    intro theta
    dsimp [read]
    rw [dif_pos ⟨theta, rfl⟩]
    apply h
    exact Classical.choose_spec (show ∃ x, obs x = obs theta from ⟨theta, rfl⟩)

/-- Exact condition for a new artifact channel to overcome a behavioral ambiguity. -/
theorem artifact_identifies_iff [Nonempty T] (behavior : Theta -> O)
    (artifact : Theta -> A) (target : Theta -> T) :
    Recoverable (fun theta => (behavior theta, artifact theta)) target ↔
      ∀ x y, behavior x = behavior y -> artifact x = artifact y -> target x = target y := by
  rw [recoverable_iff]
  simp only [FibreConstant, Prod.mk.injEq]
  constructor
  · intro h x y hb ha; exact h x y ⟨hb, ha⟩
  · intro h x y hxy; exact h x y hxy.1 hxy.2

theorem dark_pair_obstruction (obs : Theta -> O) (target : Theta -> T)
    (x y : Theta) (ho : obs x = obs y) (ht : target x ≠ target y) :
    ¬ Recoverable obs target := by
  rintro ⟨read, hr⟩
  apply ht
  rw [<- hr x, <- hr y, ho]

theorem necessary_artifact_separation (behavior : Theta -> O) (artifact : Theta -> A)
    (target : Theta -> T) (hr : Recoverable (fun x => (behavior x, artifact x)) target)
    (x y : Theta) (hb : behavior x = behavior y) (ht : target x ≠ target y) :
    artifact x ≠ artifact y := by
  intro ha
  obtain ⟨read, hread⟩ := hr
  apply ht
  rw [<- hread x, <- hread y]
  simp only [hb, ha]

theorem coarsening_enlarges (fine : Theta -> A) (coarsen : A -> O) (theta : Theta) :
    fibre fine theta ⊆ fibre (coarsen ∘ fine) theta := by
  intro x hx
  exact congrArg coarsen hx

theorem added_channel_refines (behavior : Theta -> O) (artifact : Theta -> A)
    (theta : Theta) : fibre (fun x => (behavior x, artifact x)) theta ⊆ fibre behavior theta := by
  intro x hx
  exact congrArg Prod.fst hx

/-- A parameter symmetry is compatible with a semantic target exactly when
that target is constant on the symmetry orbits. This lemma supplies the
necessary direction without choosing neuron numberings. -/
theorem invariant_target_of_invariant_observation (obs : Theta -> O)
    (target : Theta -> T) (hr : Recoverable obs target)
    (symmetry : Theta -> Theta) (hs : ∀ theta, obs (symmetry theta) = obs theta) :
    ∀ theta, target (symmetry theta) = target theta := by
  obtain ⟨read, hread⟩ := hr
  intro theta
  rw [<- hread (symmetry theta), <- hread theta, hs]
end Observation

namespace Reduction
variable {C : Type*}

/-- A sound representable overapproximation, with no independence assumption. -/
structure Closure (C : Type*) where
  close : Set C -> Set C
  extensive : ∀ V, V ⊆ close V
  monotone : ∀ U V, U ⊆ V -> close U ⊆ close V
  idempotent : ∀ V, close (close V) = close V

def Closed (cl : Closure C) (A : Set C) : Prop := cl.close A = A

def reduce (cs cm : Closure C) (A G : Set C) : Set C × Set C :=
  (cs.close (A ∩ G), cm.close (A ∩ G))

theorem reduced_component_le (cs cm : Closure C) (A G : Set C)
    (hA : Closed cs A) (hG : Closed cm G) :
    (reduce cs cm A G).1 ⊆ A ∧ (reduce cs cm A G).2 ⊆ G := by
  constructor
  · have h := cs.monotone (A ∩ G) A Set.inter_subset_left
    have hA' : cs.close A = A := hA
    rw [hA'] at h
    simpa [reduce] using h
  · have h := cm.monotone (A ∩ G) G Set.inter_subset_right
    have hG' : cm.close G = G := hG
    rw [hG'] at h
    simpa [reduce] using h

theorem reduced_meaning (cs cm : Closure C) (A G : Set C)
    (hA : Closed cs A) (hG : Closed cm G) :
    (reduce cs cm A G).1 ∩ (reduce cs cm A G).2 = A ∩ G := by
  apply Set.Subset.antisymm
  · exact Set.inter_subset_inter (reduced_component_le cs cm A G hA hG).1
      (reduced_component_le cs cm A G hA hG).2
  · intro c hc
    exact ⟨cs.extensive _ hc, cm.extensive _ hc⟩

theorem reduced_closed (cs cm : Closure C) (A G : Set C) :
    Closed cs (reduce cs cm A G).1 ∧ Closed cm (reduce cs cm A G).2 :=
  ⟨cs.idempotent _, cm.idempotent _⟩

theorem reduction_idempotent (cs cm : Closure C) (A G : Set C)
    (hA : Closed cs A) (hG : Closed cm G) :
    reduce cs cm (reduce cs cm A G).1 (reduce cs cm A G).2 = reduce cs cm A G := by
  unfold reduce
  rw [show cs.close (A ∩ G) ∩ cm.close (A ∩ G) = A ∩ G from
    reduced_meaning cs cm A G hA hG]

/-- Constructing the closure from an intersection-closed representable family. -/
def representableHull (family : Set (Set C)) (V : Set C) : Set C :=
  Set.sInter {A | A ∈ family ∧ V ⊆ A}

theorem hull_extensive (family : Set (Set C)) (V : Set C) : V ⊆ representableHull family V := by
  intro c hc
  apply Set.mem_sInter.mpr
  intro A hA
  exact hA.2 hc

theorem hull_monotone (family : Set (Set C)) {U V : Set C} (h : U ⊆ V) :
    representableHull family U ⊆ representableHull family V := by
  intro c hc
  apply Set.mem_sInter.mpr
  intro A hA
  exact Set.mem_sInter.mp hc A ⟨hA.1, h.trans hA.2⟩

theorem hull_fixed (family : Set (Set C)) {A : Set C} (hA : A ∈ family) :
    representableHull family A = A := by
  apply Set.Subset.antisymm
  · intro c hc; exact Set.mem_sInter.mp hc A ⟨hA, Set.Subset.refl _⟩
  · exact hull_extensive family A

def closureOfFamily (family : Set (Set C))
    (hinter : ∀ subfamily : Set (Set C), subfamily ⊆ family -> Set.sInter subfamily ∈ family) :
    Closure C where
  close := representableHull family
  extensive := hull_extensive family
  monotone := fun _ _ h => hull_monotone family h
  idempotent _ := hull_fixed family (hinter _ (fun _ hA => hA.1))

end Reduction
end NeuralArtifacts

end -- noncomputable section

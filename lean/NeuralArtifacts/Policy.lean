import NeuralArtifacts.MindChange
import NeuralArtifacts.CoupledWidth

/-!
# 30. Adaptive experiments on a pooled memory

A policy whose persistent state is the pooled outcome of its experiments has an
inference state that depends only on the set of outcomes received. Successive
states descend, so the number of experiments that move the state along a branch
is bounded by the chain height of the state, hence by the pooled channel
heights, and on a coupled memory by the number of codes. The chain
constructions, read as policies that eliminate one boundary per experiment,
attain both bounds.
-/

noncomputable section
open Classical Function
open scoped BigOperators
namespace NeuralArtifacts
namespace Policy
universe u v w

section Pooled
variable {R : Type u} [SemilatticeInf R] [OrderTop R]
variable {P : Type v} {Y : Type w}

/-- Evaluation is the finite meet over the observations received. -/
theorem eval_eq_finset_inf [DecidableEq P] (g : P -> R) (s : List P) :
    Inference.eval g s = s.toFinset.inf g := by
  induction s with
  | nil => simp
  | cons p t ih => simp [ih, List.toFinset_cons, Finset.inf_insert]

/-- The evaluated state depends only on the set of outcomes received, not on
their order or on repetitions. -/
theorem eval_toFinset [DecidableEq P] (g : P -> R) {s t : List P}
    (h : s.toFinset = t.toFinset) : Inference.eval g s = Inference.eval g t := by
  rw [eval_eq_finset_inf, eval_eq_finset_inf, h]

/-- The semantic state of the policy after the first `i` experiments. -/
def semState (rho : R -> Y) (g : P -> R) (s : List P) (i : Nat) : Inference.State rho :=
  MindChange.semState rho g s i

/-- At the end of the history the semantic state is the state of the whole
history. -/
theorem semState_length (rho : R -> Y) (g : P -> R) (s : List P) :
    semState rho g s s.length = Inference.mk rho (Inference.eval g s) := by
  simp [semState, MindChange.semState]

/-- The number of prefixes of `s` at which the semantic state strictly
descends: the experiments that change the state. -/
def descents (rho : R -> Y) (g : P -> R) (s : List P) : Nat :=
  MindChange.descentCount (semState rho g s) s.length

/-- The number of state-changing experiments along a history is bounded by the
chain height of the inference state. -/
theorem changes_le_height [Fintype R] (rho : R -> Y) (g : P -> R) (s : List P) :
    descents rho g s ≤ FiniteOrder.height (Inference.State rho) - 1 :=
  MindChange.descentCount_le_height _ (MindChange.semState_antitone rho g s) _

/-- A memory with finitely many states affords one state-changing experiment
per state beyond the first. -/
theorem changes_le_card [Fintype R] {M : Type*} [CommMonoid M] [Fintype M]
    (e : P -> M) (out : M -> Y) (g : P -> R) (rho : R -> Y)
    (hg : Inference.Generated g)
    (hc : ∀ s, out (Pooling.aggregate e s) = rho (Inference.eval g s)) (s : List P) :
    descents rho g s ≤ Fintype.card M - 1 := by
  have h1 := changes_le_height rho g s
  have h2 : FiniteOrder.height (Inference.State rho)
      ≤ Fintype.card (Inference.State rho) := FiniteOrder.height_le_card
  have h3 : Fintype.card (Inference.State rho) ≤ Fintype.card M :=
    Inference.cardinal_lower_bound (Pooling.machine e out) g rho hg
      (by intro u; simpa using hc u)
  omega

/-- A coupled `W`-coordinate `b`-value memory affords at most `b ^ W - 1`
state-changing experiments, under any commutative pooling operation. -/
theorem changes_le_coupled [Fintype R] {b W : Nat}
    (cm : CommMonoid (Fin W -> Fin b))
    (e : P -> (Fin W -> Fin b)) (out : (Fin W -> Fin b) -> Y)
    (g : P -> R) (rho : R -> Y) (hg : Inference.Generated g)
    (hc : letI := cm
      ∀ s, out (Pooling.aggregate e s) = rho (Inference.eval g s))
    (s : List P) : descents rho g s ≤ b ^ W - 1 := by
  letI := cm
  have h := changes_le_card e out g rho hg hc s
  simpa [Fintype.card_fun] using h

section Independent
variable {J : Type*} [Fintype J]
variable {Channels : J -> Type*}
variable [∀ j, CommMonoid (Channels j)] [∀ j, Fintype (Channels j)]
variable [Fintype R]

/-- On an independently pooled memory the number of state-changing experiments
is bounded by the sum of the channel idempotent heights. -/
theorem changes_le_channels (e : P -> ∀ j, Channels j)
    (out : (∀ j, Channels j) -> Y) (g : P -> R) (rho : R -> Y)
    (hg : Inference.Generated g)
    (hc : ∀ s, out (Pooling.aggregate e s) = rho (Inference.eval g s)) (s : List P) :
    descents rho g s ≤ ∑ j, (FiniteOrder.height (FiniteMonoid.Idem (Channels j)) - 1) :=
  le_trans (changes_le_height rho g s) (Pooling.independent_height e out g rho hg hc)

/-- Adaptive experiments on a pooled memory: the state depends only on the set
of outcomes received, and the experiments that move it are bounded by the chain
height of the state and by the pooled channel heights. -/
theorem adaptive_experiments [DecidableEq P] (e : P -> ∀ j, Channels j)
    (out : (∀ j, Channels j) -> Y) (g : P -> R) (rho : R -> Y)
    (hg : Inference.Generated g)
    (hc : ∀ s, out (Pooling.aggregate e s) = rho (Inference.eval g s)) :
    (∀ s t : List P, s.toFinset = t.toFinset ->
        Inference.eval g s = Inference.eval g t) ∧
      ∀ s : List P,
        descents rho g s ≤ FiniteOrder.height (Inference.State rho) - 1 ∧
        descents rho g s ≤
          ∑ j, (FiniteOrder.height (FiniteMonoid.Idem (Channels j)) - 1) :=
  ⟨fun _ _ h => eval_toFinset g h,
    fun s => ⟨changes_le_height rho g s, changes_le_channels e out g rho hg hc s⟩⟩
end Independent
end Pooled

section Chain

/-- The state of the chain policy after `i` experiments. -/
def chainState (n i : Nat) : Fin (n + 1) := ⟨n - i, by omega⟩

/-- The `i`-th experiment of the chain policy: it cuts one further boundary. -/
def chainObs (n i : Nat) : Fin (n + 1) := ⟨n - 1 - i, by omega⟩

/-- The chain policy presents the `n` boundaries in order. -/
def chainHistory (n : Nat) : List (Fin (n + 1)) := (List.range n).map (chainObs n)

@[simp] theorem chainHistory_length (n : Nat) : (chainHistory n).length = n := by
  simp [chainHistory]

theorem chainState_zero (n : Nat) : chainState n 0 = ⊤ := by
  apply Fin.ext
  simp [chainState, Fin.top_eq_last]

theorem chain_eval_range (n : Nat) : ∀ i, i ≤ n ->
    Inference.eval id ((List.range i).map (chainObs n)) = chainState n i := by
  intro i
  induction i with
  | zero => intro _; simpa using (chainState_zero n).symm
  | succ i ih =>
    intro h
    have h1 : Inference.eval (id : Fin (n + 1) -> Fin (n + 1))
        (List.map (chainObs n) [i]) = chainObs n i := by simp
    rw [List.range_succ, List.map_append, Inference.eval_append, ih (by omega), h1]
    have hle : chainObs n i ≤ chainState n i :=
      Fin.le_def.mpr (by simp only [chainObs, chainState]; omega)
    rw [inf_eq_right.mpr hle]
    apply Fin.ext
    simp only [chainObs, chainState]
    omega

theorem chain_eval_take (n i : Nat) (h : i ≤ n) :
    Inference.eval id ((chainHistory n).take i) = chainState n i := by
  rw [chainHistory, <- List.map_take, List.take_range, min_eq_left h]
  exact chain_eval_range n i h

theorem chain_mk_injective (n : Nat) :
    Injective (Inference.mk (id : Fin (n + 1) -> Fin (n + 1))) := by
  intro a b h
  exact (Inference.eqv_iff_eq_of_injective id injective_id a b).mp
    ((Inference.mk_eq_mk _ a b).mp h)

theorem chain_descent (n i : Nat) (h : i < n) :
    MindChange.semState (id : Fin (n + 1) -> Fin (n + 1)) id (chainHistory n) (i + 1)
      < MindChange.semState id id (chainHistory n) i := by
  refine lt_of_le_of_ne (MindChange.semState_antitone _ _ _ i) ?_
  intro he
  have h1 : Inference.eval (id : Fin (n + 1) -> Fin (n + 1)) ((chainHistory n).take (i + 1))
      = Inference.eval id ((chainHistory n).take i) := chain_mk_injective n he
  rw [chain_eval_take n (i + 1) (by omega), chain_eval_take n i (by omega)] at h1
  have h2 := congrArg Fin.val h1
  simp only [chainState] at h2
  omega

/-- Every experiment of the chain policy moves the state. -/
theorem chain_descents (n : Nat) :
    descents (id : Fin (n + 1) -> Fin (n + 1)) id (chainHistory n) = n := by
  have hlen : (chainHistory n).length = n := chainHistory_length n
  unfold descents
  rw [hlen]
  exact MindChange.descentCount_eq _ n (fun i hi => chain_descent n i hi)

/-- Attainment of the independent bound: with a tight channel budget the chain
policy makes one informative experiment for every channel rung. -/
theorem chain_attains_channel_bound {J : Type*} [Fintype J] (n : Nat) (budget : J -> Nat)
    (hpos : ∀ j, 1 ≤ budget j) (htight : n = ∑ j, (budget j - 1)) :
    CutExchange.Feasible n budget ∧
      descents (id : Fin (n + 1) -> Fin (n + 1)) id (chainHistory n)
        = ∑ j, (budget j - 1) :=
  ⟨(CutExchange.feasible_iff n budget hpos).mpr (le_of_eq htight),
    (chain_descents n).trans htight⟩

/-- Attainment of the coupled bound: when the chain fills the coordinate box
the chain policy makes `b ^ W - 1` informative experiments. -/
theorem chain_attains_coupled_bound (n b W : Nat) (hexact : n + 1 = b ^ W) :
    CoupledWidth.Feasible n b W ∧
      descents (id : Fin (n + 1) -> Fin (n + 1)) id (chainHistory n) = b ^ W - 1 :=
  ⟨(CoupledWidth.feasible_iff n b W).mpr (le_of_eq hexact),
    by rw [chain_descents n]; omega⟩
end Chain

end Policy
end NeuralArtifacts

end -- noncomputable section

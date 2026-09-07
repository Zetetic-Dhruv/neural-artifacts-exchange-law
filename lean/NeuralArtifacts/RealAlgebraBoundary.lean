import NeuralArtifacts.GuardedNetworks
import NeuralArtifacts.Extraction

/-!
# 25. Rational polynomial syntax and the external real-algebra backend

Dependency boundary, not a new axiom:
The paper cites real quantifier elimination for its *effective decision*
claim. This file specifies that classical backend as an explicit argument.
It supplies all application proofs, including a sound and complete closed
formula checker once the backend is provided. It does not fabricate an
instance of quantifier elimination or call Classical.propDecidable an
executable decision procedure.

The preceding GuardedProjection and GuardedNetworks files prove the Borel
claim without this backend. No exchange, extraction, neural, hardening,
causal, or information theorem imports a QEBackend instance.
-/
noncomputable section
open Classical Function
namespace NeuralArtifacts.RealAlgebra

inductive Expr (n : Nat) where
  | const (q : Rat)
  | var (i : Fin n)
  | add (a b : Expr n)
  | mul (a b : Expr n)
  | neg (a : Expr n)

namespace Expr
variable {n : Nat}

def evalReal (x : Fin n -> Real) : Expr n -> Real
  | const q => q
  | var i => x i
  | add a b => evalReal x a + evalReal x b
  | mul a b => evalReal x a * evalReal x b
  | neg a => -evalReal x a

def evalRat (x : Fin n -> Rat) : Expr n -> Rat
  | const q => q
  | var i => x i
  | add a b => evalRat x a + evalRat x b
  | mul a b => evalRat x a * evalRat x b
  | neg a => -evalRat x a

theorem eval_cast (e : Expr n) (x : Fin n -> Rat) :
    e.evalReal (fun i => (x i : Real)) = (e.evalRat x : Real) := by
  induction e <;> simp_all [evalReal, evalRat]

theorem continuous_eval (e : Expr n) : Continuous (fun x => e.evalReal x) := by
  induction e with
  | const q => exact continuous_const
  | var i => exact continuous_apply i
  | add a b ha hb => exact ha.add hb
  | mul a b ha hb => exact ha.mul hb
  | neg a ha => exact ha.neg
end Expr

inductive QF (n : Nat) where
  | le (a b : Expr n)
  | and (p q : QF n)
  | not (p : QF n)

namespace QF
variable {n : Nat}

def holdsReal (x : Fin n -> Real) : QF n -> Prop
  | le a b => a.evalReal x ≤ b.evalReal x
  | and p q => holdsReal x p ∧ holdsReal x q
  | not p => ¬ holdsReal x p

def holdsRat (x : Fin n -> Rat) : QF n -> Prop
  | le a b => a.evalRat x ≤ b.evalRat x
  | and p q => holdsRat x p ∧ holdsRat x q
  | not p => ¬ holdsRat x p

/-- This evaluator is genuinely rational arithmetic and structural recursion. -/
def check (x : Fin n -> Rat) : QF n -> Bool
  | le a b => decide (a.evalRat x ≤ b.evalRat x)
  | and p q => check x p && check x q
  | not p => !(check x p)

theorem check_correct (q : QF n) (x : Fin n -> Rat) :
    q.check x = true ↔ q.holdsRat x := by
  induction q <;> simp_all [check, holdsRat, Bool.eq_false_iff]

theorem rational_compatibility (q : QF n) (x : Fin n -> Rat) :
    q.holdsReal (fun i => (x i : Real)) ↔ q.holdsRat x := by
  induction q with
  | le a b =>
    simp only [holdsReal, holdsRat, Expr.eval_cast]
    exact_mod_cast (Iff.rfl : a.evalRat x ≤ b.evalRat x ↔ a.evalRat x ≤ b.evalRat x)
  | and p q hp hq => simp_all [holdsReal, holdsRat]
  | not p hp => simp_all [holdsReal, holdsRat]

def guard : QF n -> Regularity.Guard (Fin n -> Real)
  | le a b => Regularity.Guard.le a.evalReal b.evalReal a.continuous_eval b.continuous_eval
  | and p q => Regularity.Guard.and p.guard q.guard
  | not p => Regularity.Guard.not p.guard

theorem guard_exact (q : QF n) (x : Fin n -> Real) :
    q.guard.holds x ↔ q.holdsReal x := by
  induction q <;> simp_all [guard, Regularity.Guard.holds, holdsReal]
end QF

inductive Formula : Nat -> Type where
  | atomic {n : Nat} (q : QF n) : Formula n
  | and {n : Nat} (p q : Formula n) : Formula n
  | not {n : Nat} (p : Formula n) : Formula n
  | existsReal {n : Nat} (p : Formula (n + 1)) : Formula n

namespace Formula

def holds : {n : Nat} -> Formula n -> (Fin n -> Real) -> Prop
  | _, atomic q, x => q.holdsReal x
  | _, and p q, x => p.holds x ∧ q.holds x
  | _, not p, x => ¬ p.holds x
  | _, existsReal p, x => ∃ y : Real, p.holds (Fin.cons y x)
end Formula

/-- The classical real-closed-field quantifier-elimination theorem, supplied
as a certified algorithm. No inhabitant of this record is postulated here. -/
structure QEBackend where
  eliminate : {n : Nat} -> Formula n -> QF n
  correct : ∀ {n : Nat} (f : Formula n) (x : Fin n -> Real),
    (eliminate f).holdsReal x ↔ f.holds x

def closedCheck (backend : QEBackend) (f : Formula 0) : Bool :=
  (backend.eliminate f).check Fin.elim0

theorem closedCheck_correct (backend : QEBackend) (f : Formula 0) :
    closedCheck backend f = true ↔ f.holds Fin.elim0 := by
  have hx : (fun i : Fin 0 => ((Fin.elim0 i : Rat) : Real)) = Fin.elim0 :=
    funext (fun i => i.elim0)
  rw [closedCheck, QF.check_correct]
  rw [<- QF.rational_compatibility, hx]
  exact backend.correct f Fin.elim0

/-- The exact projection conclusion cited in the paper, with the imported
classical backend visible in its type. -/
theorem existential_has_quantifier_free_description (backend : QEBackend)
    {n : Nat} (q : QF (n + 1)) :
    ∃ r : QF n, ∀ x,
      r.holdsReal x ↔ ∃ y : Real, q.holdsReal (Fin.cons y x) := by
  refine ⟨backend.eliminate (Formula.existsReal (Formula.atomic q)), ?_⟩
  intro x
  exact backend.correct _ x

/-- Finitely many closed verification conditions are checked simultaneously. -/
def checkAll (backend : QEBackend) (conditions : List (Formula 0)) : Bool :=
  conditions.all (closedCheck backend)

theorem checkAll_correct (backend : QEBackend) (conditions : List (Formula 0)) :
    checkAll backend conditions = true ↔ ∀ f ∈ conditions, f.holds Fin.elim0 := by
  simp [checkAll, List.all_eq_true, closedCheck_correct]

/-- Any externally generated region obligations become kernel-level facts
through the backend's correctness proof; no untrusted Boolean is accepted. -/
theorem checked_obligation (backend : QEBackend) (conditions : List (Formula 0))
    (hcheck : checkAll backend conditions = true) (f : Formula 0) (hf : f ∈ conditions) :
    f.holds Fin.elim0 := (checkAll_correct backend conditions).mp hcheck f hf

/-- A supplied rational sum-of-squares identity is directly certified without
quantifier elimination. This is useful for concrete nonlinear region checks. -/
theorem polynomial_sos_nonnegative {n : Nat} (p : Expr n) (terms : List (Expr n))
    (identity : ∀ x, p.evalReal x = (terms.map (fun q => (q.evalReal x) ^ 2)).sum) :
    ∀ x, 0 ≤ p.evalReal x := by
  intro x
  rw [identity x]
  apply List.sum_nonneg
  intro y hy
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
  exact sq_nonneg _

end NeuralArtifacts.RealAlgebra

end -- noncomputable section

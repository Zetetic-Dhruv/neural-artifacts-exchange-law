import NeuralArtifacts.Attention

/-!
# 14. Exact symbol-level hardening, same-symbol ties, and perturbations

No limit as temperature tends to zero is assumed. The central condition is
an inequality on total wrong-symbol mass at the actual positive temperature.
-/
noncomputable section
open Classical Function
open scoped BigOperators
namespace NeuralArtifacts.Neural

structure Probability (I : Type*) [Fintype I] where
  weight : I -> Real
  nonneg : ∀ i, 0 ≤ weight i
  total : (∑ i, weight i) = 1

namespace Probability
variable {I S : Type*} [Fintype I] [DecidableEq S]

def coord (p : Probability I) (label : I -> S) (s : S) : Real :=
  ∑ i, if label i = s then p.weight i else 0

def wrong (p : Probability I) (label : I -> S) (target : S) : Real :=
  ∑ i, if label i ≠ target then p.weight i else 0

theorem coord_nonneg (p : Probability I) (label : I -> S) (s : S) :
    0 ≤ p.coord label s := by
  apply Finset.sum_nonneg
  intro i hi
  split_ifs <;> first | exact p.nonneg i | exact le_rfl

theorem wrong_nonneg (p : Probability I) (label : I -> S) (s : S) :
    0 ≤ p.wrong label s := by
  apply Finset.sum_nonneg
  intro i hi
  split_ifs <;> first | exact p.nonneg i | exact le_rfl

theorem coord_add_wrong (p : Probability I) (label : I -> S) (s : S) :
    p.coord label s + p.wrong label s = 1 := by
  rw [coord, wrong, <- Finset.sum_add_distrib, <- p.total]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : label i = s <;> simp [h]

theorem coord_le_one (p : Probability I) (label : I -> S) (s : S) :
    p.coord label s ≤ 1 := by
  have he := p.coord_add_wrong label s
  have hp := p.wrong_nonneg label s
  linarith

theorem coord_other_le_wrong (p : Probability I) (label : I -> S)
    {s t : S} (h : s ≠ t) : p.coord label s ≤ p.wrong label t := by
  apply Finset.sum_le_sum
  intro i hi
  by_cases hs : label i = s
  · simp [hs, h]
  · simp only [hs, if_false]
    split_ifs <;> first | exact p.nonneg i | exact le_rfl

theorem mixture_eq_coord (p : Probability I) (label : I -> S) (s : S) :
    (∑ i, p.weight i * oneHot (label i) s) = p.coord label s := by
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : label i = s
  · simp [oneHot, h]
  · simp [oneHot, h, Ne.symm h]

theorem uniform_label_wrong_zero (p : Probability I) (label : I -> S) (s : S)
    (h : ∀ i, label i = s) : p.wrong label s = 0 := by simp [wrong, h]
end Probability

/-- Saturating two-ReLU correction, defined on all real inputs. -/
def roundSymbol (eta t : Real) : Real :=
  (relu (t - eta) - relu (t - 1 + eta)) / (1 - 2 * eta)

section Correction
variable {eta : Real} (he0 : 0 ≤ eta) (he : eta < 1 / 2)

include he0 he

omit he0 in
theorem round_low {t : Real} (ht : t ≤ eta) : roundSymbol eta t = 0 := by
  have h1 : t - eta ≤ 0 := by linarith
  have h2 : t - 1 + eta ≤ 0 := by linarith
  simp [roundSymbol, relu_of_nonpos h1, relu_of_nonpos h2]

omit he0 in
theorem round_high {t : Real} (ht : 1 - eta ≤ t) : roundSymbol eta t = 1 := by
  have h1 : 0 ≤ t - eta := by linarith
  have h2 : 0 ≤ t - 1 + eta := by linarith
  have hd : 1 - 2 * eta ≠ 0 := by linarith
  rw [roundSymbol, relu_of_nonneg h1, relu_of_nonneg h2]
  have hnum : t - eta - (t - 1 + eta) = 1 - 2 * eta := by ring
  rw [hnum, div_self hd]

omit he0 he in
theorem round_mid {t : Real} (hl : eta ≤ t) (hh : t ≤ 1 - eta) :
    roundSymbol eta t = (t - eta) / (1 - 2 * eta) := by
  simp [roundSymbol, relu_of_nonneg (by linarith : 0 ≤ t - eta),
    relu_of_nonpos (by linarith : t - 1 + eta ≤ 0)]

omit he0 in
theorem round_eq_zero_iff (t : Real) : roundSymbol eta t = 0 ↔ t ≤ eta := by
  constructor
  · intro h
    by_contra hn
    have hl : eta < t := lt_of_not_ge hn
    by_cases hh : 1 - eta ≤ t
    · rw [round_high he hh] at h
      norm_num at h
    · have hr := round_mid hl.le (le_of_not_ge hh)
      rw [hr] at h
      have hp : 0 < (t - eta) / (1 - 2 * eta) := div_pos (by linarith) (by linarith)
      linarith
  · exact round_low he

omit he0 in
theorem round_eq_one_iff (t : Real) : roundSymbol eta t = 1 ↔ 1 - eta ≤ t := by
  constructor
  · intro h
    by_contra hn
    have hh : t < 1 - eta := lt_of_not_ge hn
    by_cases hl : t ≤ eta
    · rw [round_low he hl] at h
      norm_num at h
    · rw [round_mid (le_of_not_ge hl) hh.le] at h
      have hd : 0 < 1 - 2 * eta := by linarith
      have hv : (t - eta) / (1 - 2 * eta) < 1 := by
        apply (div_lt_iff₀ hd).mpr
        linarith
      linarith
  · exact round_high he

omit he0 in
theorem round_range (t : Real) : 0 ≤ roundSymbol eta t ∧ roundSymbol eta t ≤ 1 := by
  by_cases hl : t ≤ eta
  · simp [round_low he hl]
  by_cases hh : 1 - eta ≤ t
  · simp [round_high he hh]
  rw [round_mid (le_of_not_ge hl) (le_of_not_ge hh)]
  constructor
  · exact div_nonneg (by linarith) (by linarith)
  · apply (div_le_iff₀ (by linarith : 0 < 1 - 2 * eta)).mpr
    linarith

/-- Necessary and sufficient, including ties between branches with the same value. -/
theorem exact_symbol_iff {I S : Type*} [Fintype I] [DecidableEq S]
    (p : Probability I) (label : I -> S) (target : S) :
    (fun s => roundSymbol eta (p.coord label s)) = oneHot target ↔
      p.wrong label target ≤ eta := by
  constructor
  · intro h
    have ht := congrFun h target
    simp only [oneHot_self] at ht
    have hl := (round_eq_one_iff he _).mp ht
    have heq := p.coord_add_wrong label target
    linarith
  · intro hb
    funext s
    by_cases hs : s = target
    · subst s
      rw [oneHot_self]
      apply round_high he
      have heq := p.coord_add_wrong label target
      linarith
    · rw [oneHot_ne hs]
      apply round_low he
      exact (p.coord_other_le_wrong label hs).trans hb

omit he0 in
/-- Correction is robust even when the realized coordinates leave [0,1]. -/
theorem corrected_perturbation {I S : Type*} [Fintype I] [DecidableEq S]
    (p : Probability I) (label : I -> S) (target : S)
    (xi : Real) (v : S -> Real)
    (hb : p.wrong label target ≤ eta - xi)
    (hv : ∀ s, |v s - p.coord label s| ≤ xi) :
    (fun s => roundSymbol eta (v s)) = oneHot target := by
  funext s
  have hcoord := abs_le.mp (hv s)
  by_cases hs : s = target
  · subst s
    rw [oneHot_self]
    apply round_high he
    have heq := p.coord_add_wrong label target
    linarith
  · rw [oneHot_ne hs]
    apply round_low he
    have hh := p.coord_other_le_wrong label hs
    linarith
end Correction

/-- Identifier gating uses exactly two ReLU units per (node,symbol). -/
def gatedRound (eta u w : Real) : Real :=
  (relu (w + u - 1 - eta) - relu (w + u - 2 + eta)) / (1 - 2 * eta)

theorem gatedRound_one (eta w : Real) : gatedRound eta 1 w = roundSymbol eta w := by
  unfold gatedRound roundSymbol
  congr 2 <;> ring

theorem gatedRound_zero {eta w : Real} (he0 : 0 ≤ eta) (he : eta < 1 / 2)
    (hw : w ≤ 1) : gatedRound eta 0 w = 0 := by
  have h1 : w - 1 - eta ≤ 0 := by linarith
  have h2 : w - 2 + eta ≤ 0 := by linarith
  simp [gatedRound, relu_of_nonpos h1, relu_of_nonpos h2]

section Softmax
variable {I : Type*} [Fintype I] [Nonempty I]

def partition (score : I -> Real) (T : Real) : Real := ∑ i, Real.exp (score i / T)

theorem partition_pos (score : I -> Real) (T : Real) : 0 < partition score T := by
  apply Finset.sum_pos
  · intro i hi; exact Real.exp_pos _
  · exact Finset.univ_nonempty

def softmax (score : I -> Real) (T : Real) : Probability I where
  weight i := Real.exp (score i / T) / partition score T
  nonneg i := le_of_lt (div_pos (Real.exp_pos _) (partition_pos score T))
  total := by
    rw [<- Finset.sum_div]
    exact div_self (ne_of_gt (partition_pos score T))

theorem singleton_softmax (score : Fin 1 -> Real) (T : Real) :
    (softmax score T).weight 0 = 1 := by
  simp [softmax, partition, Real.exp_ne_zero]

theorem soft_wrong_ratio {S : Type*} [DecidableEq S]
    (score : I -> Real) (T : Real) (label : I -> S) (target : S) :
    (softmax score T).wrong label target =
      (∑ i, if label i ≠ target then Real.exp (score i / T) else 0) /
      partition score T := by
  simp only [Probability.wrong, softmax]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

/-- Pure ratio algebra used by the semantic margin certificate. -/
theorem ratio_bound {G B r : Real} (hG : 0 < G) (hB : 0 ≤ B)
    (hr : 0 ≤ r) (hBG : B ≤ r * G) :
    B / (G + B) ≤ r / (1 + r) := by
  apply (div_le_div_iff₀ (by linarith : 0 < G + B) (by linarith : 0 < 1 + r)).mpr
  nlinarith

theorem ratio_threshold {r eta : Real} (hr : 0 ≤ r) (he : eta < 1) :
    r / (1 + r) ≤ eta ↔ r ≤ eta / (1 - eta) := by
  rw [div_le_iff₀ (by linarith : 0 < 1 + r), le_div_iff₀ (by linarith : 0 < 1 - eta)]
  constructor <;> intro h <;> nlinarith

/-- A set of maximizers sharing the target symbol may replace a unique branch.
The count k of bad branches and count m of certified good maximizers enter
as k/m, rather than as a count of all nonselected routes. -/
theorem semantic_margin_bound {S : Type*} [DecidableEq S]
    (score : I -> Real) (T : Real) (hT : 0 < T) (label : I -> S) (target : S)
    (Gstar : Finset I) (hGstar : Gstar.Nonempty) (best gap : Real)
    (hgood : ∀ i ∈ Gstar, label i = target ∧ score i = best)
    (hbad : ∀ i, label i ≠ target -> score i ≤ best - gap) :
    let k : Nat := (Finset.univ.filter (fun i => label i ≠ target)).card
    let m : Nat := Gstar.card
    let r : Real := (k : Real) / (m : Real) * Real.exp (-gap / T)
    (softmax score T).wrong label target ≤ r / (1 + r) := by
  classical
  let good := Finset.univ.filter (fun i => label i = target)
  let bad := Finset.univ.filter (fun i => label i ≠ target)
  let G : Real := ∑ i ∈ good, Real.exp (score i / T)
  let B : Real := ∑ i ∈ bad, Real.exp (score i / T)
  let m : Real := Gstar.card
  let k : Real := bad.card
  let r : Real := k / m * Real.exp (-gap / T)
  have hm : 0 < m := by
    show (0 : Real) < (Gstar.card : Real)
    exact_mod_cast hGstar.card_pos
  have hk : 0 ≤ k := by positivity
  have hsub : Gstar ⊆ good := by
    intro i hi
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hgood i hi).1
  have hGlow : m * Real.exp (best / T) ≤ G := by
    calc
      m * Real.exp (best / T) = ∑ i ∈ Gstar, Real.exp (score i / T) := by
        calc
          m * Real.exp (best / T) = ∑ i ∈ Gstar, Real.exp (best / T) := by simp [m]
          _ = ∑ i ∈ Gstar, Real.exp (score i / T) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [(hgood i hi).2]
      _ ≤ G := Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; exact (Real.exp_pos _).le)
  have hBbound : B ≤ k * Real.exp ((best - gap) / T) := by
    calc
      B ≤ ∑ i ∈ bad, Real.exp ((best - gap) / T) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Real.exp_le_exp.mpr
        exact div_le_div_of_nonneg_right (hbad i (Finset.mem_filter.mp hi).2) hT.le
      _ = k * Real.exp ((best - gap) / T) := by simp [k]
  have hexp : Real.exp ((best - gap) / T) = Real.exp (best / T) * Real.exp (-gap / T) := by
    rw [<- Real.exp_add]
    congr 1
    ring
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hG : 0 < G := lt_of_lt_of_le (mul_pos hm (Real.exp_pos _)) hGlow
  have hB : 0 ≤ B := Finset.sum_nonneg (by intros; exact (Real.exp_pos _).le)
  have hBG : B ≤ r * G := by
    calc
      B ≤ k * Real.exp ((best - gap) / T) := hBbound
      _ = r * (m * Real.exp (best / T)) := by
        rw [hexp]
        dsimp [r]
        field_simp
      _ ≤ r * G := mul_le_mul_of_nonneg_left hGlow hr
  have htotal : partition score T = G + B := by
    simp only [partition, G, B, good, bad, Finset.sum_filter]
    rw [<- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : label i = target <;> simp [h]
  change (softmax score T).wrong label target ≤ r / (1 + r)
  rw [soft_wrong_ratio, htotal]
  simpa [B, bad, Finset.sum_filter] using ratio_bound hG hB hr hBG

omit [Fintype I] [Nonempty I] in
/-- Stable-score certificate. Absolute score errors reduce the gap by at most
 twice the error, independently of the number of branches. -/
theorem perturbed_gap {s t : I -> Real} (winner : I) (delta zeta : Real)
    (herror : ∀ i, |t i - s i| ≤ zeta)
    (hgap : ∀ i, i ≠ winner -> delta ≤ s winner - s i) :
    ∀ i, i ≠ winner -> delta - 2 * zeta ≤ t winner - t i := by
  intro i hi
  have hw := abs_le.mp (herror winner)
  have ht := abs_le.mp (herror i)
  have hg := hgap i hi
  linarith
end Softmax

/-- Margin-to-temperature conversion; all logarithm arguments are positive. -/
theorem exp_temperature_certificate {k eta delta T : Real}
    (hk : 0 < k) (he0 : 0 < eta) (he : eta < 1 / 2)
    (hT : 0 < T)
    (hlog : 0 < Real.log (k * (1 - eta) / eta))
    (hbound : T ≤ delta / Real.log (k * (1 - eta) / eta)) :
    k * Real.exp (-delta / T) ≤ eta / (1 - eta) := by
  have he1 : 0 < 1 - eta := by linarith
  have hx : 0 < k * (1 - eta) / eta := div_pos (mul_pos hk he1) he0
  have hmul : T * Real.log (k * (1 - eta) / eta) ≤ delta :=
    (le_div_iff₀ hlog).mp hbound
  have hexponent : -delta / T ≤ -Real.log (k * (1 - eta) / eta) := by
    apply (div_le_iff₀ hT).mpr
    nlinarith
  have hmono := Real.exp_le_exp.mpr hexponent
  rw [Real.exp_neg, Real.exp_log hx] at hmono
  have h := mul_le_mul_of_nonneg_left hmono hk.le
  have hk0 : k ≠ 0 := ne_of_gt hk
  have heta0 : eta ≠ 0 := ne_of_gt he0
  have he10 : (1 : Real) - eta ≠ 0 := ne_of_gt he1
  have hkey : k * (k * (1 - eta) / eta)⁻¹ = eta / (1 - eta) := by
    field_simp
  exact le_of_le_of_eq h hkey

end NeuralArtifacts.Neural

end -- noncomputable section

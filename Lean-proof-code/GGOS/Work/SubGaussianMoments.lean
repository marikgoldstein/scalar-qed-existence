module

public import Mathlib

public section

open MeasureTheory Real

/-!
# Moments of a real variable with a Gaussian bound on its moment generating function
-/

namespace GGOS.Work

private lemma norm_pow_le_factorial_mul_exp_add_exp_neg (x : ℝ) (n : ℕ) :
    ‖x ^ n‖ ≤ (n.factorial : ℝ) * (Real.exp (1 * x) + Real.exp ((-1 : ℝ) * x)) := by
  rw [Real.norm_eq_abs, abs_pow]
  have hpos : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have h1 : |x| ^ n / (n.factorial : ℝ) ≤ Real.exp |x| :=
    Real.pow_div_factorial_le_exp _ (abs_nonneg x) n
  have h2 : |x| ^ n ≤ (n.factorial : ℝ) * Real.exp |x| := by
    have hmul := mul_le_mul_of_nonneg_left h1 hpos.le
    rwa [mul_div_cancel₀ _ hpos.ne'] at hmul
  have h3 : Real.exp |x| ≤ Real.exp (1 * x) + Real.exp ((-1 : ℝ) * x) := by
    have h1x : 1 * x = x := one_mul x
    have hnx : (-1 : ℝ) * x = -x := by ring
    rw [h1x, hnx]
    exact Real.exp_abs_le x
  exact h2.trans (mul_le_mul_of_nonneg_left h3 hpos.le)

private lemma integrable_pow_of_exp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (hX : AEMeasurable X μ)
    (hint : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * X ω)) μ) (n : ℕ) :
    Integrable (fun ω => X ω ^ n) μ := by
  have hdom : Integrable
      (fun ω => (n.factorial : ℝ) * (Real.exp (1 * X ω) + Real.exp ((-1 : ℝ) * X ω))) μ :=
    ((hint 1).fun_add (hint (-1))).const_mul (n.factorial : ℝ)
  exact Integrable.mono' hdom
    ((continuous_pow n).comp_aestronglyMeasurable hX.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => norm_pow_le_factorial_mul_exp_add_exp_neg (X ω) n)

private lemma eq_zero_of_mul_le_sq_mul_half {m A : ℝ}
    (h : ∀ s : ℝ, s * m ≤ s ^ 2 * A / 2) : m = 0 := by
  by_cases hA : A ≤ 0
  · have hm : m * m ≤ m ^ 2 * A / 2 := h m
    have hnonpos : m ^ 2 * A ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg m) hA
    have hsq : m ^ 2 ≤ 0 := by linarith [sq m]
    exact sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg m))
  · have hA' : 0 < A := lt_of_not_ge hA
    have hm : m / A * m ≤ (m / A) ^ 2 * A / 2 := h (m / A)
    have hcancel : A * (m / A) = m := mul_div_cancel₀ m hA'.ne'
    have hmul : (2 * A) * (m / A * m) ≤ (2 * A) * ((m / A) ^ 2 * A / 2) :=
      mul_le_mul_of_nonneg_left hm (by linarith)
    have hL : (2 * A) * (m / A * m) = 2 * m ^ 2 := by
      calc (2 * A) * (m / A * m) = 2 * (A * (m / A)) * m := by ring
        _ = 2 * m * m := by rw [hcancel]
        _ = 2 * m ^ 2 := by ring
    have hR : (2 * A) * ((m / A) ^ 2 * A / 2) = m ^ 2 := by
      calc (2 * A) * ((m / A) ^ 2 * A / 2) = (A * (m / A)) * (A * (m / A)) := by ring
        _ = m * m := by rw [hcancel]
        _ = m ^ 2 := by ring
    have hsq : m ^ 2 ≤ 0 := by linarith
    exact sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg m))

private lemma integral_eq_zero_of_mgf_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (A : ℝ)
    (hintX : Integrable X μ)
    (hint : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * X ω)) μ)
    (hmgf : ∀ s : ℝ, ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp (s ^ 2 * A / 2)) :
    ∫ ω, X ω ∂μ = 0 := by
  let m : ℝ := ∫ ω, X ω ∂μ
  refine eq_zero_of_mul_le_sq_mul_half (A := A) (fun s => ?_)
  have hpt : ∀ ω : Ω,
      Real.exp (s * m) + (Real.exp (s * m) * s) * (X ω - m) ≤ Real.exp (s * X ω) := by
    intro ω
    have h1 : (s * (X ω - m) + 1) * Real.exp (s * m) ≤
        Real.exp (s * (X ω - m)) * Real.exp (s * m) :=
      mul_le_mul_of_nonneg_right
        (Real.add_one_le_exp (s * (X ω - m))) (Real.exp_nonneg (s * m))
    have h2 : Real.exp (s * (X ω - m)) * Real.exp (s * m) = Real.exp (s * X ω) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h3 : (s * (X ω - m) + 1) * Real.exp (s * m) =
        Real.exp (s * m) + (Real.exp (s * m) * s) * (X ω - m) := by ring
    linarith
  have hint_sub : Integrable (fun ω => X ω - m) μ := hintX.sub' (integrable_const m)
  have hint_lin : Integrable (fun ω => (Real.exp (s * m) * s) * (X ω - m)) μ :=
    hint_sub.const_mul (Real.exp (s * m) * s)
  have hint_lhs : Integrable
      (fun ω => Real.exp (s * m) + (Real.exp (s * m) * s) * (X ω - m)) μ :=
    (integrable_const (Real.exp (s * m))).fun_add hint_lin
  have hile :
      (∫ ω, (Real.exp (s * m) + (Real.exp (s * m) * s) * (X ω - m)) ∂μ) ≤
        ∫ ω, Real.exp (s * X ω) ∂μ :=
    integral_mono hint_lhs (hint s) hpt
  have hc1 : (∫ _ : Ω, Real.exp (s * m) ∂μ) = Real.exp (s * m) :=
    integral_eq_const (Filter.Eventually.of_forall fun _ => rfl)
  have hc2 : (∫ _ : Ω, m ∂μ) = m :=
    integral_eq_const (Filter.Eventually.of_forall fun _ => rfl)
  have hlhs :
      (∫ ω, (Real.exp (s * m) + (Real.exp (s * m) * s) * (X ω - m)) ∂μ) = Real.exp (s * m) := by
    rw [integral_add (integrable_const (Real.exp (s * m))) hint_lin, hc1,
      integral_const_mul, integral_sub hintX (integrable_const m), hc2]
    change Real.exp (s * m) + (Real.exp (s * m) * s) * (m - m) = Real.exp (s * m)
    ring
  rw [hlhs] at hile
  exact Real.exp_le_exp.mp (hile.trans (hmgf s))

private lemma pow_two_mul_div_factorial_le_cosh (y : ℝ) (k : ℕ) :
    y ^ (2 * k) / ((2 * k).factorial : ℝ) ≤ (Real.exp y + Real.exp (-y)) / 2 := by
  have hnn : ∀ n : ℕ, 0 ≤ y ^ (2 * n) / ((2 * n).factorial : ℝ) := by
    intro n
    rw [pow_mul]
    exact div_nonneg (pow_nonneg (sq_nonneg y) n) (Nat.cast_nonneg _)
  have hle : y ^ (2 * k) / ((2 * k).factorial : ℝ) ≤ Real.cosh y :=
    le_hasSum (Real.hasSum_cosh y) k (fun j _ => hnn j)
  rwa [Real.cosh_eq] at hle

private lemma sq_le_exp_add_exp_neg_sub_two (y : ℝ) :
    y ^ 2 ≤ Real.exp y + Real.exp (-y) - 2 := by
  have hnn : ∀ n : ℕ, 0 ≤ y ^ (2 * n) / ((2 * n).factorial : ℝ) := by
    intro n
    rw [pow_mul]
    exact div_nonneg (pow_nonneg (sq_nonneg y) n) (Nat.cast_nonneg _)
  have hle : (∑ n ∈ Finset.range 2, y ^ (2 * n) / ((2 * n).factorial : ℝ)) ≤ Real.cosh y :=
    sum_le_hasSum (Finset.range 2) (fun n _ => hnn n) (Real.hasSum_cosh y)
  have hsum : (∑ n ∈ Finset.range 2, y ^ (2 * n) / ((2 * n).factorial : ℝ)) = 1 + y ^ 2 / 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    have h0 : (2 * 0).factorial = 1 := rfl
    have h2 : (2 * 1).factorial = 2 := rfl
    have hp0 : y ^ (2 * 0) = 1 := pow_zero y
    have hp1 : y ^ (2 * 1) = y ^ 2 := rfl
    rw [h0, h2, Nat.cast_one, Nat.cast_ofNat, hp0, hp1]
    ring
  rw [hsum, Real.cosh_eq] at hle
  linarith

private lemma exp_sub_one_le_mul_exp (u : ℝ) :
    Real.exp u - 1 ≤ u * Real.exp u := by
  have h1 : (-u + 1) * Real.exp u ≤ Real.exp (-u) * Real.exp u :=
    mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-u)) (Real.exp_nonneg u)
  have h2 : Real.exp (-u) * Real.exp u = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h3 : (-u + 1) * Real.exp u = Real.exp u - u * Real.exp u := by ring
  linarith

private lemma le_of_forall_ne_zero_le_mul_exp_sq {v A : ℝ} (hv : 0 ≤ v)
    (h : ∀ s : ℝ, s ≠ 0 → v ≤ A * Real.exp (s ^ 2 * A / 2)) : v ≤ A := by
  by_cases hA : A ≤ 0
  · rcases lt_or_eq_of_le hA with hAlt | rfl
    · have h1 : v ≤ A * Real.exp ((1 : ℝ) ^ 2 * A / 2) := h 1 one_ne_zero
      have hexp : 0 < Real.exp ((1 : ℝ) ^ 2 * A / 2) := Real.exp_pos _
      have hneg : A * Real.exp ((1 : ℝ) ^ 2 * A / 2) < 0 := mul_neg_of_neg_of_pos hAlt hexp
      linarith
    · have h1 : v ≤ 0 * Real.exp ((1 : ℝ) ^ 2 * 0 / 2) := h 1 one_ne_zero
      linarith
  · have hA' : 0 < A := lt_of_not_ge hA
    by_contra hnot
    have hlt : A < v := lt_of_not_ge hnot
    have hdiv_gt_one : 1 < v / A := (one_lt_div hA').mpr hlt
    have hlog_pos : 0 < Real.log (v / A) := Real.log_pos hdiv_gt_one
    have harg_pos : 0 < Real.log (v / A) / A := div_pos hlog_pos hA'
    let s : ℝ := Real.sqrt (Real.log (v / A) / A)
    have hs_pos : 0 < s := Real.sqrt_pos.mpr harg_pos
    have hs_sq : s ^ 2 = Real.log (v / A) / A := Real.sq_sqrt harg_pos.le
    have hbound : v ≤ A * Real.exp (s ^ 2 * A / 2) := h s hs_pos.ne'
    have hexp_arg : s ^ 2 * A / 2 = Real.log (v / A) / 2 := by
      rw [hs_sq, div_mul_cancel₀ _ hA'.ne']
    have hexp_lt : Real.exp (Real.log (v / A) / 2) < Real.exp (Real.log (v / A)) :=
      Real.exp_lt_exp.mpr (by linarith)
    have hexp_log : Real.exp (Real.log (v / A)) = v / A :=
      Real.exp_log (div_pos (lt_trans hA' hlt) hA')
    have hstrict : A * Real.exp (s ^ 2 * A / 2) < v := by
      rw [hexp_arg]
      calc A * Real.exp (Real.log (v / A) / 2)
          < A * Real.exp (Real.log (v / A)) := mul_lt_mul_of_pos_left hexp_lt hA'
        _ = A * (v / A) := by rw [hexp_log]
        _ = v := mul_div_cancel₀ v hA'.ne'
    linarith

private lemma integral_sq_le_of_mgf_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (A : ℝ)
    (hint2 : Integrable (fun ω => X ω ^ 2) μ)
    (hint : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * X ω)) μ)
    (hmgf : ∀ s : ℝ, ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp (s ^ 2 * A / 2)) :
    ∫ ω, X ω ^ 2 ∂μ ≤ A := by
  have hv_nonneg : 0 ≤ ∫ ω, X ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg (X ω)
  refine le_of_forall_ne_zero_le_mul_exp_sq hv_nonneg (fun s hs => ?_)
  have hpt : ∀ ω : Ω,
      s ^ 2 * X ω ^ 2 ≤ Real.exp (s * X ω) + Real.exp ((-s) * X ω) - 2 := by
    intro ω
    have h1 := sq_le_exp_add_exp_neg_sub_two (s * X ω)
    have hL : (s * X ω) ^ 2 = s ^ 2 * X ω ^ 2 := mul_pow s (X ω) 2
    have hR : Real.exp (-(s * X ω)) = Real.exp ((-s) * X ω) := by rw [neg_mul]
    linarith
  have hintL : Integrable (fun ω => s ^ 2 * X ω ^ 2) μ := hint2.const_mul (s ^ 2)
  have hintR : Integrable (fun ω => Real.exp (s * X ω) + Real.exp ((-s) * X ω) - 2) μ :=
    ((hint s).fun_add (hint (-s))).sub' (integrable_const (2 : ℝ))
  have hile :
      (∫ ω, s ^ 2 * X ω ^ 2 ∂μ) ≤
        ∫ ω, (Real.exp (s * X ω) + Real.exp ((-s) * X ω) - 2) ∂μ :=
    integral_mono hintL hintR hpt
  have hc2 : (∫ _ : Ω, (2 : ℝ) ∂μ) = 2 :=
    integral_eq_const (Filter.Eventually.of_forall fun _ => rfl)
  rw [integral_const_mul,
    integral_sub ((hint s).fun_add (hint (-s))) (integrable_const (2 : ℝ)),
    integral_add (hint s) (hint (-s)), hc2] at hile
  have hm1 : ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp (s ^ 2 * A / 2) := hmgf s
  have hm2 : ∫ ω, Real.exp ((-s) * X ω) ∂μ ≤ Real.exp (s ^ 2 * A / 2) := by
    have h := hmgf (-s)
    rwa [neg_sq] at h
  have hstep1 : s ^ 2 * (∫ ω, X ω ^ 2 ∂μ) ≤ 2 * (Real.exp (s ^ 2 * A / 2) - 1) := by linarith
  have hexp_ub : Real.exp (s ^ 2 * A / 2) - 1 ≤
      (s ^ 2 * A / 2) * Real.exp (s ^ 2 * A / 2) :=
    exp_sub_one_le_mul_exp (s ^ 2 * A / 2)
  have hstep2 : 2 * (Real.exp (s ^ 2 * A / 2) - 1) ≤
      s ^ 2 * (A * Real.exp (s ^ 2 * A / 2)) := by
    have hmul := mul_le_mul_of_nonneg_left hexp_ub (by norm_num : (0 : ℝ) ≤ 2)
    have hid : 2 * ((s ^ 2 * A / 2) * Real.exp (s ^ 2 * A / 2)) =
        s ^ 2 * (A * Real.exp (s ^ 2 * A / 2)) := by ring
    linarith
  have hs2_pos : 0 < s ^ 2 := sq_pos_of_ne_zero hs
  exact le_of_mul_le_mul_left (hstep1.trans hstep2) hs2_pos

private lemma exp_bound_moment_two_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (A : ℝ) (k : ℕ)
    (hint2k : Integrable (fun ω => X ω ^ (2 * k)) μ)
    (hint : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * X ω)) μ)
    (hmgf : ∀ s : ℝ, ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp (s ^ 2 * A / 2))
    (s : ℝ) :
    (s ^ (2 * k) / ((2 * k).factorial : ℝ)) * (∫ ω, X ω ^ (2 * k) ∂μ) ≤
      Real.exp (s ^ 2 * A / 2) := by
  have hpt : ∀ ω : Ω,
      (s ^ (2 * k) / ((2 * k).factorial : ℝ)) * X ω ^ (2 * k) ≤
        (1 / 2 : ℝ) * (Real.exp (s * X ω) + Real.exp ((-s) * X ω)) := by
    intro ω
    have h1 := pow_two_mul_div_factorial_le_cosh (s * X ω) k
    have hL : (s * X ω) ^ (2 * k) / ((2 * k).factorial : ℝ) =
        (s ^ (2 * k) / ((2 * k).factorial : ℝ)) * X ω ^ (2 * k) := by
      rw [mul_pow]
      ring
    have hR : (Real.exp (s * X ω) + Real.exp (-(s * X ω))) / 2 =
        (1 / 2 : ℝ) * (Real.exp (s * X ω) + Real.exp ((-s) * X ω)) := by
      rw [neg_mul]
      ring
    linarith
  have hintL : Integrable
      (fun ω => (s ^ (2 * k) / ((2 * k).factorial : ℝ)) * X ω ^ (2 * k)) μ :=
    hint2k.const_mul (s ^ (2 * k) / ((2 * k).factorial : ℝ))
  have hintR : Integrable
      (fun ω => (1 / 2 : ℝ) * (Real.exp (s * X ω) + Real.exp ((-s) * X ω))) μ :=
    ((hint s).fun_add (hint (-s))).const_mul (1 / 2 : ℝ)
  have hile :
      (∫ ω, (s ^ (2 * k) / ((2 * k).factorial : ℝ)) * X ω ^ (2 * k) ∂μ) ≤
        ∫ ω, (1 / 2 : ℝ) * (Real.exp (s * X ω) + Real.exp ((-s) * X ω)) ∂μ :=
    integral_mono hintL hintR hpt
  rw [integral_const_mul, integral_const_mul, integral_add (hint s) (hint (-s))] at hile
  have hm1 : ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp (s ^ 2 * A / 2) := hmgf s
  have hm2 : ∫ ω, Real.exp ((-s) * X ω) ∂μ ≤ Real.exp (s ^ 2 * A / 2) := by
    have h := hmgf (-s)
    rwa [neg_sq] at h
  linarith

private lemma integral_pow_two_mul_le_of_mgf_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (A : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hint2 : Integrable (fun ω => X ω ^ 2) μ)
    (hvA : ∫ ω, X ω ^ 2 ∂μ ≤ A)
    (hint2k : Integrable (fun ω => X ω ^ (2 * k)) μ)
    (hint : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * X ω)) μ)
    (hmgf : ∀ s : ℝ, ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp (s ^ 2 * A / 2)) :
    ∫ ω, X ω ^ (2 * k) ∂μ ≤ ((2 * k).factorial : ℝ) * (Real.exp 1 * A / (2 * k : ℝ)) ^ k := by
  have hv_nonneg : 0 ≤ ∫ ω, X ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg (X ω)
  have hA_nonneg : 0 ≤ A := hv_nonneg.trans hvA
  rcases hA_nonneg.eq_or_lt with hA0 | hA_pos
  · have hA0' : A = 0 := hA0.symm
    subst hA0'
    have hv0 : ∫ ω, X ω ^ 2 ∂μ = 0 := le_antisymm hvA hv_nonneg
    have hae2 : (fun ω => X ω ^ 2) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (X ω)) hint2).mp hv0
    have hk_pos_nat : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk
    have h2k_pos_nat : 0 < 2 * k := Nat.mul_pos (Nat.succ_pos 1) hk_pos_nat
    have h2k_ne : 2 * k ≠ 0 := h2k_pos_nat.ne'
    have hae2k : (fun ω => X ω ^ (2 * k)) =ᵐ[μ] (fun _ => (0 : ℝ)) :=
      hae2.mono fun ω hω => by
        change X ω ^ 2 = 0 at hω
        have hx0 : X ω = 0 := sq_eq_zero_iff.mp hω
        show X ω ^ (2 * k) = 0
        rw [hx0, zero_pow h2k_ne]
    have hc0 : (∫ _ : Ω, (0 : ℝ) ∂μ) = 0 :=
      integral_eq_const (Filter.Eventually.of_forall fun _ => rfl)
    rw [integral_congr_ae hae2k, hc0]
    have hrhs0 : (Real.exp 1 * 0 / (2 * k : ℝ)) = 0 := by ring
    rw [hrhs0]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg le_rfl k)
  · have hk_pos : (0 : ℝ) < (k : ℝ) :=
      Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
    have h2k_pos : (0 : ℝ) < (2 * k : ℝ) := by linarith
    have hdiv_pos : 0 < (2 * k : ℝ) / A := div_pos h2k_pos hA_pos
    let s : ℝ := Real.sqrt ((2 * k : ℝ) / A)
    have hs_sq : s ^ 2 = (2 * k : ℝ) / A := Real.sq_sqrt hdiv_pos.le
    have hbound :
        (s ^ (2 * k) / ((2 * k).factorial : ℝ)) * (∫ ω, X ω ^ (2 * k) ∂μ) ≤
          Real.exp (s ^ 2 * A / 2) :=
      exp_bound_moment_two_mul μ X A k hint2k hint hmgf s
    have hs2k : s ^ (2 * k) = ((2 * k : ℝ) / A) ^ k := by
      rw [pow_mul, hs_sq]
    have hexp_eq : Real.exp (s ^ 2 * A / 2) = Real.exp 1 ^ k := by
      have harg : s ^ 2 * A / 2 = (k : ℝ) * 1 := by
        calc s ^ 2 * A / 2 = ((2 * k : ℝ) / A * A) / 2 := by rw [hs_sq]
          _ = (2 * k : ℝ) / 2 := by rw [div_mul_cancel₀ _ hA_pos.ne']
          _ = (k : ℝ) * 1 := by ring
      rw [harg, Real.exp_nat_mul]
    rw [hs2k, hexp_eq] at hbound
    have hfac_pos : (0 : ℝ) < ((2 * k).factorial : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos (2 * k))
    have hfac_nonneg : 0 ≤ ((2 * k).factorial : ℝ) * (A / (2 * k : ℝ)) ^ k :=
      mul_nonneg hfac_pos.le (pow_nonneg (div_pos hA_pos h2k_pos).le k)
    have hmul := mul_le_mul_of_nonneg_left hbound hfac_nonneg
    have hvu : (A / (2 * k : ℝ)) ^ k * ((2 * k : ℝ) / A) ^ k = 1 := by
      rw [← mul_pow, div_mul_div_cancel₀ h2k_pos.ne', div_self hA_pos.ne', one_pow]
    have hL :
        (((2 * k).factorial : ℝ) * (A / (2 * k : ℝ)) ^ k) *
            ((((2 * k : ℝ) / A) ^ k / ((2 * k).factorial : ℝ)) * (∫ ω, X ω ^ (2 * k) ∂μ)) =
          ∫ ω, X ω ^ (2 * k) ∂μ := by
      calc (((2 * k).factorial : ℝ) * (A / (2 * k : ℝ)) ^ k) *
              ((((2 * k : ℝ) / A) ^ k / ((2 * k).factorial : ℝ)) * (∫ ω, X ω ^ (2 * k) ∂μ))
          = ((A / (2 * k : ℝ)) ^ k * (((2 * k).factorial : ℝ) *
              (((2 * k : ℝ) / A) ^ k / ((2 * k).factorial : ℝ)))) *
              (∫ ω, X ω ^ (2 * k) ∂μ) := by ring
        _ = ((A / (2 * k : ℝ)) ^ k * ((2 * k : ℝ) / A) ^ k) * (∫ ω, X ω ^ (2 * k) ∂μ) := by
            rw [mul_div_cancel₀ _ hfac_pos.ne']
        _ = 1 * (∫ ω, X ω ^ (2 * k) ∂μ) := by rw [hvu]
        _ = ∫ ω, X ω ^ (2 * k) ∂μ := one_mul _
    have hR :
        (((2 * k).factorial : ℝ) * (A / (2 * k : ℝ)) ^ k) * Real.exp 1 ^ k =
          ((2 * k).factorial : ℝ) * (Real.exp 1 * A / (2 * k : ℝ)) ^ k := by
      have hpow : (A / (2 * k : ℝ)) ^ k * Real.exp 1 ^ k =
          (Real.exp 1 * A / (2 * k : ℝ)) ^ k := by
        rw [← mul_pow]
        congr 1
        rw [mul_comm, ← mul_div_assoc]
      calc (((2 * k).factorial : ℝ) * (A / (2 * k : ℝ)) ^ k) * Real.exp 1 ^ k
          = ((2 * k).factorial : ℝ) * ((A / (2 * k : ℝ)) ^ k * Real.exp 1 ^ k) := mul_assoc _ _ _
        _ = ((2 * k).factorial : ℝ) * (Real.exp 1 * A / (2 * k : ℝ)) ^ k := by rw [hpow]
    rwa [hL, hR] at hmul

/-- If `E[e^{sX}] ≤ e^{s² A / 2}` for every real `s`, then `E[X] = 0`, `E[X²] ≤ A` and
`E[X^{2k}] ≤ (2k)! (e A / (2k))^k` ([GG-OS] Theorem 3.1, second sentence, from the first). -/
theorem moments_of_mgf_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : AEMeasurable X μ) (A : ℝ)
    (hint : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * X ω)) μ)
    (hmgf : ∀ s : ℝ, ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp (s ^ 2 * A / 2)) :
    (Integrable X μ ∧ ∫ ω, X ω ∂μ = 0) ∧
      (Integrable (fun ω => X ω ^ 2) μ ∧ ∫ ω, X ω ^ 2 ∂μ ≤ A) ∧
      ∀ k : ℕ, 1 ≤ k →
        Integrable (fun ω => X ω ^ (2 * k)) μ ∧
          ∫ ω, X ω ^ (2 * k) ∂μ ≤ ((2 * k).factorial : ℝ) * (Real.exp 1 * A / (2 * k : ℝ)) ^ k := by
  have hint_pow : ∀ n : ℕ, Integrable (fun ω => X ω ^ n) μ :=
    integrable_pow_of_exp μ X hX hint
  have hintX : Integrable X μ :=
    (hint_pow 1).congr (Filter.Eventually.of_forall fun ω => pow_one (X ω))
  have hmean : ∫ ω, X ω ∂μ = 0 :=
    integral_eq_zero_of_mgf_le μ X A hintX hint hmgf
  have hint2 : Integrable (fun ω => X ω ^ 2) μ := hint_pow 2
  have hvA : ∫ ω, X ω ^ 2 ∂μ ≤ A :=
    integral_sq_le_of_mgf_le μ X A hint2 hint hmgf
  refine ⟨⟨hintX, hmean⟩, ⟨hint2, hvA⟩, fun k hk => ⟨hint_pow (2 * k), ?_⟩⟩
  exact integral_pow_two_mul_le_of_mgf_le μ X A k hk hint2 hvA (hint_pow (2 * k)) hint hmgf

end GGOS.Work

end

module

public import GGOS.OS.Axioms
public import GGOS.OS.Work.SchwingerLaw

/-!
# The growth condition of the Schwinger functions ([GG-OS] Theorem 9.4 (iii))
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace GGOS.OS

theorem pow_div_factorial_le_cosh {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    t ^ n / n.factorial ≤ Real.cosh t := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have h := Real.hasSum_cosh t
    exact le_hasSum h k fun j _ => by positivity
  · have h := Real.hasSum_sinh t
    have h1 : t ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) ≤ Real.sinh t :=
      le_hasSum h k fun j _ => by positivity
    exact h1.trans (Real.sinh_lt_cosh t).le

variable {sc : Scale} {N0 : ℕ} {gd : DensityFn} {n : ℕ} {σ : Fin n → T}
  {ν : Measure (EuclideanSpace ℝ (Fin n))}

theorem pairNorm_nonneg (σ : T) : 0 ≤ pairNorm sc N0 gd σ := (isSeminorm_pairNorm sc N0 gd).nonneg σ

/-- One coordinate: `E |X_j / q|^n ≤ e^n (n!)^{1/2}` when `‖σ_j‖ ≤ q`. -/
theorem moment_one (h : ExpBounded sc N0 gd σ ν) (hn : 1 ≤ n) (j : Fin n) {q : ℝ} (hq : 0 < q)
    (hjq : pairNorm sc N0 gd (σ j) ≤ q) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => (|x j| / q) ^ n) ν ∧
      ∫ x : EuclideanSpace ℝ (Fin n), (|x j| / q) ^ n ∂ν ≤
        Real.exp n * Real.sqrt n.factorial := by
  have hprob := h.prob
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  let t : ℝ := Real.sqrt n / q
  have ht : 0 < t := div_pos hs hq
  -- the two exponential moments
  let e (r : ℝ) : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j r
  have hin (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ⟪x, e r⟫ = r * x j := by
    rw [inner_eq_sum]
    have hcoord (i : Fin n) : e r i = if i = j then r else 0 := by
      simp [e]
    simp only [hcoord, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hB (r : ℝ) : expBound sc N0 gd σ (e r) = Real.exp (1 / 2 * (|r| * Rnorm sc N0 (σ j)) ^ 2 +
      supNorm gd * (|r| * Enorm sc N0 (σ j))) := by
    have hcoord (i : Fin n) : e r i = if i = j then r else 0 := by
      simp [e]
    have h1 (g : Fin n → ℝ) : ∑ i, |e r i| * g i = |r| * g j := by
      rw [Finset.sum_eq_single j]
      · rw [hcoord, ite_eq_left rfl]
      · intro i _ hi
        rw [hcoord, ite_eq_right hi, abs_zero, zero_mul]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    simp only [expBound, h1]
  let ρ : ℝ := Rnorm sc N0 (σ j) / q
  let η : ℝ := supNorm gd * Enorm sc N0 (σ j) / q
  have hρ : 0 ≤ ρ := div_nonneg (rnorm_nonneg _ _ _) hq.le
  have hη : 0 ≤ η := div_nonneg (mul_nonneg (supNorm_nonneg gd) (enorm_nonneg _ _ _)) hq.le
  have hρη : ρ + η ≤ 1 := by
    rw [← add_div, div_le_one hq]
    exact hjq
  have hexp {r : ℝ} (hr : |r| = t) : expBound sc N0 gd σ (e r) ≤ Real.exp n := by
    rw [hB, hr]
    refine Real.exp_le_exp.mpr ?_
    have h1 : (t * Rnorm sc N0 (σ j)) ^ 2 = n * ρ ^ 2 := by
      have : t * Rnorm sc N0 (σ j) = Real.sqrt n * ρ := by
        simp only [t, ρ]
        ring
      rw [this, mul_pow, Real.sq_sqrt hn0.le]
    have h2 : supNorm gd * (t * Enorm sc N0 (σ j)) = Real.sqrt n * η := by
      simp only [t, η]
      ring
    have h3 : Real.sqrt n ≤ n := by
      rw [Real.sqrt_le_left hn0.le]
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have h4 : ρ ^ 2 ≤ ρ := by nlinarith
    rw [h1, h2]
    have h5 : Real.sqrt n * η ≤ n * η := mul_le_mul_of_nonneg_right h3 hη
    have h6 : (n : ℝ) * ρ ^ 2 ≤ n * ρ := mul_le_mul_of_nonneg_left h4 hn0.le
    have h7 : (n : ℝ) * (ρ + η) ≤ n * 1 := mul_le_mul_of_nonneg_left hρη hn0.le
    have h8 : 0 ≤ (n : ℝ) * ρ := mul_nonneg hn0.le hρ
    nlinarith
  have hcosh_int : Integrable (fun x : EuclideanSpace ℝ (Fin n) => Real.cosh (t * x j)) ν := by
    have h1 := (h.exp (e t)).1
    have h2 := (h.exp (e (-t))).1
    simp only [hin] at h1 h2
    refine ((h1.add h2).div_const 2).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Real.cosh_eq, neg_mul]
  have hcosh : ∫ x : EuclideanSpace ℝ (Fin n), Real.cosh (t * x j) ∂ν ≤ Real.exp n := by
    have h1 := h.exp (e t)
    have h2 := h.exp (e (-t))
    simp only [hin] at h1 h2
    have h3 : (fun x : EuclideanSpace ℝ (Fin n) => Real.cosh (t * x j)) =
        fun x => (Real.exp (t * x j) + Real.exp (-t * x j)) / 2 := by
      funext x
      rw [Real.cosh_eq, neg_mul]
    rw [h3, integral_div, integral_add h1.1 h2.1]
    have b1 := h1.2.trans (hexp (abs_of_pos ht))
    have b2 := h2.2.trans (hexp (r := -t) (by rw [abs_neg, abs_of_pos ht]))
    linarith
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hsn : 0 < Real.sqrt n ^ n := pow_pos hs n
  have hpt (x : EuclideanSpace ℝ (Fin n)) :
      (|x j| / q) ^ n ≤ n.factorial / Real.sqrt n ^ n * Real.cosh (t * x j) := by
    have h1 := pow_div_factorial_le_cosh (t := t * |x j|) (by positivity) n
    have h2 : Real.cosh (t * |x j|) = Real.cosh (t * x j) := by
      rw [← abs_of_pos ht, ← abs_mul, Real.cosh_abs, abs_of_pos ht]
    rw [h2, div_le_iff₀ hfac] at h1
    have h3 : (t * |x j|) ^ n = Real.sqrt n ^ n * (|x j| / q) ^ n := by
      rw [← mul_pow]
      congr 1
      simp only [t]
      ring
    rw [h3] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ hsn]
    calc (|x j| / q) ^ n * Real.sqrt n ^ n = Real.sqrt n ^ n * (|x j| / q) ^ n := mul_comm _ _
      _ ≤ Real.cosh (t * x j) * n.factorial := h1
      _ = n.factorial * Real.cosh (t * x j) := mul_comm _ _
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin n) => (|x j| / q) ^ n) ν :=
    Integrable.mono' (hcosh_int.const_mul _) (by fun_prop) (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact hpt x)
  refine ⟨hint, (integral_mono hint (hcosh_int.const_mul _) hpt).trans ?_⟩
  rw [integral_const_mul]
  have hratio : (n.factorial : ℝ) / Real.sqrt n ^ n ≤ Real.sqrt n.factorial := by
    rw [div_le_iff₀ hsn]
    have h1 : Real.sqrt n.factorial ≤ Real.sqrt n ^ n := by
      rw [Real.sqrt_le_left hsn.le, ← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt hn0.le]
      exact_mod_cast Nat.factorial_le_pow n
    calc (n.factorial : ℝ) = Real.sqrt n.factorial * Real.sqrt n.factorial :=
          (Real.mul_self_sqrt hfac.le).symm
      _ ≤ Real.sqrt n.factorial * Real.sqrt n ^ n :=
          mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
  calc (n.factorial : ℝ) / Real.sqrt n ^ n * ∫ x : EuclideanSpace ℝ (Fin n), Real.cosh (t * x j) ∂ν
      ≤ Real.sqrt n.factorial * Real.exp n :=
        mul_le_mul hratio hcosh (integral_nonneg fun x => (Real.cosh_pos _).le) (Real.sqrt_nonneg _)
    _ = Real.exp n * Real.sqrt n.factorial := mul_comm _ _

/-- The product bound with strict majorants of the norms. -/
theorem moment_prod (h : ExpBounded sc N0 gd σ ν) (q : Fin n → ℝ) (hq : ∀ j, 0 < q j)
    (hjq : ∀ j, pairNorm sc N0 gd (σ j) ≤ q j) :
    |∫ x : EuclideanSpace ℝ (Fin n), ∏ i, x i ∂ν| ≤
      Real.exp n * Real.sqrt n.factorial * ∏ i, q i := by
  have hprob := h.prob
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hone := fun j => moment_one h hn j (hq j) (hjq j)
  have hpt (x : EuclideanSpace ℝ (Fin n)) :
      |∏ i, x i| ≤ (∏ i, q i) * ((1 / n) * ∑ i, (|x i| / q i) ^ n) := by
    have h1 : |∏ i, x i| = (∏ i, q i) * ∏ i, |x i| / q i := by
      rw [Finset.abs_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [mul_div_cancel₀ _ (hq i).ne']
    rw [h1]
    refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun i _ => (hq i).le)
    have h2 := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ : Fin n => (1 / n : ℝ))
      (fun i => (|x i| / q i) ^ n) (fun i _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp)
      (fun i _ => pow_nonneg (div_nonneg (abs_nonneg _) (hq i).le) n)
    rw [← Finset.mul_sum] at h2
    refine le_trans (le_of_eq ?_) h2
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [one_div, Real.pow_rpow_inv_natCast (div_nonneg (abs_nonneg _) (hq i).le) hn.ne']
  have hsum : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (∏ i, q i) * ((1 / n : ℝ) * ∑ i, (|x i| / q i) ^ n)) ν :=
    ((integrable_finsetSum _ fun i _ => (hone i).1).const_mul _).const_mul _
  calc |∫ x : EuclideanSpace ℝ (Fin n), ∏ i, x i ∂ν|
      ≤ ∫ x : EuclideanSpace ℝ (Fin n), |∏ i, x i| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ x : EuclideanSpace ℝ (Fin n), (∏ i, q i) * ((1 / n) * ∑ i, (|x i| / q i) ^ n) ∂ν :=
        integral_mono (h.integrable_prod id).abs hsum hpt
    _ = (∏ i, q i) * ((1 / n) * ∑ i, ∫ x : EuclideanSpace ℝ (Fin n), (|x i| / q i) ^ n ∂ν) := by
        rw [integral_const_mul, integral_const_mul, integral_finsetSum _ fun i _ => (hone i).1]
    _ ≤ (∏ i, q i) * ((1 / n) * ∑ _i : Fin n, Real.exp n * Real.sqrt n.factorial) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun i _ => (hone i).2) (by positivity))
          (Finset.prod_nonneg fun i _ => (hq i).le)
    _ = Real.exp n * Real.sqrt n.factorial * ∏ i, q i := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- The growth condition of the moments. -/
theorem moment_growth (h : ExpBounded sc N0 gd σ ν) :
    |∫ x : EuclideanSpace ℝ (Fin n), ∏ i, x i ∂ν| ≤
      Real.exp n * Real.sqrt n.factorial * ∏ i, pairNorm sc N0 gd (σ i) := by
  have hb (δ : ℝ) (hδ : 0 < δ) : |∫ x : EuclideanSpace ℝ (Fin n), ∏ i, x i ∂ν| ≤
      Real.exp n * Real.sqrt n.factorial * ∏ i, (pairNorm sc N0 gd (σ i) + δ) :=
    moment_prod h _ (fun j => add_pos_of_nonneg_of_pos (pairNorm_nonneg _) hδ)
      fun j => le_add_of_nonneg_right hδ.le
  have hc : Continuous fun δ : ℝ =>
      Real.exp n * Real.sqrt n.factorial * ∏ i, (pairNorm sc N0 gd (σ i) + δ) := by fun_prop
  have hlim := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simp only [add_zero] at hlim
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ => hb δ hδ)

variable {S : Alg →ₗ[ℂ] ℂ} {c : ℕ → Coeffs} {ω : ℕ → (Cfg ℤ → ℂ) → ℂ} {Nm : ℕ → ℕ}

theorem schwinger_growth (h : IsLaw sc N0 gd S σ ν) :
    ‖schwinger S σ‖ ≤ Real.exp n * Real.sqrt n.factorial * ∏ i, pairNorm sc N0 gd (σ i) := by
  rw [schwinger_eq h, Complex.norm_real, Real.norm_eq_abs]
  exact moment_growth h.expBounded

end GGOS.OS

end

end

module

public import GGOS.OS.Work.Growth

/-!
# The two-point function of the curvature ([GG-OS] Theorem 9.4 (iii))
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace GGOS.OS

theorem one_add_sq_le_cosh (y : ℝ) : 1 + y ^ 2 / 2 ≤ Real.cosh y := by
  have h := sum_le_hasSum (Finset.range 2) (fun i _ => div_nonneg (by rw [pow_mul]; positivity)
    (Nat.cast_nonneg _)) (Real.hasSum_cosh y)
  simpa [Finset.sum_range_succ] using h

variable {sc : Scale} {N0 : ℕ} {gd : DensityFn} {n : ℕ} {σ : Fin n → T}
  {ν : Measure (EuclideanSpace ℝ (Fin n))}

theorem sq_moment (h : ExpBounded sc N0 gd σ ν) (j : Fin n) (hE : Enorm sc N0 (σ j) = 0) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => x j ^ 2) ν ∧
      ∫ x : EuclideanSpace ℝ (Fin n), x j ^ 2 ∂ν ≤ Rnorm sc N0 (σ j) ^ 2 := by
  have hprob := h.prob
  set R := Rnorm sc N0 (σ j) with hR
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin n) => x j ^ 2) ν := by
    have := h.integrable_prod fun _ : Fin 2 => j
    simpa only [Fin.prod_univ_two, pow_two] using this
  refine ⟨hint, ?_⟩
  let e (r : ℝ) : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j r
  have hcoord (r : ℝ) (i : Fin n) : e r i = if i = j then r else 0 := by simp [e]
  have hin (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ⟪x, e r⟫ = r * x j := by
    rw [inner_eq_sum]
    simp only [hcoord, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hB (r : ℝ) : expBound sc N0 gd σ (e r) = Real.exp (1 / 2 * (|r| * R) ^ 2) := by
    have h1 (g : Fin n → ℝ) : ∑ i, |e r i| * g i = |r| * g j := by
      rw [Finset.sum_eq_single j]
      · rw [hcoord, ite_eq_left rfl]
      · intro i _ hi
        rw [hcoord, ite_eq_right hi, abs_zero, zero_mul]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    simp only [expBound, h1, hE, mul_zero, add_zero, ← hR]
  have hs (s : ℝ) (hs : 0 < s) : ∫ x : EuclideanSpace ℝ (Fin n), x j ^ 2 ∂ν ≤
      R ^ 2 * Real.exp (s ^ 2 * R ^ 2 / 2) := by
    have h1 := h.exp (e s)
    have h2 := h.exp (e (-s))
    simp only [hin, hB, abs_neg, abs_of_pos hs] at h1 h2
    have hcosh : (fun x : EuclideanSpace ℝ (Fin n) => Real.cosh (s * x j)) =
        fun x => (Real.exp (s * x j) + Real.exp (-s * x j)) / 2 := by
      funext x
      rw [Real.cosh_eq, neg_mul]
    have hci : Integrable (fun x : EuclideanSpace ℝ (Fin n) => Real.cosh (s * x j)) ν := by
      rw [hcosh]
      exact (h1.1.add h2.1).div_const 2
    have hcb : ∫ x : EuclideanSpace ℝ (Fin n), Real.cosh (s * x j) ∂ν ≤
        Real.exp (1 / 2 * (s * R) ^ 2) := by
      rw [hcosh, integral_div, integral_add h1.1 h2.1]
      linarith [h1.2, h2.2]
    have hle : ∫ x : EuclideanSpace ℝ (Fin n), (1 + (s ^ 2 / 2) * x j ^ 2) ∂ν ≤
        ∫ x : EuclideanSpace ℝ (Fin n), Real.cosh (s * x j) ∂ν := by
      refine integral_mono ((integrable_const 1).add (hint.const_mul _)) hci fun x => ?_
      have := one_add_sq_le_cosh (s * x j)
      calc 1 + (s ^ 2 / 2) * x j ^ 2 = 1 + (s * x j) ^ 2 / 2 := by ring
        _ ≤ Real.cosh (s * x j) := this
    rw [integral_add (integrable_const 1) (hint.const_mul _), integral_const_mul, integral_const,
      probReal_univ, one_smul] at hle
    set u := 1 / 2 * (s * R) ^ 2 with hu
    have hu0 : 0 ≤ u := by positivity
    have hexp : Real.exp u - 1 ≤ u * Real.exp u := by
      have h3 := Real.add_one_le_exp (-u)
      have h4 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos u]
    have h5 : s ^ 2 / 2 * ∫ x : EuclideanSpace ℝ (Fin n), x j ^ 2 ∂ν ≤ u * Real.exp u := by
      linarith [hle.trans hcb]
    have h6 : u = s ^ 2 / 2 * R ^ 2 := by rw [hu]; ring
    have h7 : 0 < s ^ 2 / 2 := by positivity
    have h8 : s ^ 2 * R ^ 2 / 2 = u := by rw [h6]; ring
    rw [h8]
    rw [h6, mul_assoc, ← h6] at h5
    exact le_of_mul_le_mul_left h5 h7
  have hc : Continuous fun s : ℝ => R ^ 2 * Real.exp (s ^ 2 * R ^ 2 / 2) := by fun_prop
  have hlim := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_div,
    Real.exp_zero, mul_one] at hlim
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun s h => hs s h)

theorem enorm_of_curv (sc : Scale) (N0 : ℕ) {σ : T} (h : σ.1.2 = 0) : Enorm sc N0 σ = 0 := by
  unfold Enorm
  simp [h]

theorem two_point {S : Alg →ₗ[ℂ] ℂ} {σ : T} (hσ : σ.1.2 = 0)
    {ν : Measure (EuclideanSpace ℝ (Fin 2))} (h : IsLaw sc N0 gd S ![σ, σ] ν) :
    ‖schwinger S ![σ, σ]‖ ≤ Rnorm sc N0 σ ^ 2 := by
  have hprob := h.prob
  have hE := enorm_of_curv sc N0 hσ
  have h0 := sq_moment h.expBounded 0 hE
  have h1 := sq_moment h.expBounded 1 hE
  have e0 : (![σ, σ] : Fin 2 → T) 0 = σ := rfl
  have e1 : (![σ, σ] : Fin 2 → T) 1 = σ := rfl
  rw [e0] at h0
  rw [e1] at h1
  rw [schwinger_eq h, Complex.norm_real, Real.norm_eq_abs]
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin 2) => ∏ i, x i) ν :=
    h.expBounded.integrable_prod id
  calc |∫ x : EuclideanSpace ℝ (Fin 2), ∏ i, x i ∂ν|
      ≤ ∫ x : EuclideanSpace ℝ (Fin 2), |∏ i, x i| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ x : EuclideanSpace ℝ (Fin 2), (x 0 ^ 2 + x 1 ^ 2) / 2 ∂ν := by
        refine integral_mono hint.abs ((h0.1.add h1.1).div_const 2) fun x => ?_
        simp only [Fin.prod_univ_two]
        rw [abs_le]
        constructor
        · nlinarith [sq_nonneg (x 0 + x 1)]
        · nlinarith [sq_nonneg (x 0 - x 1)]
    _ = ((∫ x : EuclideanSpace ℝ (Fin 2), x 0 ^ 2 ∂ν) +
          ∫ x : EuclideanSpace ℝ (Fin 2), x 1 ^ 2 ∂ν) / 2 := by
        rw [integral_div, integral_add h0.1 h1.1]
    _ ≤ Rnorm sc N0 σ ^ 2 := by linarith [h0.2, h1.2]

end GGOS.OS

end

end

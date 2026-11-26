module

public import GGOS.OS.Work.SchwingerLaw

/-!
# The entire extension of the generating function ([GG-OS] Theorem 9.4 (ii))
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace GGOS.OS

/-- The linear form `z ↦ ∑_j z_j x_j`. -/
def linForm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : (Fin n → ℂ) →L[ℂ] ℂ :=
  ∑ j, ((x j : ℝ) : ℂ) • (ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ)

theorem linForm_apply {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (z : Fin n → ℂ) :
    linForm x z = ∑ j, ((x j : ℝ) : ℂ) * z j := by
  simp [linForm]

theorem continuous_linForm {n : ℕ} : Continuous (linForm (n := n)) := by
  unfold linForm
  fun_prop

theorem norm_linForm_le {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ‖linForm x‖ ≤ ∑ j, |x j| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun j _ => abs_nonneg _) fun z => ?_
  rw [linForm_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z j) (abs_nonneg _)

theorem re_linForm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (z : Fin n → ℂ) :
    (linForm x z).re = ∑ j, (z j).re * x j := by
  rw [linForm_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.re_ofReal_mul, mul_comm]

/-- The entire extension. -/
def entireGen {n : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin n))) (z : Fin n → ℂ) : ℂ :=
  ∫ x, Complex.exp (linForm x z) ∂ν

variable {sc : Scale} {N0 : ℕ} {gd : DensityFn} {n : ℕ} {σ : Fin n → T}
  {ν : Measure (EuclideanSpace ℝ (Fin n))}

theorem norm_exp_linForm (x : EuclideanSpace ℝ (Fin n)) (z : Fin n → ℂ) :
    ‖Complex.exp (linForm x z)‖ = Real.exp ⟪x, WithLp.toLp 2 fun j => (z j).re⟫ := by
  rw [Complex.norm_exp, re_linForm, inner_eq_sum]

theorem continuous_exp_linForm (z : Fin n → ℂ) :
    Continuous fun x : EuclideanSpace ℝ (Fin n) => Complex.exp (linForm x z) := by
  have h := continuous_linForm (n := n)
  fun_prop

theorem integrable_exp_linForm (h : ExpBounded sc N0 gd σ ν) (z : Fin n → ℂ) :
    Integrable (fun x => Complex.exp (linForm x z)) ν := by
  refine ((h.exp (WithLp.toLp 2 fun j => (z j).re)).1).mono'
    (continuous_exp_linForm z).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  exact (norm_exp_linForm x z).le

theorem differentiable_entireGen (h : ExpBounded sc N0 gd σ ν) :
    Differentiable ℂ (entireGen ν) := by
  intro z0
  have hprob := h.prob
  have hb := (h.exp_abs fun j => |(z0 j).re| + 2).1
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ) (μ := ν)
    (F := fun (z : Fin n → ℂ) (x : EuclideanSpace ℝ (Fin n)) => Complex.exp (linForm x z))
    (F' := fun (z : Fin n → ℂ) (x : EuclideanSpace ℝ (Fin n)) =>
      Complex.exp (linForm x z) • linForm x)
    (x₀ := z0) (s := Metric.ball z0 1)
    (bound := fun x => Real.exp (∑ j, (|(z0 j).re| + 2) * |x j|))
    (Metric.ball_mem_nhds z0 one_pos)
    (Eventually.of_forall fun z => (continuous_exp_linForm z).aestronglyMeasurable)
    (integrable_exp_linForm h z0)
    ((continuous_exp_linForm z0).smul continuous_linForm).aestronglyMeasurable
    (Eventually.of_forall fun x z hz => ?_) hb
    (Eventually.of_forall fun x z _ => (linForm x).hasFDerivAt.cexp)
  · exact hmain.differentiableAt
  · rw [norm_smul, Complex.norm_exp, re_linForm]
    have hzj (j : Fin n) : (z j).re * x j ≤ (|(z0 j).re| + 1) * |x j| := by
      have h1 : |(z j).re - (z0 j).re| ≤ 1 := by
        have h2 : ‖z j - z0 j‖ ≤ ‖z - z0‖ := norm_le_pi_norm (z - z0) j
        have h3 : ‖z - z0‖ < 1 := by rwa [← dist_eq_norm, ← Metric.mem_ball]
        have h4 := Complex.abs_re_le_norm (z j - z0 j)
        rw [Complex.sub_re] at h4
        linarith
      have h5 : |(z j).re| ≤ |(z0 j).re| + 1 := by
        have := abs_sub_abs_le_abs_sub (z j).re (z0 j).re
        linarith
      calc (z j).re * x j ≤ |(z j).re * x j| := le_abs_self _
        _ = |(z j).re| * |x j| := abs_mul _ _
        _ ≤ (|(z0 j).re| + 1) * |x j| := mul_le_mul_of_nonneg_right h5 (abs_nonneg _)
    have h6 : ∑ j, (z j).re * x j ≤ ∑ j, (|(z0 j).re| + 1) * |x j| :=
      Finset.sum_le_sum fun j _ => hzj j
    have h7 : ‖linForm x‖ ≤ Real.exp (∑ j, |x j|) :=
      (norm_linForm_le x).trans ((by linarith : ∑ j, |x j| ≤ ∑ j, |x j| + 1).trans
        (Real.add_one_le_exp _))
    calc Real.exp (∑ j, (z j).re * x j) * ‖linForm x‖
        ≤ Real.exp (∑ j, (|(z0 j).re| + 1) * |x j|) * Real.exp (∑ j, |x j|) :=
          mul_le_mul (Real.exp_le_exp.mpr h6) h7 (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (∑ j, (|(z0 j).re| + 2) * |x j|) := by
          rw [← Real.exp_add, ← Finset.sum_add_distrib]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          ring

theorem norm_entireGen_le (h : ExpBounded sc N0 gd σ ν) (z : Fin n → ℂ) :
    ‖entireGen ν z‖ ≤ (entireGen ν fun j => ((z j).re : ℂ)).re ∧
      ‖entireGen ν z‖ ≤ expBound sc N0 gd σ fun j => (z j).re := by
  have h1 : ‖entireGen ν z‖ ≤ ∫ x, Real.exp ⟪x, WithLp.toLp 2 fun j => (z j).re⟫ ∂ν := by
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact norm_exp_linForm x z
  have h2 : entireGen ν (fun j => ((z j).re : ℂ)) =
      ((∫ x, Real.exp ⟪x, WithLp.toLp 2 fun j => (z j).re⟫ ∂ν : ℝ) : ℂ) := by
    unfold entireGen
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [linForm_apply, inner_eq_sum, Complex.ofReal_exp, Complex.ofReal_sum,
      Complex.ofReal_mul]
    congr 1
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine ⟨?_, h1.trans (h.exp _).2⟩
  rw [h2, Complex.ofReal_re]
  exact h1

theorem entireGen_imag {S : Alg →ₗ[ℂ] ℂ} (h : IsLaw sc N0 gd S σ ν) (t : Fin n → ℝ) :
    entireGen ν (fun j => Complex.I * (t j : ℂ)) = genFun S σ t := by
  have hc : genFun S σ t = charFun ν (WithLp.toLp 2 t) := (h.char _).symm
  rw [hc, charFun_apply]
  unfold entireGen
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [linForm_apply, inner_eq_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end GGOS.OS

end

end

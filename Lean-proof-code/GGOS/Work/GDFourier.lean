module

public import Mathlib

/-!
# Characters, product series and termwise integration for Gaussian domination
-/

@[expose] public section

open MeasureTheory Real Set Filter
open scoped Topology

namespace GGOS.Work.GD

/-- The unit-period character on the real line. -/
noncomputable def wave (x : ℝ) : ℂ := Complex.exp ((2 * π * x : ℝ) * Complex.I)

@[simp] theorem wave_zero : wave 0 = 1 := by simp [wave]

theorem wave_add (x y : ℝ) : wave (x + y) = wave x * wave y := by
  simp [wave, mul_add, add_mul, Complex.exp_add]

@[simp] theorem norm_wave (x : ℝ) : ‖wave x‖ = 1 := by
  simp [wave, Complex.norm_exp]

theorem wave_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    wave (∑ i ∈ s, f i) = ∏ i ∈ s, wave (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, wave_add, ih]

@[simp] theorem wave_int (k : ℤ) : wave k = 1 := by
  unfold wave
  convert Complex.exp_int_mul_two_pi_mul_I k using 2
  push_cast
  ring

/-- Orthogonality on an interval of one full period, including its unnormalized mass. -/
theorem integral_wave_period (l L : ℝ) (hL : 0 < L) (k : ℤ) :
    ∫ x in Ioc l (l + L), wave (k * (x / L)) =
      if k = 0 then (L : ℂ) else 0 := by
  rw [← intervalIntegral.integral_of_le (by linarith only [hL])]
  by_cases hk : k = 0
  · simp [hk]
  simp only [hk, ↓reduceIte]
  let w : ℂ := (2 * (π : ℂ) * k / L) * Complex.I
  have he (x : ℝ) : wave (k * (x / L)) = Complex.exp (w * x) := by
    unfold wave w
    push_cast
    ring_nf
  simp_rw [he]
  rw [integral_exp_mul_complex]
  · rw [← he, ← he, show (k : ℝ) * ((l + L) / L) = k * (l / L) + k by
      field_simp, wave_add, wave_int, mul_one, sub_self, zero_div]
  · dsimp [w]
    exact mul_ne_zero (div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr pi_ne_zero)) (Int.cast_ne_zero.mpr hk))
      (Complex.ofReal_ne_zero.mpr hL.ne')) Complex.I_ne_zero

private theorem pi_count_int {ι : Type*} [Fintype ι] :
    (Measure.pi fun _ : ι => (Measure.count : Measure ℤ)) = Measure.count := by
  apply Measure.ext_of_singleton
  simp

/-- Absolute convergence over all integer fields follows coordinate by coordinate. -/
theorem summable_prod {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜] {f : ι → ℤ → 𝕜}
    (hf : ∀ i, Summable (f i)) : Summable (fun m : ι → ℤ => ∏ i, f i (m i)) := by
  have h := Integrable.fintype_prod (μ := fun _ => Measure.count)
    (fun i => integrable_count_iff.mpr (hf i).norm)
  rw [pi_count_int, integrable_count_iff] at h
  exact h.of_norm

/-- Fubini for a finite product of absolutely summable integer series. -/
theorem tsum_prod {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜] {f : ι → ℤ → 𝕜}
    (hf : ∀ i, Summable (f i)) :
    (∑' m : ι → ℤ, ∏ i, f i (m i)) = ∏ i, ∑' k, f i k := by
  have h (i) : Integrable (f i) Measure.count := integrable_count_iff.mpr (hf i).norm
  have hp := Integrable.fintype_prod (μ := fun _ => Measure.count) h
  rw [pi_count_int] at hp
  have hi := integral_fintype_prod_eq_prod (μ := fun _ => Measure.count) f
  rw [pi_count_int, integral_countable hp] at hi
  simpa [integral_countable (h _), measureReal_def] using hi

/-- A summable majorant uniform almost everywhere on a finite measure space licenses integration
of a series term by term. -/
theorem hasSum_integral_bounded {ι X E : Type*} [Countable ι] [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure X} [IsFiniteMeasure μ] {F : ι → X → E} {g : ι → ℝ} {f : X → E}
    (hg : Summable g) (hm : ∀ i, AEStronglyMeasurable (F i) μ)
    (hb : ∀ i, ∀ᵐ x ∂μ, ‖F i x‖ ≤ g i) (hf : ∀ᵐ x ∂μ, HasSum (fun i => F i x) (f x)) :
    HasSum (fun i => ∫ x, F i x ∂μ) (∫ x, f x ∂μ) :=
  hasSum_integral_of_dominated_convergence (fun i _ => g i) hm hb
    (ae_of_all _ fun _ => hg) (integrable_const _) hf

end GGOS.Work.GD

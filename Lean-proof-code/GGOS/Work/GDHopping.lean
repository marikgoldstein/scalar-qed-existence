module

public import GGOS.Work.GDFourier
public import GGOS.Frozen.Defs.Hop

/-!
# Positivity of the integer Fourier coefficients of the hopping weight
-/

@[expose] public section

open MeasureTheory Real Set
open scoped ComplexOrder

namespace GGOS.Work.GD

/-- One full period of a bond variable. -/
noncomputable def period (c : Coeffs) : ℝ := 2 * π / c.γ

theorem period_pos (c : Coeffs) : 0 < period c := div_pos (mul_pos two_pos pi_pos) c.γ_pos

private theorem cos_mul_wave (t : ℝ) (k : ℤ) :
    (Real.cos (2 * π * t) : ℂ) * wave (k * t) =
      (1 / 2 : ℂ) * (wave ((k + 1 : ℤ) * t) + wave ((k - 1 : ℤ) * t)) := by
  have h : (2 : ℂ) * (Real.cos (2 * π * t) : ℂ) = wave t + wave (-t) := by
    rw [Complex.ofReal_cos, Complex.two_cos]
    simp [wave]
  simp only [Int.cast_add, Int.cast_one, Int.cast_sub]
  rw [add_mul, sub_mul, one_mul, sub_eq_add_neg, wave_add, wave_add, ← mul_add, ← h]
  ring

private theorem integral_cos_pow_wave_nonneg (l L : ℝ) (hL : 0 < L) (n : ℕ) (k : ℤ) :
    0 ≤ ∫ x in Ioc l (l + L), (Real.cos (2 * π * (x / L)) : ℂ) ^ n * wave (k * (x / L)) := by
  let F (j : ℕ) (q : ℤ) (x : ℝ) :=
    (Real.cos (2 * π * (x / L)) : ℂ) ^ j * wave (q * (x / L))
  change 0 ≤ ∫ x in Ioc l (l + L), F n k x
  have hint (j q) : IntegrableOn (F j q) (Ioc l (l + L)) := by
    have hc : Continuous (F j q) := by unfold F wave; fun_prop
    exact hc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  induction n generalizing k with
  | zero =>
    simp only [F, pow_zero, one_mul, integral_wave_period _ _ hL]
    split <;> positivity
  | succ n ih =>
    have he (x : ℝ) : F (n+1) k x = (1 / 2 : ℂ) * (F n (k+1) x + F n (k-1) x) := by
      unfold F
      rw [pow_succ, mul_assoc, cos_mul_wave]
      ring
    simp_rw [he]
    rw [integral_const_mul, integral_add (hint _ _) (hint _ _)]
    apply mul_nonneg _ (add_nonneg (ih _) (ih _))
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      (Complex.zero_le_real.mpr (by norm_num : (0 : ℝ) ≤ 1 / 2))

/-- Expanding the exponential in powers of cosine proves Fourier positivity without Bessel
functions. The exponential series gives the summable bound uniformly on the period. -/
theorem integral_exp_cos_wave_nonneg (l L : ℝ) (hL : 0 < L) {z : ℝ} (hz : 0 ≤ z) (k : ℤ) :
    0 ≤ ∫ x in Ioc l (l + L),
      (Real.exp (z * Real.cos (2 * π * (x / L))) : ℂ) * wave (k * (x / L)) := by
  let F (n : ℕ) (x : ℝ) := ((z ^ n / n.factorial : ℝ) : ℂ) *
    ((Real.cos (2 * π * (x / L)) : ℂ) ^ n * wave (k * (x / L)))
  have hs := (NormedSpace.expSeries_div_hasSum_exp z).summable
  have h := hasSum_integral_bounded (μ := volume.restrict (Ioc l (l + L))) (F := F)
    (f := fun x => (Real.exp (z * Real.cos (2 * π * (x / L))) : ℂ) * wave (k * (x / L))) hs
    (fun n => by unfold F wave; fun_prop) (fun n => ae_of_all _ fun x => by
      dsimp only [F]
      simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ z ^ n / n.factorial),
        norm_pow, norm_wave, mul_one]
      apply mul_le_of_le_one_right (by positivity)
      apply pow_le_one₀ (norm_nonneg _)
      exact Real.abs_cos_le_one _) (ae_of_all _ fun x => by
      have he := (NormedSpace.expSeries_div_hasSum_exp
        ((z : ℂ) * (Real.cos (2 * π * (x / L)) : ℂ))).mul_right (wave (k * (x / L)))
      rw [← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_mul, ← Complex.ofReal_exp] at he
      exact he.congr_fun (fun n => by simp only [F, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_mul, mul_pow]; ring))
  rw [← h.tsum_eq]
  apply tsum_nonneg
  intro n
  simp only [F, integral_const_mul]
  exact mul_nonneg (Complex.zero_le_real.mpr (by positivity)) (integral_cos_pow_wave_nonneg _ _ hL _ _)

private theorem hop_factor (c : Coeffs) (r r' x : ℝ) :
    hop c r r' x =
      Real.exp (-(c.κ / 2) * ((c.ρ0 + r) ^ 2 + (c.ρ0 + r') ^ 2)) *
      Real.exp (c.κ * (c.ρ0 + r) * (c.ρ0 + r') * Real.cos (2 * π * (x / period c))) := by
  have ha : c.γ * x = 2 * π * (x / period c) := by
    unfold period
    field_simp [pi_ne_zero, c.γ_pos.ne']
  unfold hop
  rw [← Real.exp_add, Real.exp_injective.eq_iff, Complex.sq_norm, Complex.normSq_sub,
    Complex.normSq_mul, ← Complex.sq_norm (Complex.exp _)]
  simp [-Complex.ofReal_add, Complex.norm_exp, Complex.exp_re, mul_comm Complex.I, ha,
    Complex.normSq_ofReal]
  ring

/-- On the support of the radial measure every bond Fourier coefficient is real and nonnegative. -/
theorem integral_hop_wave_nonneg (c : Coeffs) {r r' : ℝ}
    (hr : 0 ≤ c.ρ0 + r) (hr' : 0 ≤ c.ρ0 + r') (k : ℤ) :
    0 ≤ ∫ x in Ioc (-(π / c.γ)) (π / c.γ), (hop c r r' x : ℂ) * wave (k * (x / period c)) := by
  simp_rw [hop_factor, Complex.ofReal_mul, mul_assoc, integral_const_mul]
  apply mul_nonneg (Complex.zero_le_real.mpr (Real.exp_pos _).le)
  have h := integral_exp_cos_wave_nonneg (-(π / c.γ)) (period c) (period_pos c)
    (mul_nonneg (mul_nonneg c.κ_nonneg hr) hr') k
  rw [show -(π / c.γ) + period c = π / c.γ by unfold period; ring] at h
  simpa only [mul_assoc] using h

end GGOS.Work.GD

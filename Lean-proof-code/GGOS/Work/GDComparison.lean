module

public import GGOS.Work.GDDual

/-!
# The shifted closed-sector bond partition is maximal at zero
-/

public section

open MeasureTheory
open scoped ComplexOrder

namespace GGOS.Work.GD

variable (s : Side) (c : Coeffs)

private theorem integrable_modulatedSum (a : Plaq (ZMod s.n) → ℝ) (r : Site (ZMod s.n) → ℝ) :
    Integrable (modulatedSum s c a r) (cubeMeasure (Site (ZMod s.n))) := by
  let F (m : Plaq (ZMod s.n) → ℤ) (t : Site (ZMod s.n) → ℝ) :=
    (sectorIntegral s c a r m : ℂ) * wave (∑ p, cubeAdj t p * m p)
  have hn (m t) : ‖F m t‖ = sectorIntegral s c a r m := by
    simp [F, Real.norm_of_nonneg (sectorIntegral_nonneg ..)]
  apply (integrable_const (∑' m, sectorIntegral s c a r m)).mono'
  · apply StronglyMeasurable.aestronglyMeasurable
    apply StronglyMeasurable.tsum
    intro m
    apply Continuous.stronglyMeasurable
    unfold cubeAdj wave
    fun_prop
  filter_upwards with t
  change ‖∑' m, F m t‖ ≤ _
  have hs : Summable (fun m => ‖F m t‖) := by simpa only [hn] using summable_sectorIntegral s c a r
  simpa only [hn] using norm_tsum_le_tsum_norm hs

/-- After dualization each summand is a nonnegative weight times a unit phase. -/
private theorem modulatedSum_re_le (a : Plaq (ZMod s.n) → ℝ) {r : Site (ZMod s.n) → ℝ}
    (hr : ∀ x, 0 ≤ c.ρ0 + r x) (t : Site (ZMod s.n) → ℝ) :
    (modulatedSum s c a r t).re ≤ (modulatedSum s c 0 r t).re := by
  let w := dualWeight s c r (cubeAdj t)
  have hw (m) : 0 ≤ w m :=
    mul_nonneg (Complex.zero_le_real.mpr (coeffProd_pos (width_pos c) _ _).le)
      (hopFourier_nonneg s c hr m)
  have hs : Summable w := summable_dualWeight s c r _
  have hn (m) : ‖w m * sourceWave s c a (cubeAdj t) m‖ = ‖w m‖ := by
    simp only [sourceWave, norm_mul, norm_wave, mul_one]
  rw [modulatedSum_eq_dual, modulatedSum_eq_dual]
  simp only [sourceWave, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_div, neg_zero,
    wave_zero, mul_one]
  change (∑' m, w m * sourceWave s c a (cubeAdj t) m).re ≤ (∑' m, w m).re
  calc
    _ ≤ ‖∑' m, w m * sourceWave s c a (cubeAdj t) m‖ := Complex.re_le_norm _
    _ ≤ ∑' m, ‖w m * sourceWave s c a (cubeAdj t) m‖ :=
      norm_tsum_le_tsum_norm (by simpa only [hn] using hs.norm)
    _ = _ := by simp_rw [hn, ← Complex.re_eq_norm.mpr (hw _), Complex.re_tsum hs]

private theorem closedIntegral_eq_integral (a : Plaq (ZMod s.n) → ℝ) (r : Site (ZMod s.n) → ℝ) :
    closedIntegral s c a r = ∫ t, (modulatedSum s c a r t).re ∂cubeMeasure (Site (ZMod s.n)) := by
  have hs : Summable (fun m => (sectorIntegral s c a r m : ℂ)) :=
    (Complex.hasSum_ofReal.mpr (summable_sectorIntegral s c a r).hasSum).summable
  have hc : (closedIntegral s c a r : ℂ) =
      ∫ t, modulatedSum s c a r t ∂cubeMeasure (Site (ZMod s.n)) := by
    rw [closedIntegral, Complex.ofReal_tsum]
    exact closed_tsum_eq_integral hs
  exact (congrArg Complex.re hc).trans (integral_re (integrable_modulatedSum s c a r)).symm

/-- Gaussian domination at fixed physical radii, before multiplication by the radial weight. -/
theorem closedIntegral_le_zero_shift (a : Plaq (ZMod s.n) → ℝ) {r : Site (ZMod s.n) → ℝ}
    (hr : ∀ x, 0 ≤ c.ρ0 + r x) : closedIntegral s c a r ≤ closedIntegral s c 0 r := by
  rw [closedIntegral_eq_integral, closedIntegral_eq_integral]
  exact integral_mono (integrable_modulatedSum s c a r).re (integrable_modulatedSum s c 0 r).re
    (modulatedSum_re_le s c a hr)

end GGOS.Work.GD

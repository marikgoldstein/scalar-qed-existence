module

public import GGOS.Work.GDKernels
public import GGOS.Work.GDProjector

/-!
# Dual plaquette weights and the bond integral at fixed radial variables
-/

@[expose] public section

open MeasureTheory Real Set
open scoped ComplexOrder

namespace GGOS.Work.GD

variable (s : Side) (c : Coeffs)

/-- The bond character of an integer dual field, integrated against the hopping weight. -/
noncomputable def hopFourier (r : Site (ZMod s.n) → ℝ) (m : Plaq (ZMod s.n) → ℤ) : ℂ :=
  ∫ B, (hoppingProd s c r B : ℂ) * wave ((∑ b, (bondFreq m b : ℝ) * B b) / period c)
    ∂bondMeasure s c

theorem hopFourier_nonneg {r : Site (ZMod s.n) → ℝ} (hr : ∀ x, 0 ≤ c.ρ0 + r x)
    (m : Plaq (ZMod s.n) → ℤ) : 0 ≤ hopFourier s c r m := by
  let f (b : Bond (ZMod s.n)) (x : ℝ) :=
    (hop c (r b.1) (r (b.1 + unitVec (ZMod s.n) b.2)) x : ℂ) *
      wave (bondFreq m b * (x / period c))
  unfold hopFourier hoppingProd bondMeasure
  simp only [Finset.sum_div, mul_div_assoc, wave_sum, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod f]
  exact Finset.prod_nonneg fun b _ => integral_hop_wave_nonneg c (hr _) (hr _) (bondFreq m b)

theorem norm_hopFourier_le (r : Site (ZMod s.n) → ℝ) (m : Plaq (ZMod s.n) → ℤ) :
    ‖hopFourier s c r m‖ ≤ (bondMeasure s c).real univ := by
  refine (norm_integral_le_of_norm_le_const (C := 1) (f := fun B =>
    (hoppingProd s c r B : ℂ) * wave ((∑ b, (bondFreq m b : ℝ) * B b) / period c)) ?_).trans_eq
    (one_mul _)
  exact ae_of_all _ fun B => by
    simpa only [norm_mul, norm_wave, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (hoppingProd_pos s c r B).le] using hoppingProd_le_one s c r B

/-- The source-dependent phase. -/
noncomputable def sourceWave (a q : Plaq (ZMod s.n) → ℝ) (m : Plaq (ZMod s.n) → ℤ) : ℂ :=
  wave (-((∑ p, ((m p : ℝ) - q p) * a p) / period c))

/-- The cube-adjoint part of a frequency drops out when paired with the bond curl. -/
theorem split_wave (a : Plaq (ZMod s.n) → ℝ) (t : Site (ZMod s.n) → ℝ)
    (m : Plaq (ZMod s.n) → ℤ) (B : Bond (ZMod s.n) → ℝ) :
    wave (∑ p, ((m p : ℝ) - cubeAdj t p) * displacement s c a B p) =
      wave ((∑ b, (bondFreq m b : ℝ) * B b) / period c) * sourceWave s c a (cubeAdj t) m := by
  unfold sourceWave displacement
  rw [← wave_add, pair_bondFreq]
  congr 1
  simp_rw [← mul_div_assoc, ← Finset.sum_div, mul_sub, Finset.sum_sub_distrib]
  simp_rw [sub_mul, Finset.sum_sub_distrib, pair_cubeAdj_dBond, sub_zero]
  ring

/-- Fourier-modulated sum of the original bond integrals. -/
noncomputable def modulatedSum (a : Plaq (ZMod s.n) → ℝ) (r t : Site (ZMod s.n) → ℝ) : ℂ :=
  ∑' m, (sectorIntegral s c a r m : ℂ) * wave (∑ p, cubeAdj t p * m p)

private theorem tsum_integral_bounded {ι X : Type*} [Countable ι] [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {F : ι → X → ℂ} {g : ι → ℝ}
    (hg : Summable g) (hm : ∀ i, AEStronglyMeasurable (F i) μ)
    (hb : ∀ᵐ x ∂μ, ∀ i, ‖F i x‖ ≤ g i) :
    (∑' i, ∫ x, F i x ∂μ) = ∫ x, ∑' i, F i x ∂μ := by
  apply HasSum.tsum_eq
  apply hasSum_integral_bounded hg hm (fun i => hb.mono fun x hx => hx i)
  exact hb.mono fun _ hx => (hg.of_norm_bounded hx).hasSum

private theorem modulatedSum_integral (a : Plaq (ZMod s.n) → ℝ) (r t : Site (ZMod s.n) → ℝ) :
    modulatedSum s c a r t = ∫ B, (hoppingProd s c r B : ℂ) *
      ∑' m, (gaussProd (width c) (displacement s c a B) m : ℂ) * wave (∑ p, cubeAdj t p * m p)
        ∂bondMeasure s c := by
  let F (m : Plaq (ZMod s.n) → ℤ) (B : Bond (ZMod s.n) → ℝ) := (hoppingProd s c r B : ℂ) *
    ((gaussProd (width c) (displacement s c a B) m : ℂ) * wave (∑ p, cubeAdj t p * m p))
  obtain ⟨g, hg, hb⟩ := shifted_majorant s c a
  have h := tsum_integral_bounded (μ := bondMeasure s c) (F := F) hg
    (fun _ => by apply Continuous.aestronglyMeasurable; unfold F hoppingProd hop gaussProd gauss
                   displacement dBond; fun_prop) (hb.mono fun B hB m => by
      simp only [F, norm_mul, norm_wave, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (hoppingProd_pos ..).le, Real.norm_of_nonneg (gaussProd_pos ..).le]
      exact (mul_le_of_le_one_left (gaussProd_pos ..).le (hoppingProd_le_one ..)).trans (hB m))
  calc
    _ = ∑' m, ∫ B, F m B ∂bondMeasure s c := by
      apply tsum_congr
      intro m
      simp only [F, ← mul_assoc, ← Complex.ofReal_mul, integral_mul_const, integral_complex_ofReal,
        sectorIntegral]
    _ = _ := by simpa only [F, tsum_mul_left] using h

/-- The positive dual weight has no source dependence. -/
noncomputable def dualWeight (r : Site (ZMod s.n) → ℝ) (q : Plaq (ZMod s.n) → ℝ)
    (m : Plaq (ZMod s.n) → ℤ) : ℂ := (coeffProd (width c) q m : ℂ) * hopFourier s c r m

theorem summable_dualWeight (r : Site (ZMod s.n) → ℝ) (q : Plaq (ZMod s.n) → ℝ) :
    Summable (dualWeight s c r q) := by
  apply ((summable_coeffProd (width_pos c) q).mul_right ((bondMeasure s c).real univ)).of_norm_bounded
  intro m
  simp only [dualWeight, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (coeffProd_pos (width_pos c) q m).le]
  exact mul_le_mul_of_nonneg_left (norm_hopFourier_le s c r m) (coeffProd_pos (width_pos c) q m).le

/-- Equation (3.3) before radial integration, at a fixed cube multiplier. -/
theorem modulatedSum_eq_dual (a : Plaq (ZMod s.n) → ℝ) (r t : Site (ZMod s.n) → ℝ) :
    modulatedSum s c a r t = ∑' m, dualWeight s c r (cubeAdj t) m * sourceWave s c a (cubeAdj t) m := by
  let F (m : Plaq (ZMod s.n) → ℤ) (B : Bond (ZMod s.n) → ℝ) := (hoppingProd s c r B : ℂ) *
    ((coeffProd (width c) (cubeAdj t) m : ℂ) *
       wave (∑ p, ((m p : ℝ) - cubeAdj t p) * displacement s c a B p))
  have h := tsum_integral_bounded (μ := bondMeasure s c) (F := F) (summable_coeffProd (width_pos c) (cubeAdj t))
    (fun _ => by apply Continuous.aestronglyMeasurable; unfold F hoppingProd hop wave displacement dBond; fun_prop)
    (ae_of_all _ fun B m => by
      simp only [F, norm_mul, norm_wave, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (hoppingProd_pos ..).le, Real.norm_of_nonneg (coeffProd_pos (width_pos c) _ _).le]
      exact mul_le_of_le_one_left (coeffProd_pos (width_pos c) _ _).le (hoppingProd_le_one ..))
  rw [modulatedSum_integral]
  simp_rw [poisson_prod (width_pos c) _ (cubeAdj t), ← tsum_mul_left]
  change (∫ B, ∑' m, F m B ∂bondMeasure s c) = _
  rw [← h]
  apply tsum_congr
  intro m
  have he (B) : F m B = (coeffProd (width c) (cubeAdj t) m : ℂ) *
      ((hoppingProd s c r B : ℂ) * wave ((∑ b, (bondFreq m b : ℝ) * B b) / period c)) *
        sourceWave s c a (cubeAdj t) m := by
    unfold F
    rw [split_wave]
    ring
  simp only [he, integral_mul_const, integral_const_mul, dualWeight, hopFourier]

end GGOS.Work.GD

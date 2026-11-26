module

public import GGOS.Work.GDComparison

/-!
# The Gaussian tilt in the torus measure
-/

@[expose] public section

open MeasureTheory Real Set
open scoped ENNReal

namespace GGOS.Work.GD

variable (s : Side) (c : Coeffs)

/-- The physical exponential observable and the scalar from completing its square. -/
noncomputable def tilt (a : Plaq (ZMod s.n) → ℝ) (ω : Cfg (ZMod s.n)) : ℝ :=
  Real.exp (∑ p, a p * ω.1 p)

noncomputable def prefactor (a : Plaq (ZMod s.n) → ℝ) : ℝ := Real.exp (1 / 2 * ∑ p, a p ^ 2)

noncomputable def siteProd (r : Site (ZMod s.n) → ℝ) : ℝ := ∏ x, siteFactor c (r x)

private theorem scalar_square (a : Plaq (ZMod s.n) → ℝ) (B : Bond (ZMod s.n) → ℝ)
    (m : Plaq (ZMod s.n) → ℤ) (p : Plaq (ZMod s.n)) :
    Real.exp (-(curv c B m p) ^ 2 / 2) * Real.exp (a p * curv c B m p) =
      Real.exp (1 / 2 * a p ^ 2) * gauss (width c) (m p + displacement s c a B p) := by
  rw [gauss, ← Real.exp_add, ← Real.exp_add]
  apply congrArg Real.exp
  change -((dBond B p + period c * (m p : ℝ)) ^ 2) / 2 +
      a p * (dBond B p + period c * (m p : ℝ)) =
    1 / 2 * a p ^ 2 + -π * (period c ^ 2 / (2 * π)) * (m p + (dBond B p - a p) / period c) ^ 2
  field_simp [pi_ne_zero, (period_pos c).ne']
  ring

private theorem weight_mul_tilt (a : Plaq (ZMod s.n) → ℝ) (r : Site (ZMod s.n) → ℝ)
    (B : Bond (ZMod s.n) → ℝ) (m : Plaq (ZMod s.n) → ℤ) :
    weight s c r B m * tilt s a (curv c B m, r) =
      prefactor s a * (siteProd s c r * (hoppingProd s c r B *
        gaussProd (width c) (displacement s c a B) m)) := by
  have h := Finset.prod_congr (s₁ := Finset.univ) rfl (fun p _ => scalar_square s c a B m p)
  simp only [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum] at h
  change siteProd s c r * hoppingProd s c r B * _ * _ = _
  rw [mul_assoc (siteProd s c r * hoppingProd s c r B)]
  unfold tilt prefactor gaussProd
  simp only [← Real.exp_sum]
  rw [h]
  ring

/-- The unnormalised moment generating integral, retained in the extended nonnegative reals. -/
noncomputable def tiltedMass (a : Plaq (ZMod s.n) → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (tilt s a ω) ∂torusMeasure s c

local instance : SFinite (bondMeasure s c) := by unfold bondMeasure; infer_instance

private theorem measurable_sectorIntegral (a : Plaq (ZMod s.n) → ℝ) (m : Plaq (ZMod s.n) → ℤ) :
    Measurable (fun r => sectorIntegral s c a r m) := by
  apply StronglyMeasurable.measurable
  unfold sectorIntegral
  apply StronglyMeasurable.integral_prod_right (ν := bondMeasure s c)
  apply Continuous.stronglyMeasurable
  unfold Function.uncurry hoppingProd hop gaussProd gauss displacement dBond
  fun_prop

private theorem lintegral_sector (a : Plaq (ZMod s.n) → ℝ) (m : Plaq (ZMod s.n) → ℤ) :
    (∫⁻ ω, ENNReal.ofReal (tilt s a ω) ∂Measure.map
      (fun x : (Site (ZMod s.n) → ℝ) × (Bond (ZMod s.n) → ℝ) => (curv c x.2 m, x.1))
      (((siteMeasure s c).prod (bondMeasure s c)).withDensity
        (fun x => ENNReal.ofReal (weight s c x.1 x.2 m)))) =
    ENNReal.ofReal (prefactor s a) * ∫⁻ r, ENNReal.ofReal (siteProd s c r) *
      ENNReal.ofReal (sectorIntegral s c a r m) ∂siteMeasure s c := by
  let S (r : Site (ZMod s.n) → ℝ) := ENNReal.ofReal (siteProd s c r)
  let G (r : Site (ZMod s.n) → ℝ) (B : Bond (ZMod s.n) → ℝ) :=
    ENNReal.ofReal (hoppingProd s c r B * gaussProd (width c) (displacement s c a B) m)
  have ht : Measurable (fun ω => ENNReal.ofReal (tilt s a ω)) := by unfold tilt; fun_prop
  have hmap : Measurable (fun x : (Site (ZMod s.n) → ℝ) × (Bond (ZMod s.n) → ℝ) =>
      (curv c x.2 m, x.1)) := by unfold curv dBond; fun_prop
  have hw : Measurable (fun x : (Site (ZMod s.n) → ℝ) × (Bond (ZMod s.n) → ℝ) =>
      ENNReal.ofReal (weight s c x.1 x.2 m)) := by
    unfold weight hop siteFactor curv dBond
    fun_prop
  rw [lintegral_map ht hmap, lintegral_withDensity_eq_lintegral_mul _ hw
    (g := fun x => ENNReal.ofReal (tilt s a (curv c x.2 m, x.1))) (ht.comp hmap)]
  calc
    _ = ∫⁻ x, ENNReal.ofReal (prefactor s a) * (S x.1 * G x.1 x.2)
        ∂(siteMeasure s c).prod (bondMeasure s c) := by
      apply lintegral_congr
      intro x
      change ENNReal.ofReal (weight s c x.1 x.2 m) *
        ENNReal.ofReal (tilt s a (curv c x.2 m, x.1)) = _
      have he : 0 ≤ tilt s a (curv c x.2 m, x.1) := (Real.exp_pos _).le
      have hp : 0 ≤ prefactor s a := (Real.exp_pos _).le
      have hg := mul_pos (hoppingProd_pos s c x.1 x.2)
        (gaussProd_pos (width c) (displacement s c a x.2) m)
      rw [← ENNReal.ofReal_mul' he, weight_mul_tilt, ENNReal.ofReal_mul hp, ENNReal.ofReal_mul' hg.le]
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_prod]
      · congr 1
        apply lintegral_congr
        intro r
        change (∫⁻ B, S r * G r B ∂bondMeasure s c) = _
        rw [lintegral_const_mul' (S r) (G r) (show S r ≠ ⊤ from ENNReal.ofReal_ne_top)]
        congr 1
        exact (ofReal_integral_eq_lintegral_ofReal (integrable_sector s c a r m)
          (ae_of_all _ fun _ => (mul_pos (hoppingProd_pos ..) (gaussProd_pos ..)).le)).symm
      · apply Measurable.aemeasurable
        unfold S G siteProd siteFactor hoppingProd hop gaussProd gauss displacement dBond
        fun_prop

theorem tiltedMass_eq (a : Plaq (ZMod s.n) → ℝ) :
    tiltedMass s c a = ENNReal.ofReal (prefactor s a) *
      ∫⁻ r, ENNReal.ofReal (siteProd s c r) * ENNReal.ofReal (closedIntegral s c a r) ∂siteMeasure s c := by
  unfold tiltedMass torusMeasure
  rw [lintegral_sum_measure]
  simp_rw [lintegral_sector, ENNReal.tsum_mul_left]
  congr 1
  rw [← lintegral_tsum]
  · apply lintegral_congr
    intro r
    rw [ENNReal.tsum_mul_left, closedIntegral, ENNReal.ofReal_tsum_of_nonneg
      (f := fun m : {v : Plaq (ZMod s.n) → ℤ // IsClosedForm v} => sectorIntegral s c a r m.1)
      (fun m => sectorIntegral_nonneg s c a r m.1)
      ((summable_sectorIntegral s c a r).comp_injective Subtype.val_injective)]
  · intro m
    apply Measurable.aemeasurable
    exact (by unfold siteProd siteFactor; fun_prop : Measurable (fun r => ENNReal.ofReal (siteProd s c r))).mul
      (ENNReal.measurable_ofReal.comp (measurable_sectorIntegral s c a m.1))

/-- The sharp unnormalised estimate, including finiteness of the tilted integral. -/
theorem tiltedMass_le (a : Plaq (ZMod s.n) → ℝ) :
    tiltedMass s c a ≤ ENNReal.ofReal (prefactor s a) * torusMeasure s c univ := by
  have hzero : tiltedMass s c 0 = torusMeasure s c univ := by simp [tiltedMass, tilt]
  rw [← hzero, tiltedMass_eq, tiltedMass_eq]
  simp only [prefactor, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul]
  apply mul_le_mul_right
  apply lintegral_mono_ae
  have hr : ∀ᵐ r ∂siteMeasure s c, ∀ x, -c.ρ0 ≤ r x := by
    unfold siteMeasure
    apply Filter.eventually_all.mpr
    intro x
    exact (Measure.tendsto_eval_ae_ae (i := x)).eventually (ae_restrict_mem measurableSet_Ici)
  filter_upwards [hr] with r hr
  exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (closedIntegral_le_zero_shift s c a
    (fun x => by linarith only [hr x]))) _

end GGOS.Work.GD

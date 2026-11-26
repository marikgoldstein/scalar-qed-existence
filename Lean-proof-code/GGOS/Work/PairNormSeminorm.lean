module

public import GGOS.Infra.IsSeminorm
public import GGOS.Work.PairNormBounds

/-!
# The level seminorms and their bounded suprema
-/

public section

noncomputable section

open scoped ENNReal NNReal lp

namespace GGOS.Work.PairNorm

private def plaqMap (sc : Scale) (N : ℕ) : T →ₗ[ℝ] ℓ²(Plaq ℤ, ℝ) where
  toFun σ := ⟨plaqSample (eps sc N) σ,
    (memℓp_zero (finite_sample_supports sc N σ).2).of_exponent_ge zero_le⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def siteMap (sc : Scale) (N : ℕ) : T →ₗ[ℝ] ℓ¹(Site ℤ, ℝ) where
  toFun σ := ⟨siteSample (eps sc N) σ,
    (memℓp_zero (finite_sample_supports sc N σ).1).of_exponent_ge zero_le⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def plaqSeminorm (sc : Scale) (N : ℕ) : Seminorm ℝ T :=
  NNReal.mk (Real.sqrt (eps sc N ^ 3)) (Real.sqrt_nonneg _) •
    (normSeminorm ℝ _).comp (plaqMap sc N)

private def siteSeminorm (sc : Scale) (N : ℕ) : Seminorm ℝ T :=
  NNReal.mk (eps sc N ^ 3) (pow_nonneg (eps_pos sc N).le 3) •
    (normSeminorm ℝ _).comp (siteMap sc N)

private theorem plaqSeminorm_apply (sc : Scale) (N : ℕ) (σ : T) :
    plaqSeminorm sc N σ = rLevel sc N σ := by
  change Real.sqrt (eps sc N ^ 3) * ‖plaqMap sc N σ‖ = Real.sqrt (_ * _)
  rw [Real.sqrt_mul (pow_nonneg (eps_pos sc N).le 3)]
  congr 1
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal), Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rfl

private theorem siteSeminorm_apply (sc : Scale) (N : ℕ) (σ : T) :
    siteSeminorm sc N σ = eLevel sc N σ := by
  change eps sc N ^ 3 * ‖siteMap sc N σ‖ = _ * _
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, div_one, Real.rpow_one, Real.norm_eq_abs]
  rfl

theorem supNorm_nonneg (gd : DensityFn) : 0 ≤ supNorm gd := by
  obtain ⟨C, hC⟩ := gd.bdd
  have hb : BddAbove (Set.range fun r => |gd.toFun r|) := ⟨C, Set.forall_mem_range.mpr hC⟩
  exact (abs_nonneg _).trans (le_ciSup hb (0 : ℝ))

/-- Each sampled norm is the pullback of an ℓᵖ norm. Its supremum over levels is
pointwise by the compact-support bounds. -/
theorem isSeminorm_pairNorm (sc : Scale) (N0 : ℕ) (gd : DensityFn) :
    IsSeminorm (pairNorm sc N0 gd) := by
  let I := {N : ℕ // N0 ≤ N}
  let r : I → Seminorm ℝ T := fun N => plaqSeminorm sc N
  let e : I → Seminorm ℝ T := fun N => siteSeminorm sc N
  have hr : BddAbove (Set.range r) := Seminorm.bddAbove_range_iff.mpr fun σ => by
    simpa only [r, plaqSeminorm_apply] using (level_ranges_bddAbove sc N0 σ).1
  have he : BddAbove (Set.range e) := Seminorm.bddAbove_range_iff.mpr fun σ => by
    simpa only [e, siteSeminorm_apply] using (level_ranges_bddAbove sc N0 σ).2
  let p : Seminorm ℝ T :=
    (⨆ i, r i) + NNReal.mk (supNorm gd) (supNorm_nonneg gd) • ⨆ i, e i
  have hp : pairNorm sc N0 gd = ⇑p := by
    funext σ
    change Rnorm sc N0 σ + supNorm gd * Enorm sc N0 σ =
      (⨆ i, r i) σ + supNorm gd * (⨆ i, e i) σ
    rw [Seminorm.iSup_apply hr, Seminorm.iSup_apply he]
    simp only [r, e, plaqSeminorm_apply, siteSeminorm_apply]
    rfl
  rw [hp]
  exact ⟨apply_nonneg p, map_add_le_add p, map_smul_eq_mul p⟩

end GGOS.Work.PairNorm

end

end

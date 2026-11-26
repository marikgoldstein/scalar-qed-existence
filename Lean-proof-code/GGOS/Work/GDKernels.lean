module

public import GGOS.Work.GDProduct
public import GGOS.Work.GDHopping
public import GGOS.Work.TorusMass

/-!
# The shifted Gaussian partition at fixed radial variables
-/

@[expose] public section

open MeasureTheory Real Set

namespace GGOS.Work.GD

/-- Gaussian parameter corresponding to the physical curvature with variance one. -/
noncomputable def width (c : Coeffs) : ℝ := period c ^ 2 / (2 * π)

theorem width_pos (c : Coeffs) : 0 < width c :=
  div_pos (sq_pos_of_pos (period_pos c)) (mul_pos two_pos pi_pos)

variable (s : Side) (c : Coeffs)

instance : IsFiniteMeasure (bondMeasure s c) := by unfold bondMeasure; infer_instance

/-- Displacement in lattice units after completing the tilted square. -/
noncomputable def displacement (a : Plaq (ZMod s.n) → ℝ) (B : Bond (ZMod s.n) → ℝ)
    (p : Plaq (ZMod s.n)) : ℝ := (dBond B p - a p) / period c

/-- Product of the matter factors depending on the bond variables. -/
noncomputable def hoppingProd (r : Site (ZMod s.n) → ℝ) (B : Bond (ZMod s.n) → ℝ) : ℝ :=
  ∏ b : Bond (ZMod s.n), hop c (r b.1) (r (b.1 + unitVec (ZMod s.n) b.2)) (B b)

theorem hoppingProd_pos (r : Site (ZMod s.n) → ℝ) (B : Bond (ZMod s.n) → ℝ) :
    0 < hoppingProd s c r B := Finset.prod_pos fun _ _ => Real.exp_pos _

theorem hoppingProd_le_one (r : Site (ZMod s.n) → ℝ) (B : Bond (ZMod s.n) → ℝ) :
    hoppingProd s c r B ≤ 1 := by
  apply Finset.prod_le_one (fun _ _ => (Real.exp_pos _).le)
  intro b _
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr (mul_nonneg (mul_nonneg (by norm_num) c.κ_nonneg) (sq_nonneg _))

/-- Bond integral in a single flux sector, after removing the common tilt prefactor. -/
noncomputable def sectorIntegral (a : Plaq (ZMod s.n) → ℝ) (r : Site (ZMod s.n) → ℝ)
    (m : Plaq (ZMod s.n) → ℤ) : ℝ :=
  ∫ B, hoppingProd s c r B * gaussProd (width c) (displacement s c a B) m ∂bondMeasure s c

/-- The sum of the shifted sector integrals over the kernel of the cube boundary. -/
noncomputable def closedIntegral (a : Plaq (ZMod s.n) → ℝ) (r : Site (ZMod s.n) → ℝ) : ℝ :=
  ∑' m : {m : Plaq (ZMod s.n) → ℤ // IsClosedForm m}, sectorIntegral s c a r m.1

theorem ae_bond_box : ∀ᵐ B ∂bondMeasure s c, ∀ b, B b ∈ Ioc (-(π / c.γ)) (π / c.γ) := by
  unfold bondMeasure
  apply Filter.eventually_all.mpr
  intro b
  exact (Measure.tendsto_eval_ae_ae (i := b)).eventually (ae_restrict_mem measurableSet_Ioc)

/-- Compactness of the bond interval gives an absolutely summable flux envelope for each tilt. -/
theorem shifted_majorant (a : Plaq (ZMod s.n) → ℝ) :
    ∃ g : (Plaq (ZMod s.n) → ℤ) → ℝ, Summable g ∧
      ∀ᵐ B ∂bondMeasure s c, ∀ m, gaussProd (width c) (displacement s c a B) m ≤ g m := by
  obtain ⟨g, hg, hb⟩ := gaussProd_majorant (width_pos c)
    (fun p => (4 * (π / c.γ) + |a p|) / period c)
  refine ⟨g, hg, ?_⟩
  filter_upwards [ae_bond_box s c] with B hB
  apply hb
  intro p
  have h (b) : |B b| ≤ π / c.γ := abs_le.mpr ⟨(hB b).1.le, (hB b).2⟩
  have hd : |dBond B p| ≤ 4 * (π / c.γ) := by
    unfold dBond
    calc
      _ ≤ (|B _| + |B _| + |B _|) + |B _| := by grw [abs_sub, abs_sub, abs_add_le]
      _ ≤ π / c.γ + π / c.γ + π / c.γ + π / c.γ := by gcongr <;> apply h
      _ = _ := by ring
  unfold displacement
  rw [abs_div, abs_of_pos (period_pos c)]
  exact div_le_div_of_nonneg_right ((abs_sub _ _).trans (add_le_add hd le_rfl)) (period_pos c).le

theorem integrable_sector (a : Plaq (ZMod s.n) → ℝ) (r : Site (ZMod s.n) → ℝ)
    (m : Plaq (ZMod s.n) → ℤ) :
    Integrable (fun B => hoppingProd s c r B * gaussProd (width c) (displacement s c a B) m)
      (bondMeasure s c) := by
  apply (integrable_const (1 : ℝ)).mono'
  · apply Continuous.aestronglyMeasurable
    unfold hoppingProd hop gaussProd gauss displacement dBond
    fun_prop
  filter_upwards with B
  rw [Real.norm_of_nonneg (mul_pos (hoppingProd_pos ..) (gaussProd_pos ..)).le]
  apply mul_le_one₀ (hoppingProd_le_one ..) (gaussProd_pos ..).le
  apply Finset.prod_le_one (fun _ _ => (gauss_pos _ _).le)
  intro p _
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr pi_pos.le)
    (width_pos c).le) (sq_nonneg _)

theorem sectorIntegral_nonneg (a : Plaq (ZMod s.n) → ℝ) (r : Site (ZMod s.n) → ℝ)
    (m : Plaq (ZMod s.n) → ℤ) : 0 ≤ sectorIntegral s c a r m :=
  integral_nonneg fun _ => (mul_pos (hoppingProd_pos ..) (gaussProd_pos ..)).le

theorem summable_sectorIntegral (a : Plaq (ZMod s.n) → ℝ) (r : Site (ZMod s.n) → ℝ) :
    Summable (sectorIntegral s c a r) := by
  obtain ⟨g, hg, hb⟩ := shifted_majorant s c a
  apply (hg.mul_left ((bondMeasure s c).real univ)).of_norm_bounded
  intro m
  rw [Real.norm_of_nonneg (sectorIntegral_nonneg ..)]
  calc
    _ ≤ ∫ _ : Bond (ZMod s.n) → ℝ, g m ∂bondMeasure s c := by
      apply integral_mono_ae (integrable_sector ..) (integrable_const _)
      filter_upwards [hb] with B hB
      exact (mul_le_of_le_one_left (gaussProd_pos ..).le (hoppingProd_le_one ..)).trans (hB m)
    _ = _ := by simp [smul_eq_mul]

end GGOS.Work.GD

module

public import Mathlib
public import GGOS.Frozen.Defs.TorusState
public import GGOS.Frozen.Defs.SiteFactor
public import GGOS.Work.TorusMassBounds

public section

open MeasureTheory Real

/-!
# The torus measure has finite positive mass
-/

namespace GGOS.Work

theorem torusMeasure_univ_pos (c : Coeffs) (s : Side) : 0 < torusMeasure s c Set.univ := by
  let m₀ : {m : Plaq (ZMod s.n) → ℤ // IsClosedForm m} :=
    ⟨fun _ => 0, by intro x; simp [dPlaq]⟩
  rw [TorusMass.torusMeasure_univ_eq]
  refine lt_of_lt_of_le ?_ (ENNReal.le_tsum m₀)
  have hm : Measurable (fun x : (Site (ZMod s.n) → ℝ) × (Bond (ZMod s.n) → ℝ) =>
      ENNReal.ofReal (weight s c x.1 x.2 m₀.1)) := by
    unfold weight siteFactor hop curv dBond
    fun_prop
  rw [lintegral_pos_iff_support hm]
  let A := Set.univ.pi fun _ : Site (ZMod s.n) => Set.Ioi (-c.ρ0)
  have hA : siteMeasure s c A ≠ 0 := by
    rw [siteMeasure, Measure.pi_pi]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    rw [Measure.restrict_apply measurableSet_Ioi, Set.inter_eq_left.mpr Set.Ioi_subset_Ici_self,
      Real.volume_Ioi]
    exact ENNReal.top_ne_zero
  have hB : 0 < bondMeasure s c Set.univ := by
    rw [TorusMass.bondMeasure_univ]
    exact ENNReal.pow_pos (ENNReal.ofReal_pos.mpr (mul_pos two_pos (div_pos pi_pos c.γ_pos))) _
  let : SFinite (bondMeasure s c) := by unfold bondMeasure; infer_instance
  calc
    0 < ((siteMeasure s c).prod (bondMeasure s c)) (A ×ˢ Set.univ) := by
      rw [Measure.prod_prod]
      exact ENNReal.mul_pos hA hB.ne'
    _ ≤ _ := by
      apply measure_mono
      intro x hx
      apply ENNReal.ofReal_ne_zero_iff.mpr
      unfold weight
      apply mul_pos (mul_pos ?_ ?_) ?_
      · apply Finset.prod_pos
        intro i _
        have hi : -c.ρ0 < x.1 i := hx.1 i (Set.mem_univ i)
        exact mul_pos (mul_pos (by linarith only [hi]) (exp_pos _)) (exp_pos _)
      · exact Finset.prod_pos fun _ _ => exp_pos _
      · exact Finset.prod_pos fun _ _ => exp_pos _

theorem torusMeasure_univ_lt_top (c : Coeffs) (s : Side) : torusMeasure s c Set.univ < ⊤ := by
  let μ := (siteMeasure s c).prod (bondMeasure s c)
  let S (x : (Site (ZMod s.n) → ℝ) × (Bond (ZMod s.n) → ℝ)) := |∏ i, siteFactor c (x.1 i)|
  let D := ∫⁻ x, ENNReal.ofReal (S x) ∂μ
  let : IsFiniteMeasure (bondMeasure s c) := ⟨by rw [TorusMass.bondMeasure_univ]; finiteness⟩
  have hs : Integrable (fun r : Site (ZMod s.n) → ℝ => ∏ i, siteFactor c (r i)) (siteMeasure s c) :=
    Integrable.fintype_prod (f := fun _ => siteFactor c)
      (fun _ => (TorusMass.integrable_siteFactor c).integrableOn)
  have hS : Integrable S μ := (hs.comp_fst (bondMeasure s c)).norm
  obtain ⟨G, hsum, hbound⟩ := TorusMass.exists_summable_weight_bound s c
  have hB : ∀ᵐ B ∂bondMeasure s c, ∀ b, B b ∈ Set.Ioc (-(π / c.γ)) (π / c.γ) := by
    unfold bondMeasure
    apply Filter.eventually_all.mpr
    intro b
    exact (Measure.tendsto_eval_ae_ae (i := b)).eventually (ae_restrict_mem measurableSet_Ioc)
  rw [TorusMass.torusMeasure_univ_eq]
  calc
    _ ≤ ∑' m : {m : Plaq (ZMod s.n) → ℤ // IsClosedForm m}, D * ENNReal.ofReal (G m.1) := by
      apply ENNReal.tsum_le_tsum
      intro m
      dsimp only [D]
      rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono_ae
      filter_upwards [Measure.quasiMeasurePreserving_snd.ae hB] with x hx
      exact (ENNReal.ofReal_le_ofReal (hbound x.1 x.2 hx m.1)).trans_eq
        (ENNReal.ofReal_mul (abs_nonneg _))
    _ ≤ ∑' m, D * ENNReal.ofReal (G m) :=
      ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
    _ = D * ∑' m, ENNReal.ofReal (G m) := ENNReal.tsum_mul_left
    _ < ⊤ := ENNReal.mul_lt_top hS.lintegral_lt_top hsum.tsum_ofReal_lt_top

theorem isProbabilityMeasure_torusState (c : Coeffs) (s : Side) :
    IsProbabilityMeasure (torusState s c) := by
  constructor
  exact ENNReal.inv_mul_cancel (torusMeasure_univ_pos c s).ne' (torusMeasure_univ_lt_top c s).ne

end GGOS.Work

end

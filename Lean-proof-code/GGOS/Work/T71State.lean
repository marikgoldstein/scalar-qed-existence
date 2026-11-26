module

public import Mathlib
public import GGOS.Frozen.Defs.IsLimitPoint
public import GGOS.Frozen.Defs.LatticeInvariant
public import GGOS.Frozen.Defs.Iota
public import GGOS.Frozen.Defs.TauA
public import GGOS.Frozen.Defs.Phi
public import GGOS.Frozen.Defs.PairNorm
public import GGOS.Infra.IsState
public import GGOS.Work.LimitState

public section

open MeasureTheory Filter Topology

/-!
# Limit points of the torus states are states ([GG-OS], theorem "limit points, with every symmetry", part (b))
-/

namespace GGOS.Work

private theorem integrable_of_isBBL {μ : Measure (Cfg ℤ)} [IsProbabilityMeasure μ]
    {F : Cfg ℤ → ℂ} (hF : IsBBL F) : Integrable F μ := by
  obtain ⟨C, hC⟩ := hF.bounded
  exact Integrable.mono' (integrable_const C) hF.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

/-- [GG-OS], theorem "limit points, with every symmetry", (b), state part: a limit point of the torus states is a state on the
bounded Borel local functions of `Ω_N`. -/
theorem isState_of_isLimitPoint (c : Coeffs) (ω : (Cfg ℤ → ℂ) → ℂ) (h : IsLimitPoint c ω) :
    IsState c.ρ0 ω := by
  obtain ⟨_, μ, _, hprob, hsupp, _, hω⟩ := h
  haveI : IsProbabilityMeasure μ := hprob
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F G hF hG
    rw [hω (F + G) (Limit.bbl_add hF hG), hω F hF, hω G hG]
    exact integral_add (integrable_of_isBBL hF) (integrable_of_isBBL hG)
  · intro z F hF
    rw [hω (z • F) (Limit.bbl_smul z hF), hω F hF]
    change (∫ x, z * F x ∂μ) = z * ∫ x, F x ∂μ
    rw [integral_const_mul]
  · rw [hω (fun _ => 1) (Limit.bbl_const 1)]
    have h1 : (∫ _ : Cfg ℤ, (1 : ℝ) ∂μ) = 1 :=
      integral_eq_const (Filter.Eventually.of_forall fun _ => rfl)
    calc (∫ _ : Cfg ℤ, (1 : ℂ) ∂μ)
        = ∫ _ : Cfg ℤ, ((1 : ℝ) : ℂ) ∂μ := by simp only [Complex.ofReal_one]
      _ = ((∫ _ : Cfg ℤ, (1 : ℝ) ∂μ : ℝ) : ℂ) := by rw [integral_complex_ofReal]
      _ = 1 := by rw [h1, Complex.ofReal_one]
  · intro F hF hpos
    have hmem : ∀ᵐ x ∂μ, x ∈ OmegaN c.ρ0 := mem_ae_iff.mpr hsupp
    have hae : F =ᵐ[μ] fun x => ((‖F x‖ : ℝ) : ℂ) :=
      hmem.mono fun x hx => by
        obtain ⟨r, hr, hFx⟩ := hpos x hx
        show F x = ((‖F x‖ : ℝ) : ℂ)
        rw [hFx, Complex.norm_real, Real.norm_of_nonneg hr]
    refine ⟨∫ x, ‖F x‖ ∂μ, integral_nonneg fun x => norm_nonneg (F x), ?_⟩
    rw [hω F hF, integral_congr_ae hae, integral_complex_ofReal]

end GGOS.Work

end

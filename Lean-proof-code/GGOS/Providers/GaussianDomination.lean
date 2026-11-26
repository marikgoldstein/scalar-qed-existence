module

public import Mathlib
public import GGOS.Frozen.Defs.TorusState
public import GGOS.Infra.Cells
public import GGOS.Infra.Coeffs
public import GGOS.Infra.Side
public import GGOS.Work.GDPartition
public import GGOS.Work.TorusMass

/-!
# Provider for `GGOS.gaussian_domination`

The proof of the theorem in `GGOS/Frozen/GaussianDomination.lean`,
as `GGOS.Providers.gaussian_domination`,
stated with exactly the theorem's type; the theorem is `by exact` of it.
-/

public section

open MeasureTheory GGOS.Work GGOS.Work.GD

namespace GGOS.Providers

/-- Gaussian domination of the Villain curvature, including integrability of the tilt. -/
theorem gaussian_domination :
    ∀ (c : Coeffs) (s : Side) (a : Plaq (ZMod s.n) → ℝ),
    IsProbabilityMeasure (torusState s c) ∧
      Integrable (fun ω : Cfg (ZMod s.n) => Real.exp (∑ p, a p * ω.1 p)) (torusState s c) ∧
      ∫ ω, Real.exp (∑ p, a p * ω.1 p) ∂(torusState s c) ≤ Real.exp (1 / 2 * ∑ p, a p ^ 2) := by
  intro c s a
  have hpos (ω : Cfg (ZMod s.n)) : 0 ≤ tilt s a ω := (Real.exp_pos _).le
  have hbound : (∫⁻ ω, ENNReal.ofReal (tilt s a ω) ∂torusState s c) ≤
      ENNReal.ofReal (prefactor s a) := by
    rw [torusState, lintegral_smul_measure, smul_eq_mul]
    calc
      _ ≤ (torusMeasure s c Set.univ)⁻¹ *
          (ENNReal.ofReal (prefactor s a) * torusMeasure s c Set.univ) :=
        mul_le_mul_right (tiltedMass_le s c a) _
      _ = _ := by
        rw [mul_left_comm, ENNReal.inv_mul_cancel (torusMeasure_univ_pos c s).ne'
          (torusMeasure_univ_lt_top c s).ne, mul_one]
  have hi : Integrable (tilt s a) (torusState s c) := by
    refine ⟨by unfold tilt; fun_prop, ?_⟩
    change (∫⁻ ω, ‖tilt s a ω‖ₑ ∂torusState s c) < ⊤
    simpa only [Real.enorm_eq_ofReal (hpos _)] using
      hbound.trans_lt ENNReal.ofReal_lt_top
  refine ⟨isProbabilityMeasure_torusState c s, hi, ?_⟩
  change ∫ ω, tilt s a ω ∂torusState s c ≤ prefactor s a
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hpos) hi.1]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal (Real.exp_pos _).le)

end GGOS.Providers

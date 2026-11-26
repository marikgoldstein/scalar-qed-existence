module

public import Mathlib
public import GGOS.Frozen.Defs.TorusState
public import GGOS.Infra.Cells
public import GGOS.Infra.Coeffs
public import GGOS.Infra.Side
public import GGOS.Providers.GaussianDomination

/-!
# [GG-OS] Theorem 3.1, first sentence
-/

public section

open MeasureTheory

namespace GGOS

/-- [GG-OS] Theorem 3.1, first sentence (Gaussian domination, identity covariance), for the
coefficients of Remark 2.1; with `Z(a) ∈ (0, ∞)` from its proof. -/
theorem gaussian_domination :
    ∀ (c : Coeffs) (s : Side) (a : Plaq (ZMod s.n) → ℝ),
    IsProbabilityMeasure (torusState s c) ∧
      Integrable (fun ω : Cfg (ZMod s.n) => Real.exp (∑ p, a p * ω.1 p)) (torusState s c) ∧
      ∫ ω, Real.exp (∑ p, a p * ω.1 p) ∂(torusState s c) ≤ Real.exp (1 / 2 * ∑ p, a p ^ 2) :=
  by exact GGOS.Providers.gaussian_domination

end GGOS

end

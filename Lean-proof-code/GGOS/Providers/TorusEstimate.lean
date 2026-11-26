module

public import Mathlib
public import GGOS.Frozen.Defs.Embeds
public import GGOS.Frozen.Defs.PairNorm
public import GGOS.Frozen.Defs.Per
public import GGOS.Frozen.Defs.Phi
public import GGOS.Frozen.Defs.TorusState
public import GGOS.Infra.Cells
public import GGOS.Infra.Coeffs
public import GGOS.Infra.DensityFn
public import GGOS.Infra.Scale
public import GGOS.Infra.Side
public import GGOS.Infra.T

public import GGOS.Frozen.GaussianMoments
public import GGOS.Work.TorusEstimateCore

/-!
# Provider for `GGOS.torus_estimate`

The proof of the theorem in `GGOS/Frozen/TorusEstimate.lean`,
as `GGOS.Providers.torus_estimate`,
stated with exactly the theorem's type; the theorem is `by exact` of it.
-/

public section

open MeasureTheory

namespace GGOS.Providers

/-- [GG-OS] Proposition 4.2, torus inequality: `GGOS.Work.torus_estimate_of_second_moment`
with the second-moment conjunct of `GGOS.gaussian_moments`. -/
theorem torus_estimate :
    ∀ (c : Coeffs) (sc : Scale) (N0 : ℕ) (gd : DensityFn) (σ : T) (N : ℕ) (hN : N0 ≤ N) (s : Side)
      (hemb : Embeds sc N s σ),
    Integrable (fun ω : Cfg (ZMod s.n) => Phi sc N gd σ (per s.n ω) ^ 2) (torusState s c) ∧
      Real.sqrt (∫ ω, Phi sc N gd σ (per s.n ω) ^ 2 ∂(torusState s c)) ≤ pairNorm sc N0 gd σ := by
  intro c sc N0 gd σ N hN s hemb
  exact GGOS.Work.torus_estimate_of_second_moment c sc N0 gd σ N hN s hemb
    (fun a => (GGOS.gaussian_moments c s a).2.1)

end GGOS.Providers

end

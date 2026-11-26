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
public import GGOS.Providers.TorusEstimate

/-!
# [GG-OS] Proposition 4.2, first inequality of (4.1)
-/

public section

open MeasureTheory

namespace GGOS

/-- [GG-OS] Proposition 4.2, first inequality of (4.1): on every torus into which the support
of `σ` embeds, `(⟨Φ_N(σ)²⟩)^{1/2} ≤ ‖σ‖`, for the coefficients of Remark 2.1. -/
theorem torus_estimate :
    ∀ (c : Coeffs) (sc : Scale) (N0 : ℕ) (gd : DensityFn) (σ : T) (N : ℕ) (hN : N0 ≤ N) (s : Side)
      (hemb : Embeds sc N s σ),
    Integrable (fun ω : Cfg (ZMod s.n) => Phi sc N gd σ (per s.n ω) ^ 2) (torusState s c) ∧
      Real.sqrt (∫ ω, Phi sc N gd σ (per s.n ω) ^ 2 ∂(torusState s c)) ≤ pairNorm sc N0 gd σ :=
  by exact GGOS.Providers.torus_estimate

end GGOS

end

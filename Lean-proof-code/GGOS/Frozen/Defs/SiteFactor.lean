module

public import Mathlib
public import GGOS.Infra.Coeffs

/-!
# `GGOS.siteFactor`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The site factor `g_ct(ρ̃) = ρ e^{-λ_0 (ρ² - ρ_{0,0}²)²} e^{-δm_B ρ²/2}`, `ρ = ρ_{0,0} + ρ̃`. -/
def siteFactor (c : Coeffs) (r : ℝ) : ℝ :=
  (c.ρ0 + r) * Real.exp (-(c.lam * ((c.ρ0 + r) ^ 2 - c.ρ0 ^ 2) ^ 2))
    * Real.exp (-(1 / 2 * c.δm * (c.ρ0 + r) ^ 2))

end GGOS

end

end

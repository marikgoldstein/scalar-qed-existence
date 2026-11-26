module

public import Mathlib
public import GGOS.Infra.Coeffs

/-!
# `GGOS.hop`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The hopping factor `h(r, r', ϑ) = exp(-κ_N |e^{iγϑ}(ρ_{0,0} + r') - (ρ_{0,0} + r)|² / 2)`. -/
def hop (c : Coeffs) (r r' ϑ : ℝ) : ℝ :=
  Real.exp (-(1 / 2 * c.κ *
    ‖Complex.exp (Complex.I * ((c.γ * ϑ : ℝ) : ℂ)) * ((c.ρ0 + r' : ℝ) : ℂ)
        - ((c.ρ0 + r : ℝ) : ℂ)‖ ^ 2))

end GGOS

end

end

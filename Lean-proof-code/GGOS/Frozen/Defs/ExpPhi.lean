module

public import Mathlib
public import GGOS.Frozen.Defs.Phi
public import GGOS.Infra.Cells
public import GGOS.Infra.DensityFn
public import GGOS.Infra.Scale
public import GGOS.Infra.T

/-!
# `GGOS.expPhi`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- `e^{iΦ_N(σ)}`. -/
def expPhi (sc : Scale) (N : ℕ) (gd : DensityFn) (σ : T) : Cfg ℤ → ℂ :=
  fun ω => Complex.exp (Complex.I * ((Phi sc N gd σ ω : ℝ) : ℂ))

end GGOS

end

end

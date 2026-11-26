module

public import Mathlib
public import GGOS.Frozen.Defs.ExpPhi
public import GGOS.Infra.Alg
public import GGOS.Infra.Cells
public import GGOS.Infra.DensityFn
public import GGOS.Infra.Scale

/-!
# `GGOS.iota`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The realisation `ι_N(e_σ) = e^{iΦ_N(σ)}`, extended linearly to `𝒜`. -/
def iota (sc : Scale) (N : ℕ) (gd : DensityFn) (a : Alg) : Cfg ℤ → ℂ :=
  a.coeff.sum fun σ z => z • expPhi sc N gd σ

end GGOS

end

end

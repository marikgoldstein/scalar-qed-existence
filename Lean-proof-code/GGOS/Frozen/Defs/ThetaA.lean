module

public import Mathlib
public import GGOS.Frozen.Defs.Theta
public import GGOS.Infra.Alg

/-!
# `GGOS.ThetaA`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- `Θ e_σ = e_{-θσ}`, `Θ` antilinear. -/
def ThetaA (a : Alg) : Alg :=
  AddMonoidAlgebra.mapDomain (fun σ => -theta σ)
    (AddMonoidAlgebra.ofCoeff (a.coeff.mapRange (starRingEnd ℂ) (map_zero _)))

end GGOS

end

end

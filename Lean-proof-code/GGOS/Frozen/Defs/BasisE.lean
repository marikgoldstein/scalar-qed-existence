module

public import Mathlib
public import GGOS.Infra.Alg
public import GGOS.Infra.T

/-!
# `GGOS.basisE`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The basis element `e_σ`. -/
def basisE (σ : T) : Alg := AddMonoidAlgebra.single σ 1

end GGOS

end

end

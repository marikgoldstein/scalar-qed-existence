module

public import Mathlib
public import GGOS.Infra.Ambient
public import GGOS.Infra.T

/-!
# `GGOS.SupportedPos`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- `σ` is supported in the open half space `{x_3 > 0}`. -/
def SupportedPos (σ : T) : Prop :=
  (∀ μ ν, tsupport (σ.1.1 μ ν) ⊆ {ξ : E3 | 0 < ξ 2}) ∧ tsupport σ.1.2 ⊆ {ξ : E3 | 0 < ξ 2}

end GGOS

end

end

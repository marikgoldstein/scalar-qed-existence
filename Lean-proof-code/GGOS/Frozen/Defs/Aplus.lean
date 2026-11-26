module

public import Mathlib
public import GGOS.Frozen.Defs.BasisE
public import GGOS.Frozen.Defs.SupportedPos
public import GGOS.Infra.Alg

/-!
# `GGOS.Aplus`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- `𝒜_+`: the span of the `e_σ` with `σ` supported in `{x_3 > 0}`. -/
def Aplus : Submodule ℂ Alg := Submodule.span ℂ {a | ∃ σ, SupportedPos σ ∧ a = basisE σ}

end GGOS

end

end

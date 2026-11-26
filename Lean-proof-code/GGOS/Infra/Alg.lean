module

public import Mathlib
public import GGOS.Infra.T

/-!
# `GGOS.Alg`

Infrastructure of the [GG-OS] definitions (structures, abbreviations and their lemmas).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The algebra `𝒜 = ℂ[𝒯]`: the group algebra with basis `e_σ`, `e_σ e_σ' = e_{σ+σ'}`. -/
abbrev Alg := AddMonoidAlgebra ℂ T

end GGOS

end

end

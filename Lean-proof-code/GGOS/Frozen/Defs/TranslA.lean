module

public import Mathlib
public import GGOS.Frozen.Defs.Transl
public import GGOS.Infra.Alg
public import GGOS.Infra.Ambient

/-!
# `GGOS.translA`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- `τ_v e_σ = e_{τ_v σ}` for a translation by `v ∈ ℝ³`. -/
def translA (v : E3) (a : Alg) : Alg := AddMonoidAlgebra.mapDomain (transl v) a

end GGOS

end

end

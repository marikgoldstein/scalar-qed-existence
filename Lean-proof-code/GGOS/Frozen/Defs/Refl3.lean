module

public import Mathlib
public import GGOS.Frozen.Defs.Sgn3
public import GGOS.Infra.Ambient

/-!
# `GGOS.refl3`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The time reflection `x ↦ (x_1, x_2, -x_3)` of `ℝ³`. -/
def refl3 (ξ : E3) : E3 := fun i => sgn3 i * ξ i

end GGOS

end

end

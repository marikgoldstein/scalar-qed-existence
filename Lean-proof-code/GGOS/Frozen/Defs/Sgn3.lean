module

public import Mathlib

/-!
# `GGOS.sgn3`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The signs of the time reflection. -/
def sgn3 : Fin 3 → ℝ := ![1, 1, -1]

end GGOS

end

end

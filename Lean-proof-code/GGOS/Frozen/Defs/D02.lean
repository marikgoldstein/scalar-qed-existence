module

public import Mathlib
public import GGOS.Infra.Dir2

/-!
# `GGOS.d02`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The orientation `(0,2)`. -/
def d02 : Dir2 := ⟨(0, 2), by decide⟩

end GGOS

end

end

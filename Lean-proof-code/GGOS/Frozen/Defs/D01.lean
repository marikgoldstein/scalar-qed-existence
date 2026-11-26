module

public import Mathlib
public import GGOS.Infra.Dir2

/-!
# `GGOS.d01`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The orientation `(0,1)`. -/
def d01 : Dir2 := ⟨(0, 1), by decide⟩

end GGOS

end

end

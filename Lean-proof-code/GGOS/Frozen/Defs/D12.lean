module

public import Mathlib
public import GGOS.Infra.Dir2

/-!
# `GGOS.d12`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The orientation `(1,2)`. -/
def d12 : Dir2 := ⟨(1, 2), by decide⟩

end GGOS

end

end

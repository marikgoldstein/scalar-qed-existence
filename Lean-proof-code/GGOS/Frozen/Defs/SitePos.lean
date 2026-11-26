module

public import Mathlib
public import GGOS.Infra.Ambient
public import GGOS.Infra.Site

/-!
# `GGOS.sitePos`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The position of a site of the lattice of spacing `ε`. -/
def sitePos (ε : ℝ) (x : Site ℤ) : E3 := fun i => ε * (x i : ℝ)

end GGOS

end

end

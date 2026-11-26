module

public import Mathlib
public import GGOS.Infra.Ambient
public import GGOS.Infra.Cells

/-!
# `GGOS.plaqCentre`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The centre `x_p` of a plaquette of the lattice of spacing `ε`. -/
def plaqCentre (ε : ℝ) (p : Plaq ℤ) : E3 :=
  fun i => ε * ((p.1 i : ℝ) + if i = p.2.1.1 ∨ i = p.2.1.2 then 1 / 2 else 0)

end GGOS

end

end

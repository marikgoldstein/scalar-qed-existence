module

public import Mathlib
public import GGOS.Frozen.Defs.D01
public import GGOS.Frozen.Defs.D02
public import GGOS.Frozen.Defs.D12
public import GGOS.Frozen.Defs.UnitVec
public import GGOS.Infra.Cells
public import GGOS.Infra.Site

/-!
# `GGOS.dPlaq`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

section Lattice

variable (R : Type*) [CommRing R]
variable {R}

/-- `(dm)_c` for the cube with base site `x`, with the signs of the boundary. -/
def dPlaq (m : Plaq R → ℤ) (x : Site R) : ℤ :=
  (m (x + unitVec R 0, d12) - m (x, d12)) - (m (x + unitVec R 1, d02) - m (x, d02))
    + (m (x + unitVec R 2, d01) - m (x, d01))

end Lattice

end GGOS

end

end

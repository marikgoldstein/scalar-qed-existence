module

public import Mathlib
public import GGOS.Frozen.Defs.UnitVec
public import GGOS.Infra.Cells

/-!
# `GGOS.dBond`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

section Lattice

variable (R : Type*) [CommRing R]
variable {R}

/-- `(dB)_p`, with the signs of the boundary. -/
def dBond (B : Bond R → ℝ) (p : Plaq R) : ℝ :=
  B (p.1, p.2.1.1) + B (p.1 + unitVec R p.2.1.1, p.2.1.2)
    - B (p.1 + unitVec R p.2.1.2, p.2.1.1) - B (p.1, p.2.1.2)

end Lattice

end GGOS

end

end

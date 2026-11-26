module

public import Mathlib
public import GGOS.Infra.Site

/-!
# `GGOS.unitVec`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

section Lattice

variable (R : Type*) [CommRing R]

/-- The unit vector of the direction `μ`. -/
def unitVec (μ : Fin 3) : Site R := Pi.single μ 1

end Lattice

end GGOS

end

end

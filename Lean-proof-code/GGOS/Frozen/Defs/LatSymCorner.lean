module

public import Mathlib
public import GGOS.Frozen.Defs.UnitVec
public import GGOS.Infra.LatSym
public import GGOS.Infra.Site

/-!
# `GGOS.LatSym.corner`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

section Symmetry

variable {R : Type*} [CommRing R]

/-- The shift of the base site of an image plaquette when the direction `μ` is reversed. -/
def LatSym.corner (g : LatSym R) (μ : Fin 3) : Site R :=
  if g.sgn μ = 1 then 0 else -unitVec R (g.perm μ)

end Symmetry

end GGOS

end

end

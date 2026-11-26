module

public import Mathlib
public import GGOS.Infra.LatSym
public import GGOS.Infra.Site

/-!
# `GGOS.LatSym.act`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

section Symmetry

variable {R : Type*} [CommRing R]

/-- The action on sites: `(g x)_{perm μ} = sgn μ * x_μ + shift_{perm μ}`. -/
def LatSym.act (g : LatSym R) (x : Site R) : Site R :=
  fun α => (((g.sgn (g.perm.symm α) : ℤˣ) : ℤ) : R) * x (g.perm.symm α) + g.shift α

end Symmetry

end GGOS

end

end

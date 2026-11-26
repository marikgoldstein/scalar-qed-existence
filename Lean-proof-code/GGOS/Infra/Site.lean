module

public import Mathlib

/-!
# `GGOS.Site`

Infrastructure of the [GG-OS] definitions (structures, abbreviations and their lemmas).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

section Lattice

variable (R : Type*) [CommRing R]

/-- Sites (`R = ℤ`: the infinite lattice; `R = ZMod n`: the torus with `n` sites per side). -/
abbrev Site := Fin 3 → R

end Lattice

end GGOS

end

end

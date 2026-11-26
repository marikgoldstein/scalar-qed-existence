module

public import Mathlib
public import GGOS.Frozen.Defs.DPlaq
public import GGOS.Infra.Cells

/-!
# `GGOS.IsClosedForm`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

section Lattice

variable (R : Type*) [CommRing R]
variable {R}

/-- `dm = 0` on every cube; the Villain variable is `v_p = (2π/γ) m_p`. -/
def IsClosedForm (m : Plaq R → ℤ) : Prop := ∀ x, dPlaq m x = 0

end Lattice

end GGOS

end

end

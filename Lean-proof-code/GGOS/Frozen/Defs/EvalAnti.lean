module

public import Mathlib
public import GGOS.Infra.Cells
public import GGOS.Infra.Site

/-!
# `GGOS.evalAnti`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

section Symmetry

variable {R : Type*} [CommRing R]

/-- A plaquette field extended antisymmetrically to all orientations `(α, β)`. -/
def evalAnti (F : Plaq R → ℝ) (y : Site R) (α β : Fin 3) : ℝ :=
  if h : α < β then F (y, ⟨(α, β), h⟩)
  else if h' : β < α then -F (y, ⟨(β, α), h'⟩)
  else 0

end Symmetry

end GGOS

end

end

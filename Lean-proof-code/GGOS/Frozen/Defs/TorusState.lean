module

public import Mathlib
public import GGOS.Frozen.Defs.TorusMeasure
public import GGOS.Infra.Cells
public import GGOS.Infra.Coeffs
public import GGOS.Infra.Side

/-!
# `GGOS.torusState`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

section Torus

variable (s : Side)

/-- The fine torus state `⟨·⟩^fine_L`: the normalised torus measure. -/
def torusState (c : Coeffs) : Measure (Cfg (ZMod s.n)) :=
  (torusMeasure s c Set.univ)⁻¹ • torusMeasure s c

end Torus

end GGOS

end

end

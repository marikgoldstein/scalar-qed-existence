module

public import Mathlib
public import GGOS.Infra.Coeffs
public import GGOS.Infra.Side
public import GGOS.Infra.Site

/-!
# `GGOS.siteMeasure`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

section Torus

variable (s : Side)

/-- Lebesgue measure on the site variables `ρ̃_x ∈ [-ρ_{0,0}, ∞)`. -/
def siteMeasure (c : Coeffs) : Measure (Site (ZMod s.n) → ℝ) :=
  Measure.pi fun _ => (volume : Measure ℝ).restrict (Set.Ici (-c.ρ0))

end Torus

end GGOS

end

end

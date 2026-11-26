module

public import Mathlib
public import GGOS.Infra.Cells
public import GGOS.Infra.Coeffs
public import GGOS.Infra.Side

/-!
# `GGOS.bondMeasure`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

section Torus

variable (s : Side)

/-- Lebesgue measure on the bond variables `B_b ∈ (-π/γ, π/γ]`. -/
def bondMeasure (c : Coeffs) : Measure (Bond (ZMod s.n) → ℝ) :=
  Measure.pi fun _ =>
    (volume : Measure ℝ).restrict (Set.Ioc (-(Real.pi / c.γ)) (Real.pi / c.γ))

end Torus

end GGOS

end

end

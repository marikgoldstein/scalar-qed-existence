module

public import Mathlib
public import GGOS.Infra.Cells

/-!
# `GGOS.OmegaN`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The configuration space `Ω_N = ℝ^{plaquettes} × [-ρ_{0,0}, ∞)^{sites}`, as a subset. -/
def OmegaN (ρ0 : ℝ) : Set (Cfg ℤ) := {ω | ∀ x, -ρ0 ≤ ω.2 x}

end GGOS

end

end

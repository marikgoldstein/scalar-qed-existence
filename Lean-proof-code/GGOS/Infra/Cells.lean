module

public import Mathlib
public import GGOS.Infra.Dir2
public import GGOS.Infra.Site

/-!
# `GGOS.Bond`, `GGOS.Plaq`, `GGOS.Cfg`

Infrastructure of the [GG-OS] definitions (structures, abbreviations and their lemmas).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

section Lattice

variable (R : Type*) [CommRing R]

/-- Bonds `(x, μ)`, from `x` to `x + e_μ`. -/
abbrev Bond := Site R × Fin 3

/-- Plaquettes `(x, (μ, ν))`, `μ < ν`, with corners `x`, `x + e_μ`, `x + e_ν`, `x + e_μ + e_ν`. -/
abbrev Plaq := Site R × Dir2

/-- Configurations of the gauge-invariant variables: the curvature `𝔣_p` and the density `ρ̃_x`. -/
abbrev Cfg := (Plaq R → ℝ) × (Site R → ℝ)

end Lattice

end GGOS

end

end

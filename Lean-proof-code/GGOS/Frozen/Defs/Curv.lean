module

public import Mathlib
public import GGOS.Frozen.Defs.DBond
public import GGOS.Infra.Cells
public import GGOS.Infra.Coeffs

/-!
# `GGOS.curv`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

section Lattice

variable (R : Type*) [CommRing R]
variable {R}

/-- The Villain curvature `𝔣_p = (dB)_p + (2π/γ) m_p`. -/
def curv (c : Coeffs) (B : Bond R → ℝ) (m : Plaq R → ℤ) (p : Plaq R) : ℝ :=
  dBond B p + 2 * Real.pi / c.γ * (m p : ℝ)

end Lattice

end GGOS

end

end

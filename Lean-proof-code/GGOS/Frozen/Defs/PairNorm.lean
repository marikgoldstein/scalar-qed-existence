module

public import Mathlib
public import GGOS.Frozen.Defs.Enorm
public import GGOS.Frozen.Defs.Rnorm
public import GGOS.Frozen.Defs.SupNorm
public import GGOS.Infra.DensityFn
public import GGOS.Infra.Scale
public import GGOS.Infra.T

/-!
# `GGOS.pairNorm`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- `‖σ‖ = R(f) + ‖g_d‖_∞ E(h)`. -/
def pairNorm (sc : Scale) (N0 : ℕ) (gd : DensityFn) (σ : T) : ℝ :=
  Rnorm sc N0 σ + supNorm gd * Enorm sc N0 σ

end GGOS

end

end

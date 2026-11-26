module

public import Mathlib
public import GGOS.Infra.DensityFn

/-!
# `GGOS.supNorm`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- `‖g_d‖_∞`. -/
def supNorm (gd : DensityFn) : ℝ := ⨆ r : ℝ, |gd.toFun r|

end GGOS

end

end

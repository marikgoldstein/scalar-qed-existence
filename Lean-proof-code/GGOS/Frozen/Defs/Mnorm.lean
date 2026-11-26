module

public import Mathlib
public import GGOS.Infra.Alg

/-!
# `GGOS.Mnorm`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- `M(∑_j c_j e_{σ_j}) = ∑_j |c_j|`. -/
def Mnorm (a : Alg) : ℝ := a.coeff.sum fun _ z => ‖z‖

end GGOS

end

end

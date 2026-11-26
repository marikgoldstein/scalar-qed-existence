module

public import Mathlib
public import GGOS.Infra.Scale

/-!
# `GGOS.eps`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The spacing `ε_N = a_0 5^{-N}`. -/
def eps (sc : Scale) (N : ℕ) : ℝ := sc.a0 / 5 ^ N

end GGOS

end

end

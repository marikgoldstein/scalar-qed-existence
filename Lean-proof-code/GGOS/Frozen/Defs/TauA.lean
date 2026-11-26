module

public import Mathlib
public import GGOS.Frozen.Defs.TranslA
public import GGOS.Infra.Alg

/-!
# `GGOS.tauA`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The time translation `τ_t`: the translation by `t e_3`. -/
def tauA (t : ℝ) (a : Alg) : Alg := translA (Pi.single 2 t) a

end GGOS

end

end

module

public import Mathlib

/-!
# `GGOS.Dir2`

Infrastructure of the [GG-OS] definitions (structures, abbreviations and their lemmas).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The orientations `μ < ν` of the plaquettes. -/
abbrev Dir2 := {q : Fin 3 × Fin 3 // q.1 < q.2}

end GGOS

end

end

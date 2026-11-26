module

public import Mathlib

/-!
# `GGOS.Scale`

Infrastructure of the [GG-OS] definitions (structures, abbreviations and their lemmas).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The fixed length `a_0 > 0` of [GG-OS] Section 2. -/
structure Scale where
  /-- the length `a_0` -/
  a0 : ℝ
  a0_pos : 0 < a0

end GGOS

end

end

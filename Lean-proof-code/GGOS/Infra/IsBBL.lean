module

public import Mathlib
public import GGOS.Frozen.Defs.IsLocal
public import GGOS.Infra.Cells

/-!
# `GGOS.IsBBL`

Infrastructure of the [GG-OS] definitions (structures, abbreviations and their lemmas).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The bounded Borel local functions. -/
structure IsBBL (F : Cfg ℤ → ℂ) : Prop where
  measurable : Measurable F
  bounded : ∃ C : ℝ, ∀ ω, ‖F ω‖ ≤ C
  isLocal : IsLocal F

end GGOS

end

end

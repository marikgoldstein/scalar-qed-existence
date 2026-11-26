module

public import Mathlib

/-!
# `GGOS.E3`, `GGOS.smoothTop`, `GGOS.Ambient`

Infrastructure of the [GG-OS] definitions (structures, abbreviations and their lemmas).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The space `ℝ³`. -/
abbrev E3 := Fin 3 → ℝ

/-- The smoothness exponent `∞`. -/
abbrev smoothTop : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Pairs (matrix of functions, function) before any condition. -/
abbrev Ambient := (Fin 3 → Fin 3 → E3 → ℝ) × (E3 → ℝ)

end GGOS

end

end

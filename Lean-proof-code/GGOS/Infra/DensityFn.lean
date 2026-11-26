module

public import Mathlib

/-!
# `GGOS.DensityFn`

Infrastructure of the [GG-OS] definitions (structures, abbreviations and their lemmas).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- A bounded real Borel function on `ℝ`: the density function `g_d` of the pinned scheme. -/
structure DensityFn where
  /-- the function -/
  toFun : ℝ → ℝ
  measurable : Measurable toFun
  bdd : ∃ C : ℝ, ∀ r, |toFun r| ≤ C

end GGOS

end

end

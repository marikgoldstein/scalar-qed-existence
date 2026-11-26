module

public import Mathlib
public import GGOS.Infra.T

/-!
# `GGOS.IsSeminorm`

Infrastructure of the [GG-OS] definitions (structures, abbreviations and their lemmas).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- A seminorm on `𝒯`, as a function. -/
structure IsSeminorm (p : T → ℝ) : Prop where
  nonneg : ∀ σ, 0 ≤ p σ
  add_le : ∀ σ σ', p (σ + σ') ≤ p σ + p σ'
  smul : ∀ (c : ℝ) (σ : T), p (c • σ) = |c| * p σ

end GGOS

end

end

module

public import Mathlib
public import GGOS.Frozen.Defs.OmegaN
public import GGOS.Infra.Cells
public import GGOS.Infra.IsBBL

/-!
# `GGOS.IsState`

Infrastructure of the [GG-OS] definitions (structures, abbreviations and their lemmas).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- A state on the bounded Borel local functions of `Ω_N`: linear, positive, `ω(1) = 1`. -/
structure IsState (ρ0 : ℝ) (ω : (Cfg ℤ → ℂ) → ℂ) : Prop where
  map_add : ∀ F G, IsBBL F → IsBBL G → ω (F + G) = ω F + ω G
  map_smul : ∀ (z : ℂ) F, IsBBL F → ω (z • F) = z * ω F
  map_one : ω (fun _ => 1) = 1
  nonneg : ∀ F, IsBBL F → (∀ x ∈ OmegaN ρ0, ∃ r : ℝ, 0 ≤ r ∧ F x = (r : ℂ)) →
    ∃ r : ℝ, 0 ≤ r ∧ ω F = (r : ℂ)

end GGOS

end

end

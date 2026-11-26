module

public import Mathlib
public import GGOS.Frozen.Defs.ConvTest
public import GGOS.Infra.T

/-!
# `GGOS.Admissible`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- A seminorm is admissible if `σ_n → σ` in `C_c^∞` implies `‖σ_n - σ‖' → 0`. -/
def Admissible (p : T → ℝ) : Prop :=
  ∀ (σs : ℕ → T) (σ : T), ConvTest σs σ → Tendsto (fun n => p (σs n - σ)) atTop (𝓝 0)

end GGOS

end

end

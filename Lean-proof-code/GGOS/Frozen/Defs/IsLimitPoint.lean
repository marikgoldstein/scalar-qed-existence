module

public import Mathlib
public import GGOS.Frozen.Defs.IsLocal
public import GGOS.Frozen.Defs.OmegaN
public import GGOS.Frozen.Defs.Per
public import GGOS.Frozen.Defs.TorusState
public import GGOS.Infra.Cells
public import GGOS.Infra.Coeffs
public import GGOS.Infra.IsBBL
public import GGOS.Infra.Side

/-!
# `GGOS.IsLimitPoint`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- [GG-OS] Definition 2.3: `ω` is the state of a limit point of the torus states — there are sides
`L_n → ∞` and a Borel probability measure `μ_N` on `Ω_N` such that the finite-dimensional laws of the
gauge-invariant variables under the torus states converge weakly to those of `μ_N` (equivalently:
the torus expectations of every bounded continuous local `F` converge to `∫ F dμ_N`; a local `F` is
evaluated on a torus configuration through its periodic extension), and `ω(F) = ∫ F dμ_N` for every
bounded Borel local `F`. -/
def IsLimitPoint (c : Coeffs) (ω : (Cfg ℤ → ℂ) → ℂ) : Prop :=
  ∃ (L : ℕ → Side) (μ : Measure (Cfg ℤ)),
    Tendsto (fun n => (L n).n) atTop atTop ∧
    IsProbabilityMeasure μ ∧ μ (OmegaN c.ρ0)ᶜ = 0 ∧
    (∀ F : Cfg ℤ → ℂ, IsLocal F → Continuous F → (∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) →
      Tendsto (fun n => ∫ x, F (per (L n).n x) ∂(torusState (L n) c)) atTop
        (𝓝 (∫ x, F x ∂μ))) ∧
    ∀ F : Cfg ℤ → ℂ, IsBBL F → ω F = ∫ x, F x ∂μ

end GGOS

end

end

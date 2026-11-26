module

public import Mathlib
public import GGOS.Infra.Ambient
public import GGOS.Infra.T

/-!
# `GGOS.ConvTest`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- `σ_n → σ` in `C_c^∞`: supports in a fixed compact set, all derivatives uniformly. -/
def ConvTest (σs : ℕ → T) (σ : T) : Prop :=
  (∃ K : Set E3, IsCompact K ∧
      ∀ n, (∀ μ ν, tsupport ((σs n).1.1 μ ν) ⊆ K) ∧ tsupport (σs n).1.2 ⊆ K) ∧
    ∀ k : ℕ,
      (∀ μ ν, TendstoUniformly (fun n => iteratedFDeriv ℝ k ((σs n).1.1 μ ν))
          (iteratedFDeriv ℝ k (σ.1.1 μ ν)) atTop) ∧
        TendstoUniformly (fun n => iteratedFDeriv ℝ k (σs n).1.2)
          (iteratedFDeriv ℝ k σ.1.2) atTop

end GGOS

end

end

module

public import Mathlib
public import GGOS.Frozen.Defs.MkT
public import GGOS.Frozen.Defs.Refl3
public import GGOS.Frozen.Defs.Refl3Homeo
public import GGOS.Frozen.Defs.Sgn3
public import GGOS.Infra.Refl3Lemmas
public import GGOS.Infra.T

/-!
# `GGOS.theta`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- `θσ`: the push-forward of `σ = (f, h)` under the time reflection, the 2-form transforming as
a 2-form (its components with one index 3 change sign). -/
def theta (σ : T) : T :=
  mkT (fun μ ν ξ => sgn3 μ * sgn3 ν * σ.1.1 μ ν (refl3 ξ), fun ξ => σ.1.2 (refl3 ξ))
    { antisymm := by
        intro μ ν x
        change sgn3 μ * sgn3 ν * σ.1.1 μ ν (refl3 x) = -(sgn3 ν * sgn3 μ * σ.1.1 ν μ (refl3 x))
        rw [σ.isTestPair.antisymm μ ν (refl3 x)]; ring
      smooth_f := fun μ ν =>
        contDiff_const.mul ((σ.isTestPair.smooth_f μ ν).comp contDiff_refl3)
      compact_f := fun μ ν =>
        ((σ.isTestPair.compact_f μ ν).comp_homeomorph refl3Homeo).mul_left
      smooth_h := σ.isTestPair.smooth_h.comp contDiff_refl3
      compact_h := σ.isTestPair.compact_h.comp_homeomorph refl3Homeo }

end GGOS

end

end

module

public import Mathlib
public import GGOS.Frozen.Defs.MkT
public import GGOS.Infra.Ambient
public import GGOS.Infra.T

/-!
# `GGOS.transl`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The translation of a test pair by `v ∈ ℝ³`: `(transl v σ)(ξ) = σ(ξ - v)`. -/
def transl (v : E3) (σ : T) : T :=
  mkT (fun μ ν ξ => σ.1.1 μ ν (ξ - v), fun ξ => σ.1.2 (ξ - v))
    { antisymm := fun μ ν x => σ.isTestPair.antisymm μ ν (x - v)
      smooth_f := fun μ ν => (σ.isTestPair.smooth_f μ ν).comp (contDiff_id.sub contDiff_const)
      compact_f := fun μ ν =>
        (σ.isTestPair.compact_f μ ν).comp_homeomorph (Homeomorph.subRight v)
      smooth_h := σ.isTestPair.smooth_h.comp (contDiff_id.sub contDiff_const)
      compact_h := σ.isTestPair.compact_h.comp_homeomorph (Homeomorph.subRight v) }

end GGOS

end

end

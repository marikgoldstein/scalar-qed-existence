module

public import Mathlib
public import GGOS.Frozen.Defs.Refl3
public import GGOS.Infra.Ambient
public import GGOS.Infra.Refl3Lemmas

/-!
# `GGOS.refl3Homeo`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The time reflection as a homeomorphism. -/
def refl3Homeo : E3 ≃ₜ E3 where
  toFun := refl3
  invFun := refl3
  left_inv := refl3_refl3
  right_inv := refl3_refl3
  continuous_toFun := contDiff_refl3.continuous
  continuous_invFun := contDiff_refl3.continuous

end GGOS

end

end

module

public import Mathlib
public import GGOS.Infra.Site

/-!
# `GGOS.castSite`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The torus site under a site of `ℤ³`. -/
def castSite (n : ℕ) (x : Site ℤ) : Site (ZMod n) := fun i => ((x i : ℤ) : ZMod n)

end GGOS

end

end

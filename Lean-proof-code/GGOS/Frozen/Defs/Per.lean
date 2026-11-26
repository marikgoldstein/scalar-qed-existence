module

public import Mathlib
public import GGOS.Frozen.Defs.CastSite
public import GGOS.Infra.Cells

/-!
# `GGOS.per`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The periodic extension to `ℤ³` of a torus configuration. -/
def per (n : ℕ) (ω : Cfg (ZMod n)) : Cfg ℤ :=
  (fun p => ω.1 (castSite n p.1, p.2), fun x => ω.2 (castSite n x))

end GGOS

end

end

module

public import Mathlib
public import GGOS.Frozen.Defs.Eps
public import GGOS.Frozen.Defs.SitePos
public import GGOS.Infra.Scale
public import GGOS.Infra.Site
public import GGOS.Infra.T

/-!
# `GGOS.Enorm`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- `E(h) = sup_{N ≥ N_0} ε_N³ ∑_z |h(z)|`. -/
def Enorm (sc : Scale) (N0 : ℕ) (σ : T) : ℝ :=
  ⨆ N : {N : ℕ // N0 ≤ N}, eps sc N ^ 3 * ∑' z : Site ℤ, |σ.1.2 (sitePos (eps sc N) z)|

end GGOS

end

end

module

public import Mathlib
public import GGOS.Frozen.Defs.Eps
public import GGOS.Frozen.Defs.PlaqCentre
public import GGOS.Frozen.Defs.SitePos
public import GGOS.Infra.Cells
public import GGOS.Infra.DensityFn
public import GGOS.Infra.Scale
public import GGOS.Infra.Site
public import GGOS.Infra.T

/-!
# `GGOS.Phi`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- `Φ_N(σ) = ε_N^{3/2} ∑_p f_{μν(p)}(x_p) 𝔣_p + ε_N³ ∑_z h(z) g_d(ρ̃_z)` (pinned
normalisations; finitely many non-zero terms). -/
def Phi (sc : Scale) (N : ℕ) (gd : DensityFn) (σ : T) (ω : Cfg ℤ) : ℝ :=
  eps sc N ^ (3 / 2 : ℝ) *
      (∑' p : Plaq ℤ, σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p) * ω.1 p)
    + eps sc N ^ 3 * (∑' z : Site ℤ, σ.1.2 (sitePos (eps sc N) z) * gd.toFun (ω.2 z))

end GGOS

end

end

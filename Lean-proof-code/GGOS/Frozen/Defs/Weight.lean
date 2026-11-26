module

public import Mathlib
public import GGOS.Frozen.Defs.Curv
public import GGOS.Frozen.Defs.Hop
public import GGOS.Frozen.Defs.SiteFactor
public import GGOS.Frozen.Defs.UnitVec
public import GGOS.Infra.Cells
public import GGOS.Infra.Coeffs
public import GGOS.Infra.Side
public import GGOS.Infra.Site

/-!
# `GGOS.weight`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

section Torus

variable (s : Side)

/-- The weight `W = ∏_x g_ct(ρ̃_x) ∏_b h(ρ̃_{b-}, ρ̃_{b+}, B_b) ∏_p e^{-𝔣_p²/2}` on the torus. -/
def weight (c : Coeffs) (ρt : Site (ZMod s.n) → ℝ) (B : Bond (ZMod s.n) → ℝ)
    (m : Plaq (ZMod s.n) → ℤ) : ℝ :=
  (∏ x : Site (ZMod s.n), siteFactor c (ρt x))
    * (∏ b : Bond (ZMod s.n), hop c (ρt b.1) (ρt (b.1 + unitVec (ZMod s.n) b.2)) (B b))
    * (∏ p : Plaq (ZMod s.n), Real.exp (-(curv c B m p) ^ 2 / 2))

end Torus

end GGOS

end

end

module

public import Mathlib
public import GGOS.Frozen.Defs.Eps
public import GGOS.Frozen.Defs.PlaqCentre
public import GGOS.Frozen.Defs.SitePos
public import GGOS.Infra.Ambient
public import GGOS.Infra.Cells
public import GGOS.Infra.Scale
public import GGOS.Infra.Side
public import GGOS.Infra.Site
public import GGOS.Infra.T

/-!
# `GGOS.Embeds`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- `σ` embeds in the torus of side `s` at level `N`: the closed cells that enter `Φ_N(σ)` (the
closed plaquette squares `p` with `f_{μν(p)}(x_p) ≠ 0` and the sites `z` with `h(z) ≠ 0`) lie in
an open cube of side `L = n ε_N` ([GG-OS] Section 11: "If S lies in a cube of side less than L,
the quotient map … is injective on the cells of S"). -/
def Embeds (sc : Scale) (N : ℕ) (s : Side) (σ : T) : Prop :=
  ∃ c : E3,
    (∀ p : Plaq ℤ, σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p) ≠ 0 →
      ∀ i, c i - (s.n : ℝ) * eps sc N / 2 < eps sc N * (p.1 i : ℝ) ∧
        eps sc N * ((p.1 i : ℝ) + if i = p.2.1.1 ∨ i = p.2.1.2 then 1 else 0)
          < c i + (s.n : ℝ) * eps sc N / 2) ∧
    (∀ z : Site ℤ, σ.1.2 (sitePos (eps sc N) z) ≠ 0 →
      ∀ i, |sitePos (eps sc N) z i - c i| < (s.n : ℝ) * eps sc N / 2)

end GGOS

end

end

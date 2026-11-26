module

public import Mathlib
public import GGOS.Frozen.Defs.Eps
public import GGOS.Frozen.Defs.PlaqCentre
public import GGOS.Infra.Cells
public import GGOS.Infra.Scale
public import GGOS.Infra.T

/-!
# `GGOS.Rnorm`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- `R(f) = sup_{N ≥ N_0} (ε_N³ ∑_p f_{μν(p)}(x_p)²)^{1/2}`. -/
def Rnorm (sc : Scale) (N0 : ℕ) (σ : T) : ℝ :=
  ⨆ N : {N : ℕ // N0 ≤ N},
    Real.sqrt (eps sc N ^ 3 *
      ∑' p : Plaq ℤ, (σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p)) ^ 2)

end GGOS

end

end

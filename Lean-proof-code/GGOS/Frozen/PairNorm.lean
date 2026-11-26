module

public import Mathlib
public import GGOS.Frozen.Defs.Admissible
public import GGOS.Frozen.Defs.Eps
public import GGOS.Frozen.Defs.PairNorm
public import GGOS.Frozen.Defs.PlaqCentre
public import GGOS.Frozen.Defs.SitePos
public import GGOS.Infra.Cells
public import GGOS.Infra.DensityFn
public import GGOS.Infra.IsSeminorm
public import GGOS.Infra.Scale
public import GGOS.Infra.Site
public import GGOS.Infra.T
public import GGOS.Providers.PairNorm

/-!
# [GG-OS] Definition 4.1 and the text after it
-/

public section

open MeasureTheory

namespace GGOS

/-- [GG-OS] Definition 4.1 and the text after it: the Riemann sums that define `R(f)` and `E(h)`
are bounded in `N`, `‖·‖` is a seminorm, and `‖·‖` is admissible. -/
theorem pairNorm_finite_seminorm_admissible :
    ∀ (sc : Scale) (N0 : ℕ) (gd : DensityFn),
    (∀ σ : T, BddAbove (Set.range fun N : {N : ℕ // N0 ≤ N} =>
        Real.sqrt (eps sc N ^ 3 *
          ∑' p : Plaq ℤ, (σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p)) ^ 2))) ∧
      (∀ σ : T, BddAbove (Set.range fun N : {N : ℕ // N0 ≤ N} =>
        eps sc N ^ 3 * ∑' z : Site ℤ, |σ.1.2 (sitePos (eps sc N) z)|)) ∧
      IsSeminorm (pairNorm sc N0 gd) ∧ Admissible (pairNorm sc N0 gd) :=
  by exact GGOS.Providers.pairNorm_finite_seminorm_admissible

end GGOS

end

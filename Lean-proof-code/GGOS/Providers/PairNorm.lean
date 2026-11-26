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
public import GGOS.Work.PairNormAdmissible

/-!
# Provider for `GGOS.pairNorm_finite_seminorm_admissible`

The proof of the theorem in `GGOS/Frozen/PairNorm.lean`,
as `GGOS.Providers.pairNorm_finite_seminorm_admissible`,
stated with exactly the theorem's type; the theorem is `by exact` of it.
-/

public section

namespace GGOS.Providers

/-- The sampling sums of Definition 4.1 are bounded in the level and define an admissible
seminorm on test pairs. -/
theorem pairNorm_finite_seminorm_admissible :
    ∀ (sc : Scale) (N0 : ℕ) (gd : DensityFn),
    (∀ σ : T, BddAbove (Set.range fun N : {N : ℕ // N0 ≤ N} =>
        Real.sqrt (eps sc N ^ 3 *
          ∑' p : Plaq ℤ, (σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p)) ^ 2))) ∧
      (∀ σ : T, BddAbove (Set.range fun N : {N : ℕ // N0 ≤ N} =>
        eps sc N ^ 3 * ∑' z : Site ℤ, |σ.1.2 (sitePos (eps sc N) z)|)) ∧
      IsSeminorm (pairNorm sc N0 gd) ∧ Admissible (pairNorm sc N0 gd) := by
  intro sc N0 gd
  exact ⟨fun σ => (Work.PairNorm.level_ranges_bddAbove sc N0 σ).1,
    fun σ => (Work.PairNorm.level_ranges_bddAbove sc N0 σ).2,
    Work.PairNorm.isSeminorm_pairNorm sc N0 gd, Work.PairNorm.admissible_pairNorm sc N0 gd⟩

end GGOS.Providers

end

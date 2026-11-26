module

public import Mathlib
public import GGOS.Frozen.Defs.Pull
public import GGOS.Frozen.Defs.TorusState
public import GGOS.Infra.Cells
public import GGOS.Infra.Coeffs
public import GGOS.Infra.LatSym
public import GGOS.Infra.Side
public import GGOS.Work.TorusSymmetryMeasure

/-!
# Provider for `GGOS.torus_symmetry`

The proof of the theorem in `GGOS/Frozen/TorusSymmetry.lean`,
as `GGOS.Providers.torus_symmetry`,
stated with exactly the theorem's type; the theorem is `by exact` of it.
-/

public section

open MeasureTheory

namespace GGOS.Providers

/-- Invariance of the fine torus expectation under a signed affine lattice symmetry. -/
theorem torus_symmetry :
    ∀ (c : Coeffs) (s : Side) (g : LatSym (ZMod s.n)) (F : Cfg (ZMod s.n) → ℂ) (hF : Measurable F)
      (hF_bdd : ∃ C : ℝ, ∀ ω, ‖F ω‖ ≤ C),
    ∫ ω, F (pull g ω) ∂(torusState s c) = ∫ ω, F ω ∂(torusState s c) := by
  intro c s g F hF _
  rw [← integral_map (TorusSymmetry.measurable_pull g).aemeasurable hF.aestronglyMeasurable,
    TorusSymmetry.map_torusState]

end GGOS.Providers

end

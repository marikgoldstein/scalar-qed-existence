module

public import Mathlib
public import GGOS.Frozen.Defs.Pull
public import GGOS.Frozen.Defs.TorusState
public import GGOS.Infra.Cells
public import GGOS.Infra.Coeffs
public import GGOS.Infra.LatSym
public import GGOS.Infra.Side
public import GGOS.Providers.TorusSymmetry

/-!
# [GG-OS] Lemma 5.1, first part of its proof
-/

public section

open MeasureTheory

namespace GGOS

/-- [GG-OS] Lemma 5.1, first part of its proof: each torus state is invariant under every
lattice translation, reflection and cubic rotation of its torus, `⟨F ∘ g⟩_L = ⟨F⟩_L`, for the
coefficients of Remark 2.1. -/
theorem torus_symmetry :
    ∀ (c : Coeffs) (s : Side) (g : LatSym (ZMod s.n)) (F : Cfg (ZMod s.n) → ℂ) (hF : Measurable F)
      (hF_bdd : ∃ C : ℝ, ∀ ω, ‖F ω‖ ≤ C),
    ∫ ω, F (pull g ω) ∂(torusState s c) = ∫ ω, F ω ∂(torusState s c) :=
  by exact GGOS.Providers.torus_symmetry

end GGOS

end

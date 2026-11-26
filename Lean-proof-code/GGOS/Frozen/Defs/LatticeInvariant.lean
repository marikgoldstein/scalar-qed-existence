module

public import Mathlib
public import GGOS.Frozen.Defs.Pull
public import GGOS.Infra.Cells
public import GGOS.Infra.IsBBL
public import GGOS.Infra.LatSym

/-!
# `GGOS.LatticeInvariant`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- Invariance under the translations, the reflections in the site planes and the cubic group
about the sites ([GG-OS] Lemma 5.1, first sentence). -/
def LatticeInvariant (ω : (Cfg ℤ → ℂ) → ℂ) : Prop :=
  ∀ (g : LatSym ℤ) (F : Cfg ℤ → ℂ), IsBBL F → ω (F ∘ pull g) = ω F

end GGOS

end

end

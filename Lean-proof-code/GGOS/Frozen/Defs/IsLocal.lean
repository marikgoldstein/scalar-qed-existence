module

public import Mathlib
public import GGOS.Infra.Cells
public import GGOS.Infra.Site

/-!
# `GGOS.IsLocal`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- A function of the configurations of `ℤ³` is local if it depends on the variables of finitely
many cells. -/
def IsLocal (F : Cfg ℤ → ℂ) : Prop :=
  ∃ (P : Finset (Plaq ℤ)) (X : Finset (Site ℤ)), ∀ ω ω' : Cfg ℤ,
    (∀ p ∈ P, ω.1 p = ω'.1 p) → (∀ x ∈ X, ω.2 x = ω'.2 x) → F ω = F ω'

end GGOS

end

end

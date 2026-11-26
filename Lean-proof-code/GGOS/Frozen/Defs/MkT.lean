module

public import Mathlib
public import GGOS.Infra.Ambient
public import GGOS.Infra.IsTestPair
public import GGOS.Infra.T

/-!
# `GGOS.mkT`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- A test pair from its two components. -/
def mkT (σ : Ambient) (h : IsTestPair σ) : T := ⟨σ, h⟩

end GGOS

end

end

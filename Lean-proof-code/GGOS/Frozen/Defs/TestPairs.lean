module

public import Mathlib
public import GGOS.Infra.Ambient
public import GGOS.Infra.IsTestPair

/-!
# `GGOS.TestPairs`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The real vector space `𝒯` of the test pairs, as a subspace. -/
def TestPairs : Submodule ℝ Ambient where
  carrier := {σ | IsTestPair σ}
  zero_mem' := isTestPair_zero
  add_mem' := fun ha hb => ha.add hb
  smul_mem' := fun c _ ha => ha.smul c

end GGOS

end

end

module

public import Mathlib
public import GGOS.Frozen.Defs.TestPairs
public import GGOS.Infra.IsTestPair

/-!
# `GGOS.T`, `GGOS.T.isTestPair`

Infrastructure of the [GG-OS] definitions (structures, abbreviations and their lemmas).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The real vector space `𝒯` of the test pairs. -/
abbrev T : Type := ↥TestPairs

theorem T.isTestPair (σ : T) : IsTestPair σ.1 := σ.2

end GGOS

end

end

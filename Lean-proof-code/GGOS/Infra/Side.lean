module

public import Mathlib

/-!
# `GGOS.Side`, the instance `NeZero s.n`

Infrastructure of the [GG-OS] definitions (structures, abbreviations and their lemmas).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- A torus side in lattice units: `n` sites per side, `n` even and positive (the side
`L = n ε_N` of [GG-OS] Section 2 has `L/2 ∈ ε_N ℤ`). -/
structure Side where
  /-- the number of sites per side -/
  n : ℕ
  even : Even n
  pos : 0 < n

instance (s : Side) : NeZero s.n := ⟨s.pos.ne'⟩

end GGOS

end

end

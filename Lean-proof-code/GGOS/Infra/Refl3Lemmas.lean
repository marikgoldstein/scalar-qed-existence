module

public import Mathlib
public import GGOS.Frozen.Defs.Refl3
public import GGOS.Frozen.Defs.Sgn3
public import GGOS.Infra.Ambient

/-!
# `GGOS.refl3_refl3`, `GGOS.contDiff_refl3`

Infrastructure of the [GG-OS] definitions (structures, abbreviations and their lemmas).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

theorem refl3_refl3 (ξ : E3) : refl3 (refl3 ξ) = ξ := by
  funext i
  fin_cases i <;> simp [refl3, sgn3]

theorem contDiff_refl3 : ContDiff ℝ smoothTop refl3 :=
  contDiff_pi.2 fun i => contDiff_const.mul (contDiff_apply ℝ ℝ i)

end GGOS

end

end

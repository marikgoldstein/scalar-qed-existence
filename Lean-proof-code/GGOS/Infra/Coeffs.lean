module

public import Mathlib

/-!
# `GGOS.Coeffs`

Infrastructure of the [GG-OS] definitions (structures, abbreviations and their lemmas).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The coefficients of the Villain fine model at one level ([GG-OS] Section 2), in the range of
[GG-OS] Remark 2.1. -/
structure Coeffs where
  /-- the phase constant `γ_N` -/
  γ : ℝ
  /-- the quartic coupling `λ_0` -/
  lam : ℝ
  /-- the vacuum value `ρ_{0,0}` -/
  ρ0 : ℝ
  /-- the hopping coefficient `κ_N` -/
  κ : ℝ
  /-- the bare mass counterterm `δm_B` -/
  δm : ℝ
  γ_pos : 0 < γ
  lam_pos : 0 < lam
  ρ0_pos : 0 < ρ0
  κ_nonneg : 0 ≤ κ

end GGOS

end

end

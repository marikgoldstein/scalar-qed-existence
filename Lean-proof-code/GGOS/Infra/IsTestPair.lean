module

public import Mathlib
public import GGOS.Infra.Ambient

/-!
# `GGOS.IsTestPair`, `GGOS.isTestPair_zero`, `GGOS.IsTestPair.add`, `GGOS.IsTestPair.smul`

Infrastructure of the [GG-OS] definitions (structures, abbreviations and their lemmas).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- A test pair `σ = (f, h)`: `f` a real `C_c^∞` 2-form on `ℝ³` (components `f μ ν`,
antisymmetric), `h ∈ C_c^∞(ℝ³; ℝ)`. -/
structure IsTestPair (σ : Ambient) : Prop where
  antisymm : ∀ μ ν x, σ.1 μ ν x = -σ.1 ν μ x
  smooth_f : ∀ μ ν, ContDiff ℝ smoothTop (σ.1 μ ν)
  compact_f : ∀ μ ν, HasCompactSupport (σ.1 μ ν)
  smooth_h : ContDiff ℝ smoothTop σ.2
  compact_h : HasCompactSupport σ.2

theorem isTestPair_zero : IsTestPair (0 : Ambient) where
  antisymm := by intro μ ν x; simp
  smooth_f := fun _ _ => contDiff_const
  compact_f := fun _ _ => HasCompactSupport.zero
  smooth_h := contDiff_const
  compact_h := HasCompactSupport.zero

theorem IsTestPair.add {a b : Ambient} (ha : IsTestPair a) (hb : IsTestPair b) :
    IsTestPair (a + b) where
  antisymm := by
    intro μ ν x
    change a.1 μ ν x + b.1 μ ν x = -(a.1 ν μ x + b.1 ν μ x)
    rw [ha.antisymm μ ν x, hb.antisymm μ ν x]; ring
  smooth_f := fun μ ν => (ha.smooth_f μ ν).add (hb.smooth_f μ ν)
  compact_f := fun μ ν => (ha.compact_f μ ν).add (hb.compact_f μ ν)
  smooth_h := ha.smooth_h.add hb.smooth_h
  compact_h := ha.compact_h.add hb.compact_h

theorem IsTestPair.smul (c : ℝ) {a : Ambient} (ha : IsTestPair a) : IsTestPair (c • a) where
  antisymm := by
    intro μ ν x
    change c * a.1 μ ν x = -(c * a.1 ν μ x)
    rw [ha.antisymm μ ν x]; ring
  smooth_f := fun μ ν => contDiff_const.mul (ha.smooth_f μ ν)
  compact_f := fun μ ν => (ha.compact_f μ ν).mul_left
  smooth_h := contDiff_const.mul ha.smooth_h
  compact_h := ha.compact_h.mul_left

end GGOS

end

end

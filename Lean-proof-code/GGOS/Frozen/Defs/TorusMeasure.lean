module

public import Mathlib
public import GGOS.Frozen.Defs.BondMeasure
public import GGOS.Frozen.Defs.Curv
public import GGOS.Frozen.Defs.IsClosedForm
public import GGOS.Frozen.Defs.SiteMeasure
public import GGOS.Frozen.Defs.Weight
public import GGOS.Infra.Cells
public import GGOS.Infra.Coeffs
public import GGOS.Infra.Side
public import GGOS.Infra.Site

/-!
# `GGOS.torusMeasure`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

section Torus

variable (s : Side)

/-- The torus measure of the gauge-invariant variables before normalisation: for each closed
Villain variable, the image of `W dρ̃ dB` under `(ρ̃, B) ↦ (𝔣, ρ̃)`; summed over them. -/
def torusMeasure (c : Coeffs) : Measure (Cfg (ZMod s.n)) :=
  Measure.sum fun m : {m : Plaq (ZMod s.n) → ℤ // IsClosedForm m} =>
    Measure.map
      (fun x : (Site (ZMod s.n) → ℝ) × (Bond (ZMod s.n) → ℝ) => (curv c x.2 m.1, x.1))
      (((siteMeasure s c).prod (bondMeasure s c)).withDensity
        fun x => ENNReal.ofReal (weight s c x.1 x.2 m.1))

end Torus

end GGOS

end

end

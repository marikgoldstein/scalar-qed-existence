module

public import Mathlib
public import GGOS.Frozen.Defs.EvalAnti
public import GGOS.Frozen.Defs.LatSymAct
public import GGOS.Frozen.Defs.LatSymCorner
public import GGOS.Infra.Cells
public import GGOS.Infra.LatSym

/-!
# `GGOS.pull`

A definition of [GG-OS], one declaration per file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

section Symmetry

variable {R : Type*} [CommRing R]

/-- The configuration transformed by `g`: the curvature as a lattice 2-form, the density as a
site function.  `F ∘ pull g` is `F` on the transformed configuration ([GG-OS], proof of
Lemma 5.1). -/
def pull (g : LatSym R) (ω : Cfg R) : Cfg R :=
  (fun p =>
      (((g.sgn p.2.1.1 * g.sgn p.2.1.2 : ℤˣ) : ℤ) : ℝ)
        * evalAnti ω.1 (g.act p.1 + g.corner p.2.1.1 + g.corner p.2.1.2)
            (g.perm p.2.1.1) (g.perm p.2.1.2),
    fun x => ω.2 (g.act x))

end Symmetry

end GGOS

end

end

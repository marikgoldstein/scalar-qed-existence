module

public import Mathlib
public import GGOS.Frozen.Defs.IsLimitPoint
public import GGOS.Frozen.Defs.LatticeInvariant
public import GGOS.Frozen.Defs.Iota
public import GGOS.Frozen.Defs.TauA
public import GGOS.Frozen.Defs.Phi
public import GGOS.Frozen.Defs.PairNorm
public import GGOS.Infra.IsState
public import GGOS.Frozen.TorusSymmetry
public import GGOS.Work.T71LocalMarginals
public import GGOS.Work.T71PeriodicPull

public section

open MeasureTheory Filter Topology

/-!
# Limit points of the torus states are lattice invariant ([GG-OS], theorem "limit points, with every symmetry", part (c))
-/

namespace GGOS.Work

/-- [GG-OS], theorem "limit points, with every symmetry", (c), lattice part: a limit point of the torus states is invariant under
every lattice symmetry of `ℤ³` (translations, reflections in site planes, cubic group). -/
theorem latticeInvariant_of_isLimitPoint (c : Coeffs) (ω : (Cfg ℤ → ℂ) → ℂ)
    (h : IsLimitPoint c ω) : LatticeInvariant ω := by
  obtain ⟨L, μ, _, hμ, _, hlim, hω⟩ := h
  intro g F hF
  have hg := TorusSymmetry.measurable_pull g
  have map_eq : μ.map (pull g) = μ := by
    apply measure_eq_of_integral_local_eq
    intro A hloc hc
    rintro ⟨C, hC⟩
    have limPull := hlim (A ∘ pull g) (isLocal_comp_pull hloc g) (hc.comp (continuous_pull g))
      ⟨C, fun x => hC (pull g x)⟩
    rw [integral_map hg.aemeasurable hc.aestronglyMeasurable]
    refine tendsto_nhds_unique (limPull.congr ?_) (hlim A hloc hc ⟨C, hC⟩)
    intro n
    change (∫ x, A (pull g (per (L n).n x)) ∂torusState (L n) c) = _
    simp_rw [← per_pull]
    exact torus_symmetry c (L n) (torusLatSym (L n).n g) (A ∘ per (L n).n)
      (hc.measurable.comp (by unfold per; fun_prop)) ⟨C, fun x => hC (per (L n).n x)⟩
  obtain ⟨C, hC⟩ := hF.bounded
  have hcomp : IsBBL (F ∘ pull g) :=
    ⟨hF.measurable.comp hg, ⟨C, fun x => hC (pull g x)⟩, isLocal_comp_pull hF.isLocal g⟩
  calc
    ω (F ∘ pull g) = ∫ x, F (pull g x) ∂μ := hω _ hcomp
    _ = ∫ x, F x ∂(μ.map (pull g)) :=
      (integral_map hg.aemeasurable hF.measurable.aestronglyMeasurable).symm
    _ = ∫ x, F x ∂μ := by rw [map_eq]
    _ = ω F := (hω _ hF).symm

end GGOS.Work

end

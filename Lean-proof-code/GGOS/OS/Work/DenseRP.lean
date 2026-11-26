module

public import Mathlib

/-!
# A positive form on bounded continuous functions is positive on `L²`
-/

@[expose] public section

open MeasureTheory
open scoped ComplexOrder ENNReal

namespace GGOS.OS

theorem nonneg_of_continuous {Y Ω : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [T4Space Y] [SecondCountableTopologyEither Y ℂ] [MeasurableSpace Ω] {ν : Measure Y}
    [IsFiniteMeasure ν] [ν.WeaklyRegular] {μ : Measure Ω} {p q : Ω → Y}
    (hp : MeasurePreserving p μ ν) (hq : MeasurePreserving q μ ν)
    (h : ∀ g : BoundedContinuousFunction Y ℂ, 0 ≤ ∫ x, starRingEnd ℂ (g (q x)) * g (p x) ∂μ)
    {f : Y → ℂ} (hf : MemLp f 2 ν) : 0 ≤ ∫ x, starRingEnd ℂ (f (q x)) * f (p x) ∂μ := by
  let A : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 μ := Lp.compMeasurePreservingₗᵢ ℂ p hp
  let B : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 μ := Lp.compMeasurePreservingₗᵢ ℂ q hq
  have hA (u : Lp ℂ 2 ν) : (A u : Ω → ℂ) =ᵐ[μ] fun x => u (p x) :=
    Lp.coeFn_compMeasurePreserving u hp
  have hB (u : Lp ℂ 2 ν) : (B u : Ω → ℂ) =ᵐ[μ] fun x => u (q x) :=
    Lp.coeFn_compMeasurePreserving u hq
  have hinner (u : Lp ℂ 2 ν) : inner ℂ (B u) (A u) = ∫ x, starRingEnd ℂ (u (q x)) * u (p x) ∂μ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hA u, hB u] with x h1 h2
    rw [h1, h2, RCLike.inner_apply, mul_comm]
  have hfun (u : Lp ℂ 2 ν) (g : Y → ℂ) (hu : u =ᵐ[ν] g) :
      ∫ x, starRingEnd ℂ (u (q x)) * u (p x) ∂μ = ∫ x, starRingEnd ℂ (g (q x)) * g (p x) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hp.quasiMeasurePreserving.ae hu, hq.quasiMeasurePreserving.ae hu] with x h1 h2
    rw [h1, h2]
  have key (u : Lp ℂ 2 ν) : 0 ≤ inner ℂ (B u) (A u) := by
    refine DenseRange.induction_on (BoundedContinuousFunction.toLp_denseRange ℂ ν ℂ
      (p := 2) ENNReal.ofNat_ne_top) u ?_ fun g => ?_
    · exact isClosed_le continuous_const (B.continuous.inner A.continuous)
    · rw [hinner, hfun _ _ (BoundedContinuousFunction.coeFn_toLp 2 ν ℂ g)]
      exact h g
  have := key (hf.toLp f)
  rwa [hinner, hfun _ _ hf.coeFn_toLp] at this

end GGOS.OS

end

module

public import Mathlib
public import GGOS.Frozen.Defs.TorusState
public import GGOS.Infra.Cells
public import GGOS.Infra.Coeffs
public import GGOS.Infra.Side
public import GGOS.Frozen.GaussianDomination
public import GGOS.Work.SubGaussianMoments

/-!
# Provider for `GGOS.gaussian_moments`

The proof of the theorem in `GGOS/Frozen/GaussianMoments.lean`,
as `GGOS.Providers.gaussian_moments`,
stated with exactly the theorem's type; the theorem is `by exact` of it.
-/

public section

open MeasureTheory

namespace GGOS.Providers

/-- [GG-OS] Theorem 3.1, second sentence: from the first sentence (`GGOS.gaussian_domination`,
applied to `s • a` for every real `s`) and `GGOS.Work.moments_of_mgf_le`. -/
theorem gaussian_moments :
    ∀ (c : Coeffs) (s : Side) (a : Plaq (ZMod s.n) → ℝ),
    (Integrable (fun ω : Cfg (ZMod s.n) => ∑ p, a p * ω.1 p) (torusState s c) ∧
        ∫ ω, (∑ p, a p * ω.1 p) ∂(torusState s c) = 0) ∧
      (Integrable (fun ω : Cfg (ZMod s.n) => (∑ p, a p * ω.1 p) ^ 2) (torusState s c) ∧
        ∫ ω, (∑ p, a p * ω.1 p) ^ 2 ∂(torusState s c) ≤ ∑ p, a p ^ 2) ∧
      ∀ k : ℕ, 1 ≤ k →
        Integrable (fun ω : Cfg (ZMod s.n) => (∑ p, a p * ω.1 p) ^ (2 * k)) (torusState s c) ∧
          ∫ ω, (∑ p, a p * ω.1 p) ^ (2 * k) ∂(torusState s c) ≤
            ((2 * k).factorial : ℝ) * (Real.exp 1 * (∑ p, a p ^ 2) / (2 * k : ℝ)) ^ k := by
  intro c s a
  haveI : IsProbabilityMeasure (torusState s c) := (GGOS.gaussian_domination c s a).1
  have hsum : ∀ (t : ℝ) (ω : Cfg (ZMod s.n)),
      ∑ p, (t * a p) * ω.1 p = t * ∑ p, a p * ω.1 p := by
    intro t ω
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hint : ∀ t : ℝ, Integrable (fun ω : Cfg (ZMod s.n) =>
      Real.exp (t * ∑ p, a p * ω.1 p)) (torusState s c) := by
    intro t
    have h := (GGOS.gaussian_domination c s (fun p => t * a p)).2.1
    simpa only [hsum] using h
  have hmgf : ∀ t : ℝ, ∫ ω, Real.exp (t * ∑ p, a p * ω.1 p) ∂(torusState s c)
      ≤ Real.exp (t ^ 2 * (∑ p, a p ^ 2) / 2) := by
    intro t
    have h := (GGOS.gaussian_domination c s (fun p => t * a p)).2.2
    simp only [hsum] at h
    have he : (1 / 2 * ∑ p, (t * a p) ^ 2) = t ^ 2 * (∑ p, a p ^ 2) / 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
      exact Finset.sum_congr rfl fun p _ => by ring
    rwa [he] at h
  have hmeas : AEMeasurable (fun ω : Cfg (ZMod s.n) => ∑ p, a p * ω.1 p) (torusState s c) := by
    apply Measurable.aemeasurable
    exact Finset.measurable_sum _ fun p _ =>
      measurable_const.mul ((measurable_pi_apply p).comp measurable_fst)
  exact GGOS.Work.moments_of_mgf_le (torusState s c) _ hmeas _ hint hmgf

end GGOS.Providers

end

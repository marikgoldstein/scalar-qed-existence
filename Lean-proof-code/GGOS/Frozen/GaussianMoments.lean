module

public import Mathlib
public import GGOS.Frozen.Defs.TorusState
public import GGOS.Infra.Cells
public import GGOS.Infra.Coeffs
public import GGOS.Infra.Side
public import GGOS.Providers.GaussianMoments

/-!
# [GG-OS] Theorem 3.1, second sentence
-/

public section

open MeasureTheory

namespace GGOS

/-- [GG-OS] Theorem 3.1, second sentence: with `X = ∑_p a_p 𝔣_p`, `⟨X⟩ = 0`, `⟨X²⟩ ≤ ∑_p a_p²`
and `⟨X^{2k}⟩ ≤ (2k)! (e ∑_p a_p² / 2k)^k` for `k ≥ 1`, for the coefficients of Remark 2.1. -/
theorem gaussian_moments :
    ∀ (c : Coeffs) (s : Side) (a : Plaq (ZMod s.n) → ℝ),
    (Integrable (fun ω : Cfg (ZMod s.n) => ∑ p, a p * ω.1 p) (torusState s c) ∧
        ∫ ω, (∑ p, a p * ω.1 p) ∂(torusState s c) = 0) ∧
      (Integrable (fun ω : Cfg (ZMod s.n) => (∑ p, a p * ω.1 p) ^ 2) (torusState s c) ∧
        ∫ ω, (∑ p, a p * ω.1 p) ^ 2 ∂(torusState s c) ≤ ∑ p, a p ^ 2) ∧
      ∀ k : ℕ, 1 ≤ k →
        Integrable (fun ω : Cfg (ZMod s.n) => (∑ p, a p * ω.1 p) ^ (2 * k)) (torusState s c) ∧
          ∫ ω, (∑ p, a p * ω.1 p) ^ (2 * k) ∂(torusState s c) ≤
            ((2 * k).factorial : ℝ) * (Real.exp 1 * (∑ p, a p ^ 2) / (2 * k : ℝ)) ^ k :=
  by exact GGOS.Providers.gaussian_moments

end GGOS

end

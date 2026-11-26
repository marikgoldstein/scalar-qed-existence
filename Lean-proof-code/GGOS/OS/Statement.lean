module

public import Mathlib
public import GGOS.Frozen.Defs.IsLimitPoint
public import GGOS.Infra.Coeffs
public import GGOS.OS.Axioms
public import GGOS.OS.Work.Main

/-!
# The statement: OS0, OS1 without rotations, OS2 and OS3 for every limit functional
-/

public section

open MeasureTheory Filter Topology

namespace GGOS

/-- From [GG-OS] Section 9 (Theorem 9.4, Propositions 9.6, 9.9, 9.11 and 9.12, as listed in `OS0`,
`OS1Cubic`, `OS2`, `OS3`).  Given states `ω_N` that are limit points of the torus states
(Definition 2.3; their existence, [GG-OS] Theorem 11.5, is assumed, not proved here), limit
functionals of them along levels `N_m → ∞` exist, and every one satisfies OS0, OS1 without rotations,
OS2 and OS3; its Schwinger functions are the limits along `N_m` of the correlation functions of the
states `ω_{N_m}`.  The constant `C` of (E0′) (`OS0.tempered`) depends on the length `a_0` and on the
density function `g_d` only.  Not claimed: rotation invariance, OS4, a measure on distributions,
uniqueness of the limit. -/
theorem osterwalder_schrader :
    ∀ (sc : Scale) (gd : DensityFn), ∃ C : ℝ,
      ∀ (N0 : ℕ) (c : ℕ → Coeffs) (ω : ℕ → (Cfg ℤ → ℂ) → ℂ)
        (_ : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N)),
      (∃ (Nm : ℕ → ℕ) (S : Alg →ₗ[ℂ] ℂ), IsLimitFunctional sc N0 gd ω Nm S) ∧
        ∀ (Nm : ℕ → ℕ) (S : Alg →ₗ[ℂ] ℂ), IsLimitFunctional sc N0 gd ω Nm S →
          OS0 sc N0 gd C S ∧ OS1Cubic S ∧ OS2 S ∧ OS3 S ∧
          ∀ (μ : ℕ → Measure (Cfg ℤ)),
            (∀ N, N0 ≤ N → IsProbabilityMeasure (μ N) ∧ ∀ F, IsBBL F → ω N F = ∫ x, F x ∂(μ N)) →
            ∀ (n : ℕ) (σ : Fin n → T),
              (∀ m, Integrable (fun x => ∏ i, Phi sc (Nm m) gd (σ i) x) (μ (Nm m))) ∧
              Tendsto (fun m => ((∫ x, ∏ i, Phi sc (Nm m) gd (σ i) x ∂(μ (Nm m)) : ℝ) : ℂ)) atTop
                (𝓝 (schwinger S σ)) :=
  by exact GGOS.OS.osterwalder_schrader

end GGOS

end

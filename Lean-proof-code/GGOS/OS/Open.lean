module

public import Mathlib
public import GGOS.OS.Axioms
public import GGOS.OS.Rotation
public import GGOS.OS.Schwartz

/-!
# The two parts of the full statement that are not formalized

Both are proved in [GG-OS]; here they are stated with `sorry`.
-/

@[expose] public section

noncomputable section

namespace GGOS.OS

/-- [GG-OS] Theorem 9.4 (i), (iii): OS0 on Schwartz test functions, from the bounds of OS0 and the
multilinearity of OS3 on smooth compactly supported test pairs (by density). Not formalized. -/
theorem os0Schwartz_of {sc : Scale} {N0 : ℕ} {gd : DensityFn} {C : ℝ} {S : Alg →ₗ[ℂ] ℂ}
    (h0 : OS0 sc N0 gd C S) (h3 : OS3 S) : OS0Schwartz C S := by
  sorry

/-- [GG-OS] Theorem 12.4 (with Theorems 12.2 and 12.3): the limit functionals of torus limit points
along dyadic sequences of sides, with positive hopping coefficients at every level, are invariant
under `O(3)`. Not formalized. -/
theorem rotation_invariance {sc : Scale} {N0 : ℕ} {gd : DensityFn} {c : ℕ → Coeffs}
    {ω : ℕ → (Cfg ℤ → ℂ) → ℂ} {Nm : ℕ → ℕ} {S : Alg →ₗ[ℂ] ℂ}
    (hω : ∀ N, N0 ≤ N → 0 < (c N).κ ∧ IsDyadicLimitPoint N (c N) (ω N))
    (hS : IsLimitFunctional sc N0 gd ω Nm S) (O : O3) (σ : T) :
    S (basisE (rotT O σ)) = S (basisE σ) := by
  sorry

end GGOS.OS

end

end

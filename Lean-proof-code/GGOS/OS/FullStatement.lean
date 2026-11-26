module

public import Mathlib
public import GGOS.Frozen.Defs.IsLimitPoint
public import GGOS.Infra.Coeffs
public import GGOS.OS.Axioms
public import GGOS.OS.Rotation
public import GGOS.OS.Schwartz
public import GGOS.OS.Work.Full

/-!
# The full statement: the Osterwalder–Schrader axioms as far as [GG-OS] proves them
-/

public section

open MeasureTheory Filter Topology

namespace GGOS

/-- The Osterwalder–Schrader axioms for every limit functional of limit points of the torus states.
Proved in Lean (`GGOS.osterwalder_schrader`): OS0 on smooth compactly supported test pairs, OS1
without rotations, OS2, OS3. Stated with `sorry` (`GGOS.OS.os0Schwartz_of`,
`GGOS.OS.rotation_invariance`): OS0 on Schwartz test functions ([GG-OS] Theorem 9.4 (i), (iii)), and
OS1 for the whole Euclidean group when the limit points run along dyadic sequences of sides and the
hopping coefficients are positive ([GG-OS] Theorem 12.4). OS4 is not stated: [GG-OS] proves it in a
weak form, for the ergodic components of the measure of its Theorem 9.13 (Theorem 9.15). -/
theorem osterwalder_schrader_full :
    ∀ (sc : Scale) (gd : DensityFn), ∃ C : ℝ,
      ∀ (N0 : ℕ) (c : ℕ → Coeffs) (ω : ℕ → (Cfg ℤ → ℂ) → ℂ)
        (_ : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N)),
      (∃ (Nm : ℕ → ℕ) (S : Alg →ₗ[ℂ] ℂ), IsLimitFunctional sc N0 gd ω Nm S) ∧
        ∀ (Nm : ℕ → ℕ) (S : Alg →ₗ[ℂ] ℂ), IsLimitFunctional sc N0 gd ω Nm S →
          OS0 sc N0 gd C S ∧ OS0Schwartz C S ∧ OS1Cubic S ∧ OS2 S ∧ OS3 S ∧
          ((∀ N, N0 ≤ N → 0 < (c N).κ ∧ IsDyadicLimitPoint N (c N) (ω N)) → OS1 S) :=
  by exact GGOS.OS.osterwalder_schrader_full

end GGOS

end

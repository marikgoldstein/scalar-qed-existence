module

public import GGOS.OS.Open
public import GGOS.OS.Statement
public import GGOS.OS.Work.Invariance

/-!
# Assembly of the full statement
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS.OS

/-- The motion `x ↦ x + y` acts on test pairs as the translation by `y`. -/
theorem pushT_translation (y : E3) (σ : T) :
    pushT ⟨Equiv.refl _, fun _ => 1, y⟩ σ = transl y σ := by
  have hinv (ξ : E3) : LatSym.invAct ⟨Equiv.refl (Fin 3), fun _ => (1 : ℤˣ), y⟩ ξ = ξ - y := by
    funext i
    simp [LatSym.invAct]
  refine T_ext (fun μ ν x => ?_) fun x => ?_
  · change ((((1 : ℤˣ) * 1 : ℤˣ) : ℤ) : ℝ) * σ.1.1 μ ν _ = σ.1.1 μ ν (x - y)
    rw [hinv]
    simp
  · change σ.1.2 _ = σ.1.2 (x - y)
    rw [hinv]

/-- OS1 from OS1 without rotations and the invariance under `O(3)`. -/
theorem os1_of_rotations {S : Alg →ₗ[ℂ] ℂ} (h1 : OS1Cubic S)
    (hrot : ∀ (O : O3) (σ : T), S (basisE (rotT O σ)) = S (basisE σ)) : OS1 S := by
  intro O y σ
  rw [← pushT_translation, ← pushA_basisE, h1.invariant, hrot]

theorem osterwalder_schrader_full :
    ∀ (sc : Scale) (gd : DensityFn), ∃ C : ℝ,
      ∀ (N0 : ℕ) (c : ℕ → Coeffs) (ω : ℕ → (Cfg ℤ → ℂ) → ℂ)
        (_ : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N)),
      (∃ (Nm : ℕ → ℕ) (S : Alg →ₗ[ℂ] ℂ), IsLimitFunctional sc N0 gd ω Nm S) ∧
        ∀ (Nm : ℕ → ℕ) (S : Alg →ₗ[ℂ] ℂ), IsLimitFunctional sc N0 gd ω Nm S →
          OS0 sc N0 gd C S ∧ OS0Schwartz C S ∧ OS1Cubic S ∧ OS2 S ∧ OS3 S ∧
          ((∀ N, N0 ≤ N → 0 < (c N).κ ∧ IsDyadicLimitPoint N (c N) (ω N)) → OS1 S) := by
  intro sc gd
  obtain ⟨C, hC⟩ := GGOS.osterwalder_schrader sc gd
  refine ⟨C, fun N0 c ω hω => ⟨(hC N0 c ω hω).1, fun Nm S hS => ?_⟩⟩
  obtain ⟨h0, h1, h2, h3, -⟩ := (hC N0 c ω hω).2 Nm S hS
  exact ⟨h0, os0Schwartz_of h0 h3, h1, h2, h3,
    fun hd => os1_of_rotations h1 (rotation_invariance hd hS)⟩

end GGOS.OS

end

end

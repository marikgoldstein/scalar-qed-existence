module

public import GGOS.Frozen.Defs.IsLimitPoint
public import GGOS.Frozen.Defs.PairNorm
public import GGOS.Frozen.PairNorm
public import GGOS.OS.LimitFunctionalDef
public import GGOS.OS.Work.Phase
public import GGOS.Work.T71Estimate
public import GGOS.Work.T71Invariance
public import GGOS.Work.T71State

/-!
# First properties of a limit functional: values on the basis, and the norm bound
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS.OS

variable {sc : Scale} {N0 : ℕ} {gd : DensityFn} {c : ℕ → Coeffs}
  {ω : ℕ → (Cfg ℤ → ℂ) → ℂ} {Nm : ℕ → ℕ} {S : Alg →ₗ[ℂ] ℂ}

theorem tendsto_basis (hS : IsLimitFunctional sc N0 gd ω Nm S) (σ : T) :
    Tendsto (fun m => ω (Nm m) (expPhi sc (Nm m) gd σ)) atTop (𝓝 (S (basisE σ))) := by
  simpa only [iota_basisE] using hS.tendsto (basisE σ)

theorem state_lipschitz (hω : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N)) {N : ℕ} (hN : N0 ≤ N)
    (σ τ : T) :
    ‖ω N (expPhi sc N gd σ) - ω N (expPhi sc N gd τ)‖ ≤ pairNorm sc N0 gd (σ - τ) :=
  Work.Limit.norm_state_exp_sub_le sc N gd
    (Work.isState_of_isLimitPoint (c N) (ω N) (hω N hN))
    (fun σ => Work.trunc_le_pairNorm_of_isLimitPoint sc N0 gd (c N) (ω N) N hN (hω N hN) σ) σ τ

/-- [GG-OS] Theorem 9.4 (i): the generating functional is 1-Lipschitz for the norm `‖·‖`. -/
theorem basis_lipschitz (hω : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N))
    (hS : IsLimitFunctional sc N0 gd ω Nm S) (σ τ : T) :
    ‖S (basisE σ) - S (basisE τ)‖ ≤ pairNorm sc N0 gd (σ - τ) :=
  le_of_tendsto' ((tendsto_basis hS σ).sub (tendsto_basis hS τ)).norm
    fun m => state_lipschitz hω (hS.le m) σ τ

theorem basis_zero (hω : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N))
    (hS : IsLimitFunctional sc N0 gd ω Nm S) : S (basisE 0) = 1 := by
  refine tendsto_nhds_unique (tendsto_basis hS 0) ?_
  have h (m : ℕ) : ω (Nm m) (expPhi sc (Nm m) gd 0) = 1 := by
    have he : expPhi sc (Nm m) gd 0 = fun _ => 1 := funext fun x => expPhi_zero sc (Nm m) gd x
    rw [he]
    exact (Work.isState_of_isLimitPoint _ _ (hω _ (hS.le m))).map_one
  simp only [h]
  exact tendsto_const_nhds

end GGOS.OS

end

end

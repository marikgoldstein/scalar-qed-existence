module

public import GGOS.OS.Axioms
public import GGOS.OS.Work.Limit
public import GGOS.Work.PushLattice
public import GGOS.Work.LimitLattice
public import GGOS.Work.LimitTests

/-!
# OS1 without rotations ([GG-OS] Proposition 9.6)
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS.OS

variable {sc : Scale} {N0 : ℕ} {gd : DensityFn} {c : ℕ → Coeffs}
  {ω : ℕ → (Cfg ℤ → ℂ) → ℂ} {Nm : ℕ → ℕ} {S : Alg →ₗ[ℂ] ℂ}

theorem basis_push (hω : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N))
    (hS : IsLimitFunctional sc N0 gd ω Nm S) (g : LatSym ℝ) (σ : T) :
    S (basisE (pushT g σ)) = S (basisE σ) := by
  obtain ⟨j, hj⟩ := Work.Limit.exists_mesh_approx sc g.shift
  set τ := pushT (linPart g) σ with hτ
  have hu : Tendsto (fun m => sitePos (eps sc (Nm m)) (j (Nm m))) atTop (𝓝 g.shift) :=
    hj.comp hS.strictMono.tendsto_atTop
  have hadm := (GGOS.pairNorm_finite_seminorm_admissible sc N0 gd).2.2.2
  have hzero : Tendsto (fun m => ‖ω (Nm m) (expPhi sc (Nm m) gd σ) -
      ω (Nm m) (expPhi sc (Nm m) gd (pushT g σ))‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_)
      (hadm _ _ (Work.Limit.convTest_transl hu τ))
    have hinv := Work.latticeInvariant_of_isLimitPoint (c (Nm m)) (ω (Nm m)) (hω _ (hS.le m))
    rw [← state_expPhi_push sc (Nm m) gd hinv (meshSym g (j (Nm m))) σ, push_scaled_meshSym,
      push_eq_transl g σ]
    exact state_lipschitz hω (hS.le m) _ _
  have h := tendsto_nhds_unique ((tendsto_basis hS σ).sub (tendsto_basis hS (pushT g σ))).norm hzero
  exact (sub_eq_zero.mp (norm_eq_zero.mp h)).symm

theorem pushA_basisE (g : LatSym ℝ) (σ : T) : pushA g (basisE σ) = basisE (pushT g σ) := by
  simp [pushA, basisE, AddMonoidAlgebra.mapDomain_single]

theorem pushA_add (g : LatSym ℝ) (a b : Alg) : pushA g (a + b) = pushA g a + pushA g b :=
  AddMonoidAlgebra.mapDomain_add _ _ _

theorem pushA_smul (g : LatSym ℝ) (z : ℂ) (a : Alg) : pushA g (z • a) = z • pushA g a :=
  (AddMonoidAlgebra.mapDomainLinearMap ℂ ℂ (pushT g)).map_smul z a

theorem genFun_push (hω : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N))
    (hS : IsLimitFunctional sc N0 gd ω Nm S) (g : LatSym ℝ) {n : ℕ} (σ : Fin n → T) :
    genFun S (fun i => pushT g (σ i)) = genFun S σ := by
  funext t
  unfold genFun
  rw [← push_sum_smul, basis_push hω hS]

/-- [GG-OS] Proposition 9.6. -/
theorem os1Cubic (hω : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N))
    (hS : IsLimitFunctional sc N0 gd ω Nm S) : OS1Cubic S where
  invariant g a := by
    induction a using alg_induction with
    | hb σ => rw [pushA_basisE, basis_push hω hS]
    | hadd a b ha hb => rw [pushA_add, map_add, map_add, ha, hb]
    | hsmul z a ha => rw [pushA_smul, map_smul, map_smul, ha]
  schwinger_invariant g n σ := by
    unfold schwinger
    rw [genFun_push hω hS]

end GGOS.OS

end

end

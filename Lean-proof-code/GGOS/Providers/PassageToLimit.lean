module

public import Mathlib
public import GGOS.Frozen.Defs.Admissible
public import GGOS.Frozen.Defs.Aplus
public import GGOS.Frozen.Defs.Eps
public import GGOS.Frozen.Defs.Iota
public import GGOS.Frozen.Defs.LatSymAct
public import GGOS.Frozen.Defs.LatticeInvariant
public import GGOS.Frozen.Defs.Mnorm
public import GGOS.Frozen.Defs.Phi
public import GGOS.Frozen.Defs.SitePos
public import GGOS.Frozen.Defs.TauA
public import GGOS.Frozen.Defs.ThetaA
public import GGOS.Frozen.Defs.TranslA
public import GGOS.Infra.Alg
public import GGOS.Infra.Ambient
public import GGOS.Infra.Cells
public import GGOS.Infra.DensityFn
public import GGOS.Infra.IsSeminorm
public import GGOS.Infra.IsState
public import GGOS.Infra.LatSym
public import GGOS.Infra.Motion
public import GGOS.Infra.Scale
public import GGOS.Infra.T
public import GGOS.Work.LimitAlgebra
public import GGOS.Work.LimitCompactness
public import GGOS.Work.LimitLattice
public import GGOS.Work.PushLattice

/-!
# Provider for `GGOS.passage_to_limit`

The proof of the theorem in `GGOS/Frozen/PassageToLimit.lean`,
as `GGOS.Providers.passage_to_limit`,
stated with exactly the theorem's type; the theorem is `by exact` of it.
-/

public section

open MeasureTheory Filter Topology
open GGOS.Work.Limit

namespace GGOS.Providers

/-- [GG-OS] Proposition 6.1 (the passage to the limit), with the estimate in the truncated form
of Remark 6.2 (i). The cubic group about a point is the group of the motions `g` of `GGOS.LatSym ℝ`
that fix it. -/
theorem passage_to_limit :
    ∀ (sc : Scale) (N0 : ℕ) (gd : DensityFn) (ρ0 : ℕ → ℝ) (ω : ℕ → (Cfg ℤ → ℂ) → ℂ) (p : T → ℝ)
      (hρ0 : ∀ N, N0 ≤ N → 0 < ρ0 N) (hstate : ∀ N, N0 ≤ N → IsState (ρ0 N) (ω N))
      (hinv : ∀ N, N0 ≤ N → LatticeInvariant (ω N)) (htime : ∀ N, N0 ≤ N → ∀ (a : Alg) (k : ℤ),
        ω N (iota sc N gd (tauA (eps sc N * k) a)) = ω N (iota sc N gd a))
      (hp : IsSeminorm p) (hp_adm : Admissible p) (hest : ∀ N, N0 ≤ N → ∀ σ : T,
        (ω N fun x => ((min |Phi sc N gd σ x| 2 : ℝ) : ℂ)).re ≤ p σ),
    ∃ (Nm : ℕ → ℕ) (S : Alg →ₗ[ℂ] ℂ),
      StrictMono Nm ∧ (∀ m, N0 ≤ Nm m) ∧
      (∀ a : Alg, Tendsto (fun m => ω (Nm m) (iota sc (Nm m) gd a)) atTop (𝓝 (S a))) ∧
      (∀ (t : ℝ) (a : Alg), S (tauA t a) = S a) ∧
      (∀ a ∈ Aplus, ∀ b ∈ Aplus,
        ContinuousOn (fun t : ℝ => S (ThetaA a * tauA t b)) (Set.Ici 0)) ∧
      (∀ v : E3, v 2 = 0 → ∀ a : Alg, S (translA v a) = S a) ∧
      (∀ (m : ℕ) (z : Site ℤ) (g : LatSym ℝ),
        g.act (sitePos (eps sc (Nm m)) z) = sitePos (eps sc (Nm m)) z →
          ∀ a : Alg, S (pushA g a) = S a) ∧
      ∀ a : Alg, ‖S a‖ ≤ Mnorm a := by
  intro sc N0 gd ρ0 ω p _hρ0 hstate hinv _htime _hp hp_adm hest
  let F (N : ℕ) (σ : T) := ω N (expPhi sc N gd σ)
  have hbound N (hN : N0 ≤ N) (σ : T) : ‖F N σ‖ ≤ 1 :=
    norm_state_exp_le sc N gd (hstate N hN) σ
  have hmod N (hN : N0 ≤ N) (σ τ : T) : ‖F N σ - F N τ‖ ≤ p (σ - τ) :=
    norm_state_exp_sub_le sc N gd (hstate N hN) (hest N hN) σ τ
  obtain ⟨Nm, Z, hmono, hN0, hZ⟩ := exists_basis_limit F N0 hp_adm hbound hmod
  have hZbound σ : ‖Z σ‖ ≤ 1 :=
    le_of_tendsto' (hZ σ).norm (fun m => hbound _ (hN0 m) σ)
  have hZmod σ τ : ‖Z σ - Z τ‖ ≤ p (σ - τ) :=
    le_of_tendsto' ((hZ σ).sub (hZ τ)).norm (fun m => hmod _ (hN0 m) σ τ)
  have htrans (v : E3) (σ : T) : Z (transl v σ) = Z σ := by
    obtain ⟨j, hj⟩ := exists_mesh_approx sc v
    let u (m : ℕ) := sitePos (eps sc (Nm m)) (j (Nm m))
    have hu : Tendsto u atTop (𝓝 v) := hj.comp hmono.tendsto_atTop
    have he m : F (Nm m) (transl (u m) σ) = F (Nm m) σ :=
      state_exp_mesh_eq sc (Nm m) gd (hinv _ (hN0 m)) σ _
    have hzero : Tendsto (fun m => ‖F (Nm m) σ - F (Nm m) (transl v σ)‖) atTop (𝓝 0) := by
      refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_) (hp_adm _ _ (convTest_transl hu σ))
      rw [← he m]
      exact hmod _ (hN0 m) _ _
    have h := tendsto_nhds_unique ((hZ σ).sub (hZ (transl v σ))).norm hzero
    exact (sub_eq_zero.mp (norm_eq_zero.mp h)).symm
  have hpush (g : LatSym ℝ) (σ : T) : Z (pushT g σ) = Z σ := by
    obtain ⟨j, hj⟩ := exists_mesh_approx sc g.shift
    let u (m : ℕ) := sitePos (eps sc (Nm m)) (j (Nm m))
    have hu : Tendsto u atTop (𝓝 g.shift) := hj.comp hmono.tendsto_atTop
    have he m : F (Nm m) (transl (u m) (pushT (OS.linPart g) σ)) = F (Nm m) σ := by
      have h := OS.state_expPhi_push sc (Nm m) gd (hinv _ (hN0 m)) (OS.meshSym g (j (Nm m))) σ
      rwa [OS.push_scaled_meshSym] at h
    have hzero : Tendsto (fun m => ‖F (Nm m) σ - F (Nm m) (pushT g σ)‖) atTop (𝓝 0) := by
      refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_)
        (hp_adm _ _ (convTest_transl hu (pushT (OS.linPart g) σ)))
      rw [← he m, OS.push_eq_transl g σ]
      exact hmod _ (hN0 m) _ _
    have h := tendsto_nhds_unique ((hZ σ).sub (hZ (pushT g σ))).norm hzero
    exact (sub_eq_zero.mp (norm_eq_zero.mp h)).symm
  refine ⟨Nm, linearExtension Z, hmono, hN0,
    tendsto_iota sc gd (fun m => hstate _ (hN0 m)) hZ,
    fun t a => extension_transl _ (htrans (Pi.single 2 t)) a, ?_,
    fun v _ a => extension_transl v (htrans v) a,
    fun _ _ g _ a => extension_push g (hpush g) a, norm_extension_le hZbound⟩
  intro a _ b _
  have ht : Continuous (fun t : ℝ => (Pi.single 2 t : E3)) :=
    continuous_single (A := fun _ : Fin 3 => ℝ) 2
  exact ((continuous_mixed hp_adm hZmod (ThetaA a) b).comp ht).continuousOn

end GGOS.Providers

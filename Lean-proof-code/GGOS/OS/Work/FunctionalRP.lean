module

public import GGOS.OS.Work.Planes
public import GGOS.OS.Work.StateRP

/-!
# OS2 for the limit functional, functional form ([GG-OS] Proposition 9.9)
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ComplexOrder ENNReal

namespace GGOS.OS

theorem scaled_timeRefl (ε : ℝ) : scaled ε (timeRefl ℤ) = reflPlane 2 0 := by
  refine motion_ext rfl ?_ ?_
  · funext i
    fin_cases i <;> simp [scaled, timeRefl, reflPlane]
  · funext i
    fin_cases i <;> simp [scaled, timeRefl, reflPlane]

theorem phi_refl (sc : Scale) (N : ℕ) (gd : DensityFn) (σ : T) (x : Cfg ℤ) :
    Phi sc N gd (pushT (reflPlane 2 0) σ) x = Phi sc N gd σ (pull (timeRefl ℤ) x) := by
  rw [← scaled_timeRefl (eps sc N), phi_push]

theorem iota_theta (sc : Scale) (N : ℕ) (gd : DensityFn) (a : Alg) (x : Cfg ℤ) :
    iota sc N gd (ThetaPlane 2 0 a) x = starRingEnd ℂ (iota sc N gd a (pull (timeRefl ℤ) x)) := by
  induction a using alg_induction with
  | hb σ =>
    rw [thetaPlane_basisE, iota_basisE, iota_basisE, expPhi_neg]
    simp only [expPhi, phi_refl]
  | hadd a b ha hb =>
    rw [thetaPlane_add, iota_add, iota_add, Pi.add_apply, Pi.add_apply, map_add, ha, hb]
  | hsmul z a ha =>
    rw [thetaPlane_smul, iota_smul, iota_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul, map_mul, ha]

/-! ### The realised elements of `𝒜_+` depend on the closed upper half -/

theorem dependsUp_mono {P P' : Finset (Plaq ℤ)} {X X' : Finset (Site ℤ)} {F : Cfg ℤ → ℂ}
    (h : DependsUp P X F) (hP : P ⊆ P') (hX : X ⊆ X') (hP' : ∀ p ∈ P', 0 ≤ p.1 2)
    (hX' : ∀ x ∈ X', 0 ≤ x 2) : DependsUp P' X' F :=
  ⟨hP', hX', fun ω ω' h1 h2 => h.2.2 ω ω' (fun p hp => h1 p (hP hp)) fun x hx => h2 x (hX hx)⟩

theorem exists_dependsUp_op {F G : Cfg ℤ → ℂ} (hF : ∃ P X, DependsUp P X F)
    (hG : ∃ P X, DependsUp P X G) (op : ℂ → ℂ → ℂ) :
    ∃ P X, DependsUp P X fun x => op (F x) (G x) := by
  classical
  obtain ⟨P, X, h⟩ := hF
  obtain ⟨P', X', h'⟩ := hG
  refine ⟨P ∪ P', X ∪ X', fun p hp => ?_, fun x hx => ?_, fun ω ω' h1 h2 => ?_⟩
  · rcases Finset.mem_union.mp hp with hp | hp
    · exact h.1 p hp
    · exact h'.1 p hp
  · rcases Finset.mem_union.mp hx with hx | hx
    · exact h.2.1 x hx
    · exact h'.2.1 x hx
  · have e1 := h.2.2 ω ω' (fun p hp => h1 p (Finset.mem_union_left _ hp))
      fun x hx => h2 x (Finset.mem_union_left _ hx)
    have e2 := h'.2.2 ω ω' (fun p hp => h1 p (Finset.mem_union_right _ hp))
      fun x hx => h2 x (Finset.mem_union_right _ hx)
    simp only [e1, e2]

/-- The phase of a source above the plane depends on the cells of the closed upper half. -/
theorem exists_dependsUp_phi (sc : Scale) (N : ℕ) (gd : DensityFn) {σ : T}
    (hσ : SupportedAbove 2 0 σ) (f : ℝ → ℂ) : ∃ P X, DependsUp P X fun x => f (Phi sc N gd σ x) := by
  have hε : 0 < eps sc N := Work.PairNorm.eps_pos sc N
  refine ⟨(finite_face_support sc N σ).toFinset, (finite_site_support sc N σ).toFinset,
    fun p hp => ?_, fun z hz => ?_, fun ω ω' h1 h2 => ?_⟩
  · have hne : σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p) ≠ 0 := by simpa using hp
    have hpos : (0 : ℝ) < plaqCentre (eps sc N) p 2 := hσ.1 _ _ (subset_tsupport _ hne)
    have h3 : 0 < (p.1 2 : ℝ) + if (2 : Fin 3) = p.2.1.1 ∨ (2 : Fin 3) = p.2.1.2 then 1 / 2 else 0 :=
      (mul_pos_iff_of_pos_left hε).mp hpos
    have h4 : (-1 : ℝ) < p.1 2 := by
      split_ifs at h3 <;> linarith
    have h5 : (-1 : ℤ) < p.1 2 := by exact_mod_cast h4
    omega
  · have hne : σ.1.2 (sitePos (eps sc N) z) ≠ 0 := by simpa using hz
    have hpos : (0 : ℝ) < sitePos (eps sc N) z 2 := hσ.2 (subset_tsupport _ hne)
    have h3 : 0 < (z 2 : ℝ) := (mul_pos_iff_of_pos_left hε).mp hpos
    have h4 : 0 < z 2 := by exact_mod_cast h3
    omega
  · have hΦ : Phi sc N gd σ ω = Phi sc N gd σ ω' := by
      unfold Phi
      congr 1
      · congr 1
        refine tsum_congr fun p => ?_
        by_cases hp : σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p) = 0
        · rw [hp, zero_mul, zero_mul]
        · rw [h1 p (by simpa using hp)]
      · congr 1
        refine tsum_congr fun z => ?_
        by_cases hz : σ.1.2 (sitePos (eps sc N) z) = 0
        · rw [hz, zero_mul, zero_mul]
        · rw [h2 z (by simpa using hz)]
    simp only [hΦ]

theorem exists_dependsUp_iota (sc : Scale) (N : ℕ) (gd : DensityFn) {a : Alg}
    (ha : a ∈ AplusPlane 2 0) : ∃ P X, DependsUp P X (iota sc N gd a) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨σ, hσ, rfl⟩ := ha
    rw [iota_basisE]
    exact exists_dependsUp_phi sc N gd hσ fun r => Complex.exp (Complex.I * (r : ℂ))
  | zero =>
    refine ⟨∅, ∅, by simp, by simp, fun ω ω' _ _ => ?_⟩
    simp only [iota_apply, map_zero]
  | add a b _ _ ha hb =>
    rw [iota_add]
    exact exists_dependsUp_op ha hb (· + ·)
  | smul z a _ ha =>
    rw [iota_smul]
    exact exists_dependsUp_op ha ha fun u _ => z • u

variable {sc : Scale} {N0 : ℕ} {gd : DensityFn} {c : ℕ → Coeffs}
  {ω : ℕ → (Cfg ℤ → ℂ) → ℂ} {Nm : ℕ → ℕ} {S : Alg →ₗ[ℂ] ℂ}

/-- Reflection positivity at level `N`. -/
theorem rp_level {cN : Coeffs} {ωN : (Cfg ℤ → ℂ) → ℂ} (hω : IsLimitPoint cN ωN) (N : ℕ)
    {a : Alg} (ha : a ∈ AplusPlane 2 0) : 0 ≤ ωN (iota sc N gd (ThetaPlane 2 0 a * a)) := by
  obtain ⟨μ, hμ⟩ := exists_represents hω
  have hprob := hμ.prob
  obtain ⟨P, X, hup⟩ := exists_dependsUp_iota sc N gd ha
  have hbbl := bbl_iota sc N gd a
  obtain ⟨C, hC⟩ := hbbl.bounded
  have h2 : MemLp (iota sc N gd a) 2 μ :=
    MemLp.of_bound hbbl.measurable.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  have h := rp_state hω hμ hbbl.measurable h2 hup
  rw [hμ.eq _ (bbl_iota sc N gd _), iota_mul]
  simpa only [iota_theta] using h

theorem nonneg_refl (hω : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N))
    (hS : IsLimitFunctional sc N0 gd ω Nm S) {a : Alg} (ha : a ∈ AplusPlane 2 0) :
    0 ≤ S (ThetaPlane 2 0 a * a) :=
  ge_of_tendsto' (hS.tendsto _) fun m => rp_level (hω _ (hS.le m)) (Nm m) ha

theorem conj_refl (hω : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N))
    (hS : IsLimitFunctional sc N0 gd ω Nm S) (a : Alg) :
    S (ThetaPlane 2 0 a) = starRingEnd ℂ (S a) := by
  refine tendsto_nhds_unique (hS.tendsto _) ?_
  have h (m : ℕ) : ω (Nm m) (iota sc (Nm m) gd (ThetaPlane 2 0 a)) =
      starRingEnd ℂ (ω (Nm m) (iota sc (Nm m) gd a)) := by
    have hl := hω _ (hS.le m)
    obtain ⟨μ, hμ⟩ := exists_represents hl
    have hi := Work.latticeInvariant_of_isLimitPoint _ _ hl
    have hb := bbl_iota sc (Nm m) gd a
    rw [← hi (timeRefl ℤ) _ hb, hμ.eq _ (bbl_iota sc (Nm m) gd _), hμ.eq _
      ⟨hb.measurable.comp (TorusSymmetry.measurable_pull _), by
        obtain ⟨C, hC⟩ := hb.bounded
        exact ⟨C, fun x => hC _⟩, Work.isLocal_comp_pull hb.isLocal _⟩, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact iota_theta sc (Nm m) gd a x
  simp only [h]
  exact (Complex.continuous_conj.tendsto _).comp (hS.tendsto a)

theorem aplus_from {j : Fin 3} {r : ℝ} {a : Alg} (ha : a ∈ AplusPlane j r) :
    pushA (fromPlane j r) a ∈ AplusPlane 2 0 := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨σ, hσ, rfl⟩ := ha
    rw [pushA_basisE]
    exact Submodule.subset_span ⟨_, supportedAbove_from hσ, rfl⟩
  | zero =>
    have : pushA (fromPlane j r) 0 = 0 := by
      have h := pushA_smul (fromPlane j r) 0 0
      simpa using h
    rw [this]
    exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    rw [pushA_add]
    exact Submodule.add_mem _ ha hb
  | smul z a _ ha =>
    rw [pushA_smul]
    exact Submodule.smul_mem _ z ha

/-- [GG-OS] Proposition 9.9: positivity for the reflection in every plane. -/
theorem nonneg_plane (hω : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N))
    (hS : IsLimitFunctional sc N0 gd ω Nm S) (j : Fin 3) (r : ℝ) {a : Alg}
    (ha : a ∈ AplusPlane j r) : 0 ≤ S (ThetaPlane j r a * a) := by
  have h1 := nonneg_refl hω hS (aplus_from ha)
  rw [← (os1Cubic hω hS).invariant (toPlane j r), pushA_mul, ← thetaPlane_to, pushA_to_from] at h1
  exact h1

theorem conj_plane (hω : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N))
    (hS : IsLimitFunctional sc N0 gd ω Nm S) (j : Fin 3) (r : ℝ) (a : Alg) :
    S (ThetaPlane j r a) = starRingEnd ℂ (S a) := by
  have h1 := conj_refl hω hS (pushA (fromPlane j r) a)
  rw [← (os1Cubic hω hS).invariant (toPlane j r) (ThetaPlane 2 0 _), ← thetaPlane_to,
    pushA_to_from, (os1Cubic hω hS).invariant] at h1
  exact h1

theorem hermitian_plane (hω : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N))
    (hS : IsLimitFunctional sc N0 gd ω Nm S) (j : Fin 3) (r : ℝ) (a b : Alg) :
    S (ThetaPlane j r a * b) = starRingEnd ℂ (S (ThetaPlane j r b * a)) := by
  rw [← conj_plane hω hS j r, thetaPlane_mul, thetaPlane_thetaPlane, mul_comm]

end GGOS.OS

end

end

module

public import GGOS.OS.Work.Invariance

/-!
# Composition of motions, and the reflections in the planes `{x_j = c}`
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace GGOS.OS

/-- The composition `x ↦ g (h x)` of two motions. -/
def comp (g h : LatSym ℝ) : LatSym ℝ :=
  ⟨h.perm.trans g.perm, fun μ => h.sgn μ * g.sgn (h.perm μ), g.act h.shift⟩

theorem comp_invAct (g h : LatSym ℝ) (ξ : E3) : (comp g h).invAct ξ = h.invAct (g.invAct ξ) := by
  funext μ
  simp only [LatSym.invAct, comp, LatSym.act, Equiv.trans_apply, Equiv.symm_apply_apply]
  rcases Int.units_eq_one_or (g.sgn (h.perm μ)) with h1 | h1 <;> simp [h1] <;> ring

theorem pushT_comp (g h : LatSym ℝ) (σ : T) : pushT g (pushT h σ) = pushT (comp g h) σ := by
  refine T_ext (fun α β ξ => ?_) fun ξ => ?_
  · change _ * (_ * σ.1.1 _ _ (h.invAct (g.invAct ξ))) = _ * σ.1.1 _ _ ((comp g h).invAct ξ)
    rw [comp_invAct]
    simp only [comp, Equiv.symm_trans_apply, Equiv.apply_symm_apply, Units.val_mul, Int.cast_mul]
    ring
  · change σ.1.2 (h.invAct (g.invAct ξ)) = σ.1.2 ((comp g h).invAct ξ)
    rw [comp_invAct]

/-- The identity motion. -/
def idMotion : LatSym ℝ := ⟨Equiv.refl _, fun _ => 1, 0⟩

theorem pushT_id (σ : T) : pushT idMotion σ = σ := by
  have hinv (ξ : E3) : idMotion.invAct ξ = ξ := by
    funext i
    simp [LatSym.invAct, idMotion]
  refine T_ext (fun α β ξ => ?_) fun ξ => ?_
  · change _ * σ.1.1 _ _ (idMotion.invAct ξ) = _
    rw [hinv]
    simp [idMotion]
  · change σ.1.2 (idMotion.invAct ξ) = _
    rw [hinv]

/-- The motion that carries `{x_3 > 0}` onto `{x_j > c}`. -/
def toPlane (j : Fin 3) (c : ℝ) : LatSym ℝ := ⟨Equiv.swap 2 j, fun _ => 1, Pi.single j c⟩

/-- Its inverse. -/
def fromPlane (j : Fin 3) (c : ℝ) : LatSym ℝ := ⟨Equiv.swap 2 j, fun _ => 1, Pi.single 2 (-c)⟩

theorem motion_ext {g h : LatSym ℝ} (h1 : g.perm = h.perm) (h2 : g.sgn = h.sgn)
    (h3 : g.shift = h.shift) : g = h := by
  cases g
  cases h
  simp_all

theorem comp_to_from (j : Fin 3) (c : ℝ) : comp (toPlane j c) (fromPlane j c) = idMotion := by
  refine motion_ext ?_ ?_ ?_
  · ext i
    simp [comp, toPlane, fromPlane, idMotion]
  · funext i
    simp [comp, toPlane, fromPlane, idMotion]
  · funext i
    by_cases hi : i = j
    · subst hi
      simp [comp, toPlane, fromPlane, idMotion, LatSym.act]
    · have h : Equiv.swap 2 j i ≠ 2 := by
        intro h
        exact hi (by simpa using (Equiv.swap_apply_eq_iff.mp h))
      simp [comp, toPlane, fromPlane, idMotion, LatSym.act, Pi.single_eq_of_ne hi,
        Pi.single_eq_of_ne h]

theorem to_from (j : Fin 3) (c : ℝ) (σ : T) : pushT (toPlane j c) (pushT (fromPlane j c) σ) = σ := by
  rw [pushT_comp, comp_to_from, pushT_id]

theorem comp_refl_to (j : Fin 3) (c : ℝ) :
    comp (reflPlane j c) (toPlane j c) = comp (toPlane j c) (reflPlane 2 0) := by
  refine motion_ext ?_ ?_ ?_
  · ext i
    simp [comp, toPlane, reflPlane]
  · funext i
    by_cases hi : i = 2
    · subst hi
      simp [comp, toPlane, reflPlane]
    · have h : Equiv.swap 2 j i ≠ j := by
        intro h
        exact hi (by simpa using (Equiv.swap_apply_eq_iff.mp h))
      simp [comp, toPlane, reflPlane, Function.update_of_ne hi, Function.update_of_ne h]
  · funext i
    by_cases hi : i = j
    · subst hi
      simp [comp, toPlane, reflPlane, LatSym.act]
      ring
    · simp [comp, toPlane, reflPlane, LatSym.act, Pi.single_eq_of_ne hi]

theorem refl_to (j : Fin 3) (c : ℝ) (σ : T) :
    pushT (reflPlane j c) (pushT (toPlane j c) σ) =
      pushT (toPlane j c) (pushT (reflPlane 2 0) σ) := by
  rw [pushT_comp, pushT_comp, comp_refl_to]

theorem from_invAct (j : Fin 3) (c : ℝ) (ξ : E3) : (fromPlane j c).invAct ξ j = ξ 2 + c := by
  simp [LatSym.invAct, fromPlane]

/-- The inverse motion carries sources above `{x_j = c}` to sources above `{x_3 = 0}`. -/
theorem supportedAbove_from {j : Fin 3} {c : ℝ} {σ : T} (h : SupportedAbove j c σ) :
    SupportedAbove 2 0 (pushT (fromPlane j c) σ) := by
  have hcont : Continuous ((fromPlane j c).invAct : E3 → E3) :=
    (fromPlane j c).contDiff_invAct.continuous
  have hmem {ξ : E3} (hξ : (fromPlane j c).invAct ξ ∈ {ξ : E3 | c < ξ j}) : 0 < ξ 2 := by
    have : c < (fromPlane j c).invAct ξ j := hξ
    rw [from_invAct] at this
    linarith
  refine ⟨fun μ ν ξ hξ => ?_, fun ξ hξ => ?_⟩
  · refine hmem (h.1 ((fromPlane j c).perm.symm μ) ((fromPlane j c).perm.symm ν) ?_)
    have h1 : ξ ∈ tsupport fun ξ => σ.1.1 ((fromPlane j c).perm.symm μ)
        ((fromPlane j c).perm.symm ν) ((fromPlane j c).invAct ξ) :=
      tsupport_mul_subset_right hξ
    exact tsupport_comp_subset_preimage _ hcont h1
  · exact hmem (h.2 (tsupport_comp_subset_preimage _ hcont hξ))

theorem pushA_mul (g : LatSym ℝ) (a b : Alg) : pushA g (a * b) = pushA g a * pushA g b := by
  induction a using alg_induction with
  | hb σ =>
    induction b using alg_induction with
    | hb τ =>
      rw [basisE_mul, pushA_basisE, pushA_basisE, pushA_basisE, basisE_mul]
      congr 1
      exact map_add (pushL g) σ τ
    | hadd b b' hb hb' => rw [mul_add, pushA_add, pushA_add, mul_add, hb, hb']
    | hsmul z b hb => rw [mul_smul_comm, pushA_smul, pushA_smul, mul_smul_comm, hb]
  | hadd a a' ha ha' => rw [add_mul, pushA_add, pushA_add, add_mul, ha, ha']
  | hsmul z a ha => rw [smul_mul_assoc, pushA_smul, pushA_smul, smul_mul_assoc, ha]

theorem pushA_to_from (j : Fin 3) (c : ℝ) (a : Alg) :
    pushA (toPlane j c) (pushA (fromPlane j c) a) = a := by
  induction a using alg_induction with
  | hb σ => rw [pushA_basisE, pushA_basisE, to_from]
  | hadd a b ha hb => rw [pushA_add, pushA_add, ha, hb]
  | hsmul z a ha => rw [pushA_smul, pushA_smul, ha]

/-! ### The antilinear reflections -/

theorem thetaPlane_basisE (j : Fin 3) (c : ℝ) (σ : T) :
    ThetaPlane j c (basisE σ) = basisE (-pushT (reflPlane j c) σ) := by
  simp [ThetaPlane, basisE, AddMonoidAlgebra.mapDomain_single]

theorem thetaPlane_add (j : Fin 3) (c : ℝ) (a b : Alg) :
    ThetaPlane j c (a + b) = ThetaPlane j c a + ThetaPlane j c b := by
  unfold ThetaPlane
  rw [← AddMonoidAlgebra.mapDomain_add]
  congr 1
  ext σ
  simp

theorem thetaPlane_smul (j : Fin 3) (c : ℝ) (z : ℂ) (a : Alg) :
    ThetaPlane j c (z • a) = starRingEnd ℂ z • ThetaPlane j c a := by
  unfold ThetaPlane
  have h (b : Alg) : starRingEnd ℂ z • AddMonoidAlgebra.mapDomain
      (fun σ => -pushT (reflPlane j c) σ) b =
      AddMonoidAlgebra.mapDomain (fun σ => -pushT (reflPlane j c) σ) (starRingEnd ℂ z • b) :=
    ((AddMonoidAlgebra.mapDomainLinearMap ℂ ℂ
      (fun σ : T => -pushT (reflPlane j c) σ)).map_smul _ b).symm
  rw [h]
  congr 1
  ext σ
  simp

theorem thetaPlane_to (j : Fin 3) (c : ℝ) (a : Alg) :
    ThetaPlane j c (pushA (toPlane j c) a) = pushA (toPlane j c) (ThetaPlane 2 0 a) := by
  induction a using alg_induction with
  | hb σ => rw [pushA_basisE, thetaPlane_basisE, thetaPlane_basisE, pushA_basisE, refl_to, push_neg]
  | hadd a b ha hb => rw [pushA_add, thetaPlane_add, thetaPlane_add, pushA_add, ha, hb]
  | hsmul z a ha => rw [pushA_smul, thetaPlane_smul, thetaPlane_smul, pushA_smul, ha]

theorem thetaPlane_mul (j : Fin 3) (c : ℝ) (a b : Alg) :
    ThetaPlane j c (a * b) = ThetaPlane j c a * ThetaPlane j c b := by
  induction a using alg_induction with
  | hb σ =>
    induction b using alg_induction with
    | hb τ =>
      rw [basisE_mul, thetaPlane_basisE, thetaPlane_basisE, thetaPlane_basisE, basisE_mul]
      congr 1
      have h : pushT (reflPlane j c) (σ + τ) = pushT (reflPlane j c) σ + pushT (reflPlane j c) τ :=
        map_add (pushL (reflPlane j c)) σ τ
      rw [h]
      abel
    | hadd b b' hb hb' => rw [mul_add, thetaPlane_add, thetaPlane_add, mul_add, hb, hb']
    | hsmul z b hb => rw [mul_smul_comm, thetaPlane_smul, thetaPlane_smul, mul_smul_comm, hb]
  | hadd a a' ha ha' => rw [add_mul, thetaPlane_add, thetaPlane_add, add_mul, ha, ha']
  | hsmul z a ha => rw [smul_mul_assoc, thetaPlane_smul, thetaPlane_smul, smul_mul_assoc, ha]

theorem comp_refl_refl (j : Fin 3) (c : ℝ) :
    comp (reflPlane j c) (reflPlane j c) = idMotion := by
  refine motion_ext ?_ ?_ ?_
  · ext i
    simp [comp, reflPlane, idMotion]
  · funext i
    by_cases hi : i = j
    · subst hi
      simp [comp, reflPlane, idMotion]
    · simp [comp, reflPlane, idMotion]
  · funext i
    by_cases hi : i = j
    · subst hi
      simp [comp, reflPlane, idMotion, LatSym.act]
    · simp [comp, reflPlane, idMotion, LatSym.act, Pi.single_eq_of_ne hi]

theorem thetaPlane_thetaPlane (j : Fin 3) (c : ℝ) (a : Alg) :
    ThetaPlane j c (ThetaPlane j c a) = a := by
  induction a using alg_induction with
  | hb σ =>
    rw [thetaPlane_basisE, thetaPlane_basisE, push_neg, neg_neg, pushT_comp, comp_refl_refl,
      pushT_id]
  | hadd a b ha hb => rw [thetaPlane_add, thetaPlane_add, ha, hb]
  | hsmul z a ha =>
    rw [thetaPlane_smul, thetaPlane_smul, ha, Complex.conj_conj]

end GGOS.OS

end

end

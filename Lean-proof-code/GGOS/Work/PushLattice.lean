module

public import GGOS.Infra.Motion
public import GGOS.Frozen.Defs.ExpPhi
public import GGOS.Frozen.Defs.LatticeInvariant
public import GGOS.Frozen.Defs.Pull
public import GGOS.Frozen.Defs.Transl
public import GGOS.Work.TorusSymmetryBoundary
public import GGOS.Work.LimitObservables

/-!
# The lattice symmetries and the push-forward of test pairs

At spacing `ε` a lattice symmetry `g` of `ℤ³` is the motion `scaled ε g` of `ℝ³`, and the sampled
phase of the pushed test pair is the phase of the test pair on the pulled configuration.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace GGOS.OS

/-- The motion of `ℝ³` of a lattice symmetry at spacing `ε`. -/
def scaled (ε : ℝ) (g : LatSym ℤ) : LatSym ℝ :=
  ⟨g.perm, g.sgn, fun i => ε * (g.shift i : ℝ)⟩

theorem scaled_act_sitePos (ε : ℝ) (g : LatSym ℤ) (z : Site ℤ) :
    (scaled ε g).act (sitePos ε z) = sitePos ε (g.act z) := by
  funext α
  obtain ⟨i, rfl⟩ := g.perm.surjective α
  simp only [LatSym.act, scaled, sitePos, Equiv.symm_apply_apply, Int.cast_add, Int.cast_mul,
    Int.cast_id]
  ring

theorem corner_perm (g : LatSym ℤ) (μ i : Fin 3) :
    ((g.corner μ (g.perm i) : ℤ) : ℝ) = if g.sgn μ = 1 then 0 else if i = μ then -1 else 0 := by
  by_cases hs : g.sgn μ = 1
  · simp [LatSym.corner, hs]
  · by_cases hi : i = μ
    · subst hi
      simp [LatSym.corner, hs, unitVec]
    · simp [LatSym.corner, hs, unitVec, hi]

theorem dirImage_mem (e : Equiv.Perm (Fin 3)) (d : Dir2) (i : Fin 3) :
    (e i = (TorusSymmetry.dirImage e d).1.1 ∨ e i = (TorusSymmetry.dirImage e d).1.2) ↔
      (i = d.1.1 ∨ i = d.1.2) := by
  unfold TorusSymmetry.dirImage
  split_ifs with h
  · simp only [EmbeddingLike.apply_eq_iff_eq]
  · simp only [EmbeddingLike.apply_eq_iff_eq]
    exact or_comm

theorem scaled_act_plaqCentre (ε : ℝ) (g : LatSym ℤ) (p : Plaq ℤ) :
    (scaled ε g).act (plaqCentre ε p) = plaqCentre ε (TorusSymmetry.plaqEquiv g p) := by
  funext α
  obtain ⟨i, rfl⟩ := g.perm.surjective α
  obtain ⟨x, d⟩ := p
  have hd := dirImage_mem g.perm d i
  have hq : TorusSymmetry.plaqEquiv g (x, d) =
      (g.act x + (g.corner d.1.1 + g.corner d.1.2), TorusSymmetry.dirImage g.perm d) := rfl
  rw [hq]
  have hne : d.1.1 ≠ d.1.2 := d.2.ne
  simp only [LatSym.act, scaled, plaqCentre, Equiv.symm_apply_apply, Pi.add_apply, Int.cast_add,
    Int.cast_mul, Int.cast_id, corner_perm, hd]
  by_cases hi1 : i = d.1.1
  · have hi2 : i ≠ d.1.2 := fun h => hne (hi1.symm.trans h)
    have h2 : ((if g.sgn d.1.2 = 1 then 0 else if i = d.1.2 then -1 else 0 : ℝ)) = 0 := by
      simp [hi2]
    rw [h2, ← hi1]
    rcases Int.units_eq_one_or (g.sgn i) with h3 | h3 <;> simp [h3] <;> ring
  · by_cases hi2 : i = d.1.2
    · have h1 : ((if g.sgn d.1.1 = 1 then 0 else if i = d.1.1 then -1 else 0 : ℝ)) = 0 := by
        simp [hi1]
      rw [h1, ← hi2]
      rcases Int.units_eq_one_or (g.sgn i) with h3 | h3 <;> simp [h3] <;> ring
    · rcases Int.units_eq_one_or (g.sgn i) with h3 | h3 <;> simp [hi1, hi2, h3] <;> ring

theorem scaled_invAct_plaqCentre (ε : ℝ) (g : LatSym ℤ) (p : Plaq ℤ) :
    (scaled ε g).invAct (plaqCentre ε (TorusSymmetry.plaqEquiv g p)) = plaqCentre ε p := by
  rw [← scaled_act_plaqCentre, LatSym.invAct_act]

theorem scaled_invAct_sitePos (ε : ℝ) (g : LatSym ℤ) (z : Site ℤ) :
    (scaled ε g).invAct (sitePos ε (g.act z)) = sitePos ε z := by
  rw [← scaled_act_sitePos, LatSym.invAct_act]

/-- One term of the curvature sum, transported by `g`. -/
theorem push_face_term (ε : ℝ) (g : LatSym ℤ) (σ : T) (x : Plaq ℤ → ℝ) (p : Plaq ℤ) :
    (pushT (scaled ε g) σ).1.1 (TorusSymmetry.plaqEquiv g p).2.1.1
        (TorusSymmetry.plaqEquiv g p).2.1.2 (plaqCentre ε (TorusSymmetry.plaqEquiv g p)) *
        x (TorusSymmetry.plaqEquiv g p) =
      σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre ε p) * TorusSymmetry.faceField g x p := by
  rw [TorusSymmetry.faceField_apply]
  have hinv := scaled_invAct_plaqCentre ε g p
  obtain ⟨y, ⟨⟨μ, ν⟩, hμν⟩⟩ := p
  set q := TorusSymmetry.plaqEquiv g (y, ⟨(μ, ν), hμν⟩) with hq
  have hq2 : q.2 = TorusSymmetry.dirImage g.perm ⟨(μ, ν), hμν⟩ := rfl
  have hpush (α β : Fin 3) : (pushT (scaled ε g) σ).1.1 α β (plaqCentre ε q) =
      (((g.sgn (g.perm.symm α) * g.sgn (g.perm.symm β) : ℤˣ) : ℤ) : ℝ) *
        σ.1.1 (g.perm.symm α) (g.perm.symm β) (plaqCentre ε (y, ⟨(μ, ν), hμν⟩)) := by
    rw [← hinv]
    rfl
  rw [hpush, hq2]
  by_cases h : g.perm μ < g.perm ν
  · rcases Int.units_eq_one_or (g.sgn μ) with h1 | h1 <;>
      rcases Int.units_eq_one_or (g.sgn ν) with h2 | h2 <;>
      simp [TorusSymmetry.dirImage, TorusSymmetry.faceSign, TorusSymmetry.sign, h, h1, h2]
  · have hanti := σ.isTestPair.antisymm ν μ (plaqCentre ε (y, ⟨(μ, ν), hμν⟩))
    rcases Int.units_eq_one_or (g.sgn μ) with h1 | h1 <;>
      rcases Int.units_eq_one_or (g.sgn ν) with h2 | h2 <;>
      simp [TorusSymmetry.dirImage, TorusSymmetry.faceSign, TorusSymmetry.sign, h, h1, h2, hanti]

/-- The phase of a pushed test pair is the phase on the pulled configuration. -/
theorem phi_push (sc : Scale) (N : ℕ) (gd : DensityFn) (g : LatSym ℤ) (σ : T) (x : Cfg ℤ) :
    Phi sc N gd (pushT (scaled (eps sc N) g) σ) x = Phi sc N gd σ (pull g x) := by
  rw [TorusSymmetry.pull_eq_faceField]
  unfold Phi
  rw [← (TorusSymmetry.plaqEquiv g).tsum_eq (fun q : Plaq ℤ =>
      (pushT (scaled (eps sc N) g) σ).1.1 q.2.1.1 q.2.1.2 (plaqCentre (eps sc N) q) * x.1 q),
    ← (TorusSymmetry.siteEquiv g).tsum_eq (fun z : Site ℤ =>
      (pushT (scaled (eps sc N) g) σ).1.2 (sitePos (eps sc N) z) * gd.toFun (x.2 z))]
  congr 1
  · congr 1
    exact tsum_congr fun p => push_face_term (eps sc N) g σ x.1 p
  · congr 1
    refine tsum_congr fun z => ?_
    have : (pushT (scaled (eps sc N) g) σ).1.2 (sitePos (eps sc N) (TorusSymmetry.siteEquiv g z)) =
        σ.1.2 (sitePos (eps sc N) z) := by
      change σ.1.2 ((scaled (eps sc N) g).invAct (sitePos (eps sc N) (g.act z))) = _
      rw [scaled_invAct_sitePos]
    rw [this]
    rfl

theorem expPhi_push (sc : Scale) (N : ℕ) (gd : DensityFn) (g : LatSym ℤ) (σ : T) :
    expPhi sc N gd (pushT (scaled (eps sc N) g) σ) = expPhi sc N gd σ ∘ pull g := by
  funext x
  simp only [expPhi, Function.comp_apply, phi_push]

theorem state_expPhi_push (sc : Scale) (N : ℕ) (gd : DensityFn) {ω : (Cfg ℤ → ℂ) → ℂ}
    (hi : LatticeInvariant ω) (g : LatSym ℤ) (σ : T) :
    ω (expPhi sc N gd (pushT (scaled (eps sc N) g) σ)) = ω (expPhi sc N gd σ) := by
  rw [expPhi_push, hi _ _ (Work.Limit.bbl_exp sc N gd σ)]

theorem T_ext {σ τ : T} (h1 : ∀ μ ν x, σ.1.1 μ ν x = τ.1.1 μ ν x) (h2 : ∀ x, σ.1.2 x = τ.1.2 x) :
    σ = τ := by
  apply Subtype.ext
  refine Prod.ext ?_ (funext h2)
  funext μ ν x
  exact h1 μ ν x

/-- The push-forward as a linear map. -/
def pushL (g : LatSym ℝ) : T →ₗ[ℝ] T where
  toFun := pushT g
  map_add' _ _ := T_ext (fun _ _ _ => mul_add _ _ _) fun _ => rfl
  map_smul' _ _ := T_ext (fun _ _ _ => mul_left_comm _ _ _) fun _ => rfl

theorem pushL_apply (g : LatSym ℝ) (σ : T) : pushL g σ = pushT g σ := rfl

theorem push_sum_smul (g : LatSym ℝ) {ι : Type*} (s : Finset ι) (t : ι → ℝ) (σ : ι → T) :
    pushT g (∑ j ∈ s, t j • σ j) = ∑ j ∈ s, t j • pushT g (σ j) := by
  rw [← pushL_apply, map_sum]
  simp only [map_smul, pushL_apply]

theorem push_neg (g : LatSym ℝ) (σ : T) : pushT g (-σ) = -pushT g σ := map_neg (pushL g) σ

/-- The linear part of a motion. -/
def linPart (g : LatSym ℝ) : LatSym ℝ := ⟨g.perm, g.sgn, 0⟩

theorem push_eq_transl (g : LatSym ℝ) (σ : T) :
    pushT g σ = transl g.shift (pushT (linPart g) σ) := by
  have hinv (ξ : E3) : (linPart g).invAct (ξ - g.shift) = g.invAct ξ := by
    funext i
    simp [LatSym.invAct, linPart]
  refine T_ext (fun μ ν x => ?_) fun x => ?_
  · change _ = _ * σ.1.1 _ _ ((linPart g).invAct (x - g.shift))
    rw [hinv]
    rfl
  · change _ = σ.1.2 ((linPart g).invAct (x - g.shift))
    rw [hinv]
    rfl

/-- The lattice symmetry at level `N` with the linear part of `g` and the shift `j`. -/
def meshSym (g : LatSym ℝ) (j : Site ℤ) : LatSym ℤ := ⟨g.perm, g.sgn, j⟩

theorem push_scaled_meshSym (g : LatSym ℝ) (ε : ℝ) (j : Site ℤ) (σ : T) :
    pushT (scaled ε (meshSym g j)) σ = transl (sitePos ε j) (pushT (linPart g) σ) :=
  push_eq_transl (scaled ε (meshSym g j)) σ

end GGOS.OS

end

end

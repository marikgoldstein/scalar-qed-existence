module

public import GGOS.Frozen.Defs.BasisE
public import GGOS.Frozen.Defs.ExpPhi
public import GGOS.Frozen.Defs.Iota
public import GGOS.Frozen.Defs.Phi
public import GGOS.Infra.Alg
public import GGOS.Work.LimitObservables
public import GGOS.Work.PairNormBounds

/-!
# Linearity of the sampled phase, and the realisation `ι_N` as an algebra homomorphism
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace GGOS.OS

theorem finite_face_support (sc : Scale) (N : ℕ) (σ : T) :
    (Function.support fun p : Plaq ℤ =>
      σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p)).Finite :=
  (Work.PairNorm.finite_sample_supports sc N σ).2

theorem finite_site_support (sc : Scale) (N : ℕ) (σ : T) :
    (Function.support fun z : Site ℤ => σ.1.2 (sitePos (eps sc N) z)).Finite :=
  (Work.PairNorm.finite_sample_supports sc N σ).1

theorem summable_face (sc : Scale) (N : ℕ) (σ : T) (u : Plaq ℤ → ℝ) :
    Summable fun p : Plaq ℤ => σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p) * u p :=
  summable_of_hasFiniteSupport ((finite_face_support sc N σ).subset
    (Function.support_mul_subset_left _ _))

theorem summable_site (sc : Scale) (N : ℕ) (σ : T) (u : Site ℤ → ℝ) :
    Summable fun z : Site ℤ => σ.1.2 (sitePos (eps sc N) z) * u z :=
  summable_of_hasFiniteSupport ((finite_site_support sc N σ).subset
    (Function.support_mul_subset_left _ _))

theorem phi_add (sc : Scale) (N : ℕ) (gd : DensityFn) (σ τ : T) (x : Cfg ℤ) :
    Phi sc N gd (σ + τ) x = Phi sc N gd σ x + Phi sc N gd τ x := by
  have h1 := (summable_face sc N σ x.1).tsum_add (summable_face sc N τ x.1)
  have h2 := (summable_site sc N σ fun z => gd.toFun (x.2 z)).tsum_add
    (summable_site sc N τ fun z => gd.toFun (x.2 z))
  simp only [← add_mul] at h1 h2
  unfold Phi
  change _ * (∑' p : Plaq ℤ, (σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p) +
      τ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p)) * x.1 p) +
    _ * (∑' z : Site ℤ, (σ.1.2 (sitePos (eps sc N) z) + τ.1.2 (sitePos (eps sc N) z)) *
      gd.toFun (x.2 z)) = _
  rw [h1, h2]
  ring

theorem phi_smul (sc : Scale) (N : ℕ) (gd : DensityFn) (r : ℝ) (σ : T) (x : Cfg ℤ) :
    Phi sc N gd (r • σ) x = r * Phi sc N gd σ x := by
  have h1 : (∑' p : Plaq ℤ, (r • σ).1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p) * x.1 p) =
      r * ∑' p : Plaq ℤ, σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p) * x.1 p := by
    rw [← tsum_mul_left]
    refine tsum_congr fun p => ?_
    change r * _ * _ = _
    ring
  have h2 : (∑' z : Site ℤ, (r • σ).1.2 (sitePos (eps sc N) z) * gd.toFun (x.2 z)) =
      r * ∑' z : Site ℤ, σ.1.2 (sitePos (eps sc N) z) * gd.toFun (x.2 z) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun p => ?_
    change r * _ * _ = _
    ring
  unfold Phi
  rw [h1, h2]
  ring

/-- The phase at a configuration, as a linear form on the test pairs. -/
def phiL (sc : Scale) (N : ℕ) (gd : DensityFn) (x : Cfg ℤ) : T →ₗ[ℝ] ℝ where
  toFun σ := Phi sc N gd σ x
  map_add' σ τ := phi_add sc N gd σ τ x
  map_smul' r σ := phi_smul sc N gd r σ x

theorem phiL_apply (sc : Scale) (N : ℕ) (gd : DensityFn) (x : Cfg ℤ) (σ : T) :
    phiL sc N gd x σ = Phi sc N gd σ x := rfl

theorem phi_zero (sc : Scale) (N : ℕ) (gd : DensityFn) (x : Cfg ℤ) : Phi sc N gd 0 x = 0 :=
  map_zero (phiL sc N gd x)

theorem phi_neg (sc : Scale) (N : ℕ) (gd : DensityFn) (σ : T) (x : Cfg ℤ) :
    Phi sc N gd (-σ) x = -Phi sc N gd σ x :=
  map_neg (phiL sc N gd x) σ

theorem phi_sub (sc : Scale) (N : ℕ) (gd : DensityFn) (σ τ : T) (x : Cfg ℤ) :
    Phi sc N gd (σ - τ) x = Phi sc N gd σ x - Phi sc N gd τ x :=
  map_sub (phiL sc N gd x) σ τ

theorem phi_sum_smul (sc : Scale) (N : ℕ) (gd : DensityFn) {ι : Type*} (s : Finset ι)
    (t : ι → ℝ) (σ : ι → T) (x : Cfg ℤ) :
    Phi sc N gd (∑ j ∈ s, t j • σ j) x = ∑ j ∈ s, t j * Phi sc N gd (σ j) x := by
  rw [← phiL_apply, map_sum]
  simp only [map_smul, smul_eq_mul, phiL_apply]

theorem measurable_phi (sc : Scale) (N : ℕ) (gd : DensityFn) (σ : T) :
    Measurable (Phi sc N gd σ) := by
  unfold Phi
  refine (measurable_const.mul (.tsum fun q => measurable_const.mul
    ((measurable_pi_apply q).comp measurable_fst))).add (measurable_const.mul (.tsum fun z =>
      measurable_const.mul (gd.measurable.comp ((measurable_pi_apply z).comp measurable_snd))))

theorem expPhi_zero (sc : Scale) (N : ℕ) (gd : DensityFn) (x : Cfg ℤ) :
    expPhi sc N gd 0 x = 1 := by
  simp [expPhi, phi_zero]

theorem expPhi_add (sc : Scale) (N : ℕ) (gd : DensityFn) (σ τ : T) (x : Cfg ℤ) :
    expPhi sc N gd (σ + τ) x = expPhi sc N gd σ x * expPhi sc N gd τ x := by
  simp only [expPhi, phi_add]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem expPhi_neg (sc : Scale) (N : ℕ) (gd : DensityFn) (σ : T) (x : Cfg ℤ) :
    expPhi sc N gd (-σ) x = starRingEnd ℂ (expPhi sc N gd σ x) := by
  simp only [expPhi, phi_neg]
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem norm_expPhi (sc : Scale) (N : ℕ) (gd : DensityFn) (σ : T) (x : Cfg ℤ) :
    ‖expPhi sc N gd σ x‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal _

/-- The exponentials at a configuration, as a character of the test pairs. -/
def phaseHom (sc : Scale) (N : ℕ) (gd : DensityFn) (x : Cfg ℤ) : Multiplicative T →* ℂ where
  toFun σ := expPhi sc N gd σ.toAdd x
  map_one' := expPhi_zero sc N gd x
  map_mul' σ τ := expPhi_add sc N gd σ.toAdd τ.toAdd x

/-- Evaluation of the realisation at a configuration, as an algebra homomorphism. -/
def evalAt (sc : Scale) (N : ℕ) (gd : DensityFn) (x : Cfg ℤ) : Alg →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ T (phaseHom sc N gd x)

theorem evalAt_basisE (sc : Scale) (N : ℕ) (gd : DensityFn) (x : Cfg ℤ) (σ : T) :
    evalAt sc N gd x (basisE σ) = expPhi sc N gd σ x := by
  simp [evalAt, basisE, phaseHom]

theorem basisE_zero : basisE 0 = 1 := rfl

theorem basisE_mul (σ τ : T) : basisE σ * basisE τ = basisE (σ + τ) := by
  simp [basisE, AddMonoidAlgebra.single_mul_single]

/-- The algebra is spanned by the basis elements. -/
theorem alg_induction {p : Alg → Prop} (a : Alg) (hb : ∀ σ, p (basisE σ))
    (hadd : ∀ a b, p a → p b → p (a + b)) (hsmul : ∀ (z : ℂ) a, p a → p (z • a)) : p a := by
  induction a using AddMonoidAlgebra.induction_on with
  | of s => exact hb s
  | add x y hx hy => exact hadd x y hx hy
  | smul r x hx => exact hsmul r x hx

theorem iota_basisE (sc : Scale) (N : ℕ) (gd : DensityFn) (σ : T) :
    iota sc N gd (basisE σ) = expPhi sc N gd σ := by
  simp [iota, basisE]

theorem iota_add (sc : Scale) (N : ℕ) (gd : DensityFn) (a b : Alg) :
    iota sc N gd (a + b) = iota sc N gd a + iota sc N gd b := by
  classical
  unfold iota
  rw [AddMonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index' (fun σ => by simp) (fun σ z w => by rw [add_smul])

theorem iota_smul (sc : Scale) (N : ℕ) (gd : DensityFn) (z : ℂ) (a : Alg) :
    iota sc N gd (z • a) = z • iota sc N gd a := by
  classical
  unfold iota
  rw [AddMonoidAlgebra.coeff_smul, Finsupp.sum_smul_index' (fun σ => by simp), Finsupp.smul_sum]
  simp only [smul_eq_mul, mul_smul]

theorem iota_apply (sc : Scale) (N : ℕ) (gd : DensityFn) (a : Alg) (x : Cfg ℤ) :
    iota sc N gd a x = evalAt sc N gd x a := by
  induction a using alg_induction with
  | hb σ => rw [iota_basisE, evalAt_basisE]
  | hadd a b ha hb => rw [iota_add, map_add, Pi.add_apply, ha, hb]
  | hsmul z a ha => rw [iota_smul, map_smul, Pi.smul_apply, ha]

theorem iota_mul (sc : Scale) (N : ℕ) (gd : DensityFn) (a b : Alg) :
    iota sc N gd (a * b) = fun x => iota sc N gd a x * iota sc N gd b x := by
  funext x
  simp only [iota_apply, map_mul]

theorem bbl_iota (sc : Scale) (N : ℕ) (gd : DensityFn) (a : Alg) : IsBBL (iota sc N gd a) := by
  induction a using alg_induction with
  | hb σ => rw [iota_basisE]; exact Work.Limit.bbl_exp sc N gd σ
  | hadd a b ha hb => rw [iota_add]; exact Work.Limit.bbl_add ha hb
  | hsmul z a ha => rw [iota_smul]; exact Work.Limit.bbl_smul z ha

end GGOS.OS

end

end

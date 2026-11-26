module

public import GGOS.OS.Schwinger
public import GGOS.OS.Work.Law

/-!
# The norm `‖·‖` is bounded by the weighted sup norm ([GG-OS] Lemma 9.1)
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace GGOS.OS

/-! ### The weighted sup norm -/

/-- The weight `(1 + |x|²)²`. -/
def wgt (x : E3) : ℝ := (1 + ∑ i, x i ^ 2) ^ 2

theorem wgt_pos (x : E3) : 0 < wgt x := by
  unfold wgt
  positivity

theorem continuous_wgt : Continuous wgt := by
  unfold wgt
  fun_prop

/-- The function whose supremum is the weighted norm. -/
def wfun (σ : T) (x : E3) : ℝ := wgt x *
  max (Finset.univ.sup' Finset.univ_nonempty fun q : Fin 3 × Fin 3 => |σ.1.1 q.1 q.2 x|) |σ.1.2 x|

theorem weightNorm_eq (σ : T) : weightNorm σ = ⨆ x, wfun σ x := rfl

theorem bdd_wfun (σ : T) : BddAbove (Set.range (wfun σ)) := by
  have hf (μ ν : Fin 3) : ∃ C, ∀ x, ‖wgt x * σ.1.1 μ ν x‖ ≤ C :=
    (σ.isTestPair.compact_f μ ν).mul_left.exists_bound_of_continuous
      (continuous_wgt.mul (σ.isTestPair.smooth_f μ ν).continuous)
  obtain ⟨Ch, hCh⟩ := (σ.isTestPair.compact_h.mul_left (f := wgt)).exists_bound_of_continuous
    (continuous_wgt.mul σ.isTestPair.smooth_h.continuous)
  choose Cf hCf using hf
  have hCf0 (μ ν : Fin 3) : 0 ≤ Cf μ ν := (norm_nonneg _).trans (hCf μ ν 0)
  have hCh0 : 0 ≤ Ch := (norm_nonneg _).trans (hCh 0)
  refine ⟨(∑ q : Fin 3 × Fin 3, Cf q.1 q.2) + Ch, ?_⟩
  rintro _ ⟨x, rfl⟩
  unfold wfun
  rw [mul_max_of_nonneg _ _ (wgt_pos x).le]
  refine max_le ?_ ?_
  · obtain ⟨q, -, hq⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty
      fun q : Fin 3 × Fin 3 => |σ.1.1 q.1 q.2 x|
    rw [hq]
    have h1 := hCf q.1 q.2 x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (wgt_pos x)] at h1
    have h2 : Cf q.1 q.2 ≤ ∑ q : Fin 3 × Fin 3, Cf q.1 q.2 :=
      Finset.single_le_sum (f := fun q : Fin 3 × Fin 3 => Cf q.1 q.2) (fun q _ => hCf0 q.1 q.2)
        (Finset.mem_univ q)
    linarith
  · have h1 := hCh x
    rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (wgt_pos x)] at h1
    have h2 : 0 ≤ ∑ q : Fin 3 × Fin 3, Cf q.1 q.2 := Finset.sum_nonneg fun q _ => hCf0 q.1 q.2
    linarith

theorem weightNorm_nonneg (σ : T) : 0 ≤ weightNorm σ := by
  refine Real.iSup_nonneg fun x => mul_nonneg (wgt_pos x).le ?_
  exact le_max_of_le_right (abs_nonneg _)

theorem abs_f_le (σ : T) (μ ν : Fin 3) (x : E3) : |σ.1.1 μ ν x| ≤ weightNorm σ / wgt x := by
  rw [le_div_iff₀ (wgt_pos x), mul_comm, weightNorm_eq]
  refine le_trans ?_ (le_ciSup (bdd_wfun σ) x)
  refine mul_le_mul_of_nonneg_left ?_ (wgt_pos x).le
  exact (Finset.le_sup' (fun q : Fin 3 × Fin 3 => |σ.1.1 q.1 q.2 x|)
    (Finset.mem_univ (μ, ν))).trans (le_max_left _ _)

theorem abs_h_le (σ : T) (x : E3) : |σ.1.2 x| ≤ weightNorm σ / wgt x := by
  rw [le_div_iff₀ (wgt_pos x), mul_comm, weightNorm_eq]
  refine le_trans ?_ (le_ciSup (bdd_wfun σ) x)
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) (wgt_pos x).le

/-! ### Riemann sums of the inverse weight -/

/-- The integrable majorant, in the sup norm of `ℝ³`. -/
def maj (y : E3) : ℝ := (1 + ‖y‖ ^ 2) ^ (-(4 : ℝ) / 2)

theorem maj_eq (y : E3) : maj y = ((1 + ‖y‖ ^ 2) ^ 2)⁻¹ := by
  unfold maj
  have h : 0 < 1 + ‖y‖ ^ 2 := by positivity
  rw [show (-(4 : ℝ) / 2) = -(2 : ℕ) by norm_num, Real.rpow_neg h.le, Real.rpow_natCast]

theorem maj_pos (y : E3) : 0 < maj y := by
  rw [maj_eq]
  positivity

theorem integrable_maj : Integrable maj := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := E3) (μ := volume) (r := 4) (by simp; norm_num)
  exact h

theorem inv_wgt_le (x : E3) : (wgt x)⁻¹ ≤ ((1 + ‖x‖ ^ 2) ^ 2)⁻¹ := by
  refine inv_anti₀ (by positivity) ?_
  unfold wgt
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  have : ‖x‖ ^ 2 ≤ ∑ i, x i ^ 2 := by
    have h1 : ‖x‖ ≤ Real.sqrt (∑ i, x i ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
      rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun i => x i ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i))
    have h2 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc ‖x‖ ^ 2 ≤ Real.sqrt (∑ i, x i ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = ∑ i, x i ^ 2 := Real.sq_sqrt h2
  linarith

/-- The half-open cube of side `ε` at `x`. -/
def cube (ε : ℝ) (x : E3) : Set E3 := Set.univ.pi fun i => Set.Ico (x i) (x i + ε)

theorem measurableSet_cube (ε : ℝ) (x : E3) : MeasurableSet (cube ε x) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem volume_cube {ε : ℝ} (x : E3) : volume (cube ε x) = ENNReal.ofReal ε ^ 3 := by
  unfold cube
  rw [Real.volume_pi_Ico]
  simp

/-- The lattice point of index `z` with offset `v`. -/
def latPoint (ε : ℝ) (v : E3) (z : Site ℤ) : E3 := fun i => ε * ((z i : ℝ) + v i)

theorem disjoint_cubes {ε : ℝ} (hε : 0 < ε) (v : E3) {z z' : Site ℤ} (h : z ≠ z') :
    Disjoint (cube ε (latPoint ε v z)) (cube ε (latPoint ε v z')) := by
  rw [Set.disjoint_left]
  intro y hy hy'
  apply h
  funext i
  have h1 := Set.mem_Ico.mp (Set.mem_univ_pi.mp hy i)
  have h2 := Set.mem_Ico.mp (Set.mem_univ_pi.mp hy' i)
  simp only [latPoint] at h1 h2
  have h3 : ε * ((z i : ℝ) - z' i) < ε * 1 := by nlinarith [h1.1, h2.2]
  have h4 : ε * ((z' i : ℝ) - z i) < ε * 1 := by nlinarith [h2.1, h1.2]
  have h5 := lt_of_mul_lt_mul_left h3 hε.le
  have h6 := lt_of_mul_lt_mul_left h4 hε.le
  have h7 : z i - z' i < 1 := by exact_mod_cast h5
  have h8 : z' i - z i < 1 := by exact_mod_cast h6
  omega

/-- The constant of the Riemann sums. -/
def riemannConst (a : ℝ) : ℝ := (2 + 2 * a ^ 2) ^ 2 * ∫ y, maj y

theorem riemannConst_nonneg (a : ℝ) : 0 ≤ riemannConst a :=
  mul_nonneg (by positivity) (integral_nonneg fun y => (maj_pos y).le)

theorem one_cube {ε a : ℝ} (hε : 0 < ε) (hεa : ε ≤ a) (x : E3) :
    ε ^ 3 * ((1 + ‖x‖ ^ 2) ^ 2)⁻¹ ≤ (2 + 2 * a ^ 2) ^ 2 * ∫ y in cube ε x, maj y := by
  have hc (y : E3) (hy : y ∈ cube ε x) :
      ((1 + ‖x‖ ^ 2) ^ 2)⁻¹ * ((2 + 2 * a ^ 2) ^ 2)⁻¹ ≤ maj y := by
    rw [maj_eq, ← mul_inv, ← mul_pow]
    refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) ?_ 2)
    have hn : ‖y - x‖ ≤ a := by
      refine (pi_norm_le_iff_of_nonneg (hε.le.trans hεa)).mpr fun i => ?_
      have h1 := Set.mem_Ico.mp (Set.mem_univ_pi.mp hy i)
      rw [Real.norm_eq_abs, Pi.sub_apply, abs_of_nonneg (by linarith [h1.1])]
      linarith [h1.2]
    have hy2 : ‖y‖ ≤ ‖x‖ + a := by
      have := norm_add_le x (y - x)
      rw [add_sub_cancel] at this
      linarith
    have h3 : ‖y‖ ^ 2 ≤ (‖x‖ + a) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy2 2
    nlinarith [sq_nonneg (‖x‖ - a), sq_nonneg (‖x‖ * a)]
  have hfin : volume (cube ε x) ≠ ⊤ := by
    rw [volume_cube]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hle : ∫ _y in cube ε x, ((1 + ‖x‖ ^ 2) ^ 2)⁻¹ * ((2 + 2 * a ^ 2) ^ 2)⁻¹ ≤
      ∫ y in cube ε x, maj y :=
    setIntegral_mono_on (integrableOn_const hfin) integrable_maj.integrableOn
      (measurableSet_cube ε x) hc
  rw [setIntegral_const, measureReal_def, volume_cube, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hε.le, smul_eq_mul] at hle
  have hpos : (0 : ℝ) < (2 + 2 * a ^ 2) ^ 2 := by positivity
  calc ε ^ 3 * ((1 + ‖x‖ ^ 2) ^ 2)⁻¹
      = (2 + 2 * a ^ 2) ^ 2 * (ε ^ 3 * (((1 + ‖x‖ ^ 2) ^ 2)⁻¹ * ((2 + 2 * a ^ 2) ^ 2)⁻¹)) := by
        field_simp
    _ ≤ (2 + 2 * a ^ 2) ^ 2 * ∫ y in cube ε x, maj y := mul_le_mul_of_nonneg_left hle hpos.le

/-- [GG-OS] Lemma 9.1: the Riemann sums of the inverse weight are bounded uniformly in the
spacing. -/
theorem riemann_sum_le {ε a : ℝ} (hε : 0 < ε) (hεa : ε ≤ a) (v : E3) (F : Finset (Site ℤ)) :
    ∑ z ∈ F, ε ^ 3 * (wgt (latPoint ε v z))⁻¹ ≤ riemannConst a := by
  calc ∑ z ∈ F, ε ^ 3 * (wgt (latPoint ε v z))⁻¹
      ≤ ∑ z ∈ F, (2 + 2 * a ^ 2) ^ 2 * ∫ y in cube ε (latPoint ε v z), maj y :=
        Finset.sum_le_sum fun z _ => (mul_le_mul_of_nonneg_left (inv_wgt_le _)
          (by positivity)).trans (one_cube hε hεa _)
    _ = (2 + 2 * a ^ 2) ^ 2 * ∫ y in ⋃ z ∈ F, cube ε (latPoint ε v z), maj y := by
        rw [← Finset.mul_sum, integral_biUnion_finset F (fun z _ => measurableSet_cube ε _)
          (fun z _ z' _ h => disjoint_cubes hε v h) fun z _ => integrable_maj.integrableOn]
    _ ≤ (2 + 2 * a ^ 2) ^ 2 * ∫ y, maj y := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact setIntegral_le_integral integrable_maj (Eventually.of_forall fun y => (maj_pos y).le)
    _ = riemannConst a := rfl

theorem eps_le (sc : Scale) (N : ℕ) : eps sc N ≤ sc.a0 :=
  div_le_self sc.a0_pos.le (one_le_pow₀ (by norm_num))

theorem sitePos_eq (ε : ℝ) (z : Site ℤ) : sitePos ε z = latPoint ε 0 z := by
  funext i
  simp [sitePos, latPoint]

theorem plaqCentre_eq (ε : ℝ) (z : Site ℤ) (d : Dir2) : plaqCentre ε (z, d) =
    latPoint ε (fun i => if i = d.1.1 ∨ i = d.1.2 then 1 / 2 else 0) z := rfl

theorem enorm_le_weightNorm (sc : Scale) (N0 : ℕ) (σ : T) :
    Enorm sc N0 σ ≤ riemannConst sc.a0 * weightNorm σ := by
  have : Nonempty {N : ℕ // N0 ≤ N} := ⟨⟨N0, le_rfl⟩⟩
  refine ciSup_le fun N => ?_
  have hε : 0 < eps sc N := Work.PairNorm.eps_pos sc N
  let F := (finite_site_support sc N σ).toFinset
  have hts : ∑' z : Site ℤ, |σ.1.2 (sitePos (eps sc N) z)| =
      ∑ z ∈ F, |σ.1.2 (sitePos (eps sc N) z)| :=
    tsum_eq_sum fun z hz => by
      have : σ.1.2 (sitePos (eps sc N) z) = 0 := by
        by_contra h
        exact hz (by simpa [F] using h)
      rw [this, abs_zero]
  rw [hts, Finset.mul_sum]
  calc ∑ z ∈ F, eps sc N ^ 3 * |σ.1.2 (sitePos (eps sc N) z)|
      ≤ ∑ z ∈ F, (eps sc N ^ 3 * (wgt (latPoint (eps sc N) 0 z))⁻¹) * weightNorm σ := by
        refine Finset.sum_le_sum fun z _ => ?_
        have h := abs_h_le σ (sitePos (eps sc N) z)
        rw [sitePos_eq] at h ⊢
        rw [mul_assoc, ← div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left h (by positivity)
    _ = (∑ z ∈ F, eps sc N ^ 3 * (wgt (latPoint (eps sc N) 0 z))⁻¹) * weightNorm σ :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ riemannConst sc.a0 * weightNorm σ :=
        mul_le_mul_of_nonneg_right (riemann_sum_le hε (eps_le sc N) 0 F) (weightNorm_nonneg σ)

theorem rnorm_le_weightNorm (sc : Scale) (N0 : ℕ) (σ : T) :
    Rnorm sc N0 σ ≤ Real.sqrt (3 * riemannConst sc.a0) * weightNorm σ := by
  have : Nonempty {N : ℕ // N0 ≤ N} := ⟨⟨N0, le_rfl⟩⟩
  refine ciSup_le fun N => ?_
  have hε : 0 < eps sc N := Work.PairNorm.eps_pos sc N
  have hW := weightNorm_nonneg σ
  rw [← Real.sqrt_sq hW, ← Real.sqrt_mul (mul_nonneg (by norm_num) (riemannConst_nonneg _))]
  refine Real.sqrt_le_sqrt ?_
  let G : Finset (Site ℤ) := (finite_face_support sc N σ).toFinset.image fun p => p.1
  have hts : ∑' p : Plaq ℤ, (σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p)) ^ 2 =
      ∑ p ∈ G ×ˢ (Finset.univ : Finset Dir2),
        (σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p)) ^ 2 :=
    tsum_eq_sum fun p hp => by
      have : σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p) = 0 := by
        by_contra h
        refine hp (Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p, ?_, rfl⟩, Finset.mem_univ _⟩)
        simpa using h
      rw [this]
      norm_num
  rw [hts, Finset.sum_product_right, Finset.mul_sum]
  have hone (d : Dir2) : eps sc N ^ 3 * ∑ z ∈ G,
      (σ.1.1 d.1.1 d.1.2 (plaqCentre (eps sc N) (z, d))) ^ 2 ≤
      riemannConst sc.a0 * weightNorm σ ^ 2 := by
    set v : E3 := fun i => if i = d.1.1 ∨ i = d.1.2 then 1 / 2 else 0 with hv
    rw [Finset.mul_sum]
    calc ∑ z ∈ G, eps sc N ^ 3 * (σ.1.1 d.1.1 d.1.2 (plaqCentre (eps sc N) (z, d))) ^ 2
        ≤ ∑ z ∈ G, (eps sc N ^ 3 * (wgt (latPoint (eps sc N) v z))⁻¹) * weightNorm σ ^ 2 := by
          refine Finset.sum_le_sum fun z _ => ?_
          have h := abs_f_le σ d.1.1 d.1.2 (latPoint (eps sc N) v z)
          rw [plaqCentre_eq, mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hw := wgt_pos (latPoint (eps sc N) v z)
          have h1 : (σ.1.1 d.1.1 d.1.2 (latPoint (eps sc N) v z)) ^ 2 ≤
              (weightNorm σ / wgt (latPoint (eps sc N) v z)) ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) h 2
          refine h1.trans ?_
          have h2 : 1 ≤ wgt (latPoint (eps sc N) v z) := by
            unfold wgt
            have : 0 ≤ ∑ i, latPoint (eps sc N) v z i ^ 2 :=
              Finset.sum_nonneg fun _ _ => sq_nonneg _
            exact one_le_pow₀ (by linarith)
          have h3 : ((wgt (latPoint (eps sc N) v z)) ^ 2)⁻¹ ≤ (wgt (latPoint (eps sc N) v z))⁻¹ := by
            refine inv_anti₀ hw ?_
            nlinarith
          rw [div_pow, div_eq_inv_mul]
          exact mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
      _ = (∑ z ∈ G, eps sc N ^ 3 * (wgt (latPoint (eps sc N) v z))⁻¹) * weightNorm σ ^ 2 :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ riemannConst sc.a0 * weightNorm σ ^ 2 :=
          mul_le_mul_of_nonneg_right (riemann_sum_le hε (eps_le sc N) v G) (sq_nonneg _)
  calc ∑ d : Dir2, eps sc N ^ 3 * ∑ z ∈ G, (σ.1.1 d.1.1 d.1.2 (plaqCentre (eps sc N) (z, d))) ^ 2
      ≤ ∑ _d : Dir2, riemannConst sc.a0 * weightNorm σ ^ 2 := Finset.sum_le_sum fun d _ => hone d
    _ = 3 * riemannConst sc.a0 * weightNorm σ ^ 2 := by
        have hcard : Fintype.card Dir2 = 3 := by decide
        rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
        push_cast
        ring

/-- The constant between the two norms. -/
def normConst (sc : Scale) (gd : DensityFn) : ℝ :=
  Real.sqrt (3 * riemannConst sc.a0) + supNorm gd * riemannConst sc.a0

theorem normConst_nonneg (sc : Scale) (gd : DensityFn) : 0 ≤ normConst sc gd :=
  add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (supNorm_nonneg gd) (riemannConst_nonneg _))

/-- [GG-OS] Lemma 9.1: `‖σ‖ ≤ C ‖σ‖_w`, with `C` depending on `a_0` and `g_d` only. -/
theorem pairNorm_le_weightNorm (sc : Scale) (N0 : ℕ) (gd : DensityFn) (σ : T) :
    pairNorm sc N0 gd σ ≤ normConst sc gd * weightNorm σ := by
  unfold pairNorm normConst
  have h1 := rnorm_le_weightNorm sc N0 σ
  have h2 := mul_le_mul_of_nonneg_left (enorm_le_weightNorm sc N0 σ) (supNorm_nonneg gd)
  nlinarith

end GGOS.OS

end

end

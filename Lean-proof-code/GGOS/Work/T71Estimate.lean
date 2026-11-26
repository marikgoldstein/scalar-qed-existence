module

public import Mathlib
public import GGOS.Frozen.Defs.IsLimitPoint
public import GGOS.Frozen.Defs.LatticeInvariant
public import GGOS.Frozen.Defs.Iota
public import GGOS.Frozen.Defs.TauA
public import GGOS.Frozen.Defs.Phi
public import GGOS.Frozen.Defs.PairNorm
public import GGOS.Infra.IsState
public import GGOS.Frozen.TorusEstimate
public import GGOS.Frozen.PairNorm
public import GGOS.Work.TorusMass
public import GGOS.Work.PairNormBounds

public section

open MeasureTheory Filter Topology

/-!
# The truncated estimate for limit points ([GG-OS] Proposition 4.2, second clause)
-/

namespace GGOS.Work

private lemma min_abs_add_le (x y : ℝ) : min |x + y| 2 ≤ min |x| 2 + |y| := by
  rcases le_total |x| 2 with hx | hx
  · rw [min_eq_left hx]
    exact (min_le_left _ _).trans (abs_add_le x y)
  · rw [min_eq_right hx]
    exact (min_le_right _ _).trans (le_add_of_nonneg_right (abs_nonneg y))

private noncomputable def curvPair (σ : T) : T :=
  ⟨(σ.1.1, (0 : E3 → ℝ)), {
    antisymm := σ.isTestPair.antisymm
    smooth_f := σ.isTestPair.smooth_f
    compact_f := σ.isTestPair.compact_f
    smooth_h := contDiff_const
    compact_h := HasCompactSupport.zero
  }⟩

private noncomputable def densityPart (sc : Scale) (N : ℕ) (gd : DensityFn) (σ : T)
    (x : Cfg ℤ) : ℝ :=
  eps sc N ^ 3 * ∑' z : Site ℤ, σ.1.2 (sitePos (eps sc N) z) * gd.toFun (x.2 z)

private lemma phi_curvPair (sc : Scale) (N : ℕ) (gd : DensityFn) (σ : T) (x : Cfg ℤ) :
    Phi sc N gd (curvPair σ) x =
      eps sc N ^ (3 / 2 : ℝ) *
        ∑' p : Plaq ℤ, σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p) * x.1 p := by
  simp only [Phi, curvPair, Pi.zero_apply, zero_mul, tsum_zero, mul_zero, add_zero]

private lemma phi_eq_curvPair_add_densityPart (sc : Scale) (N : ℕ) (gd : DensityFn) (σ : T)
    (x : Cfg ℤ) :
    Phi sc N gd σ x = Phi sc N gd (curvPair σ) x + densityPart sc N gd σ x := by
  rw [phi_curvPair]
  rfl

private lemma pairNorm_curvPair_le (sc : Scale) (N0 : ℕ) (gd : DensityFn) (σ : T) :
    pairNorm sc N0 gd (curvPair σ) ≤ Rnorm sc N0 σ := by
  haveI : Nonempty {M : ℕ // N0 ≤ M} := ⟨⟨N0, le_rfl⟩⟩
  have hsup : 0 ≤ supNorm gd := by
    obtain ⟨C, hC⟩ := gd.bdd
    have hb : BddAbove (Set.range fun r : ℝ => |gd.toFun r|) :=
      ⟨C, Set.forall_mem_range.mpr hC⟩
    exact (abs_nonneg _).trans (le_ciSup hb (0 : ℝ))
  have hE : Enorm sc N0 (curvPair σ) ≤ 0 := by
    unfold Enorm
    refine ciSup_le fun M => ?_
    simp only [curvPair, Pi.zero_apply, abs_zero, tsum_zero, mul_zero, le_rfl]
  have hR : Rnorm sc N0 (curvPair σ) = Rnorm sc N0 σ := rfl
  unfold pairNorm
  rw [hR]
  have hmul : supNorm gd * Enorm sc N0 (curvPair σ) ≤ supNorm gd * 0 :=
    mul_le_mul_of_nonneg_left hE hsup
  linarith [hmul]

private lemma abs_densityPart_le (sc : Scale) (N0 N : ℕ) (hN : N0 ≤ N) (gd : DensityFn) (σ : T)
    (x : Cfg ℤ) :
    |densityPart sc N gd σ x| ≤ supNorm gd * Enorm sc N0 σ := by
  classical
  let ε : ℝ := eps sc N
  have hε : 0 < ε := PairNorm.eps_pos sc N
  let hz : Site ℤ → ℝ := PairNorm.siteSample ε σ
  have hfin := (PairNorm.finite_sample_supports sc N σ).1
  let S : Finset (Site ℤ) := hfin.toFinset
  have hhz_out : ∀ z ∉ S, hz z = 0 := by
    intro z hzs
    by_contra hne
    exact hzs (hfin.mem_toFinset.mpr hne)
  have htsum_val :
      (∑' z : Site ℤ, hz z * gd.toFun (x.2 z)) = ∑ z ∈ S, hz z * gd.toFun (x.2 z) := by
    refine (hasSum_sum_of_ne_finset_zero fun z hzs => ?_).tsum_eq
    rw [hhz_out z hzs, zero_mul]
  have htsum_abs : (∑' z : Site ℤ, |hz z|) = ∑ z ∈ S, |hz z| := by
    refine (hasSum_sum_of_ne_finset_zero fun z hzs => ?_).tsum_eq
    rw [hhz_out z hzs, abs_zero]
  obtain ⟨Cgd, hCgd⟩ := gd.bdd
  have hbdd_gd : BddAbove (Set.range fun r : ℝ => |gd.toFun r|) :=
    ⟨Cgd, Set.forall_mem_range.mpr hCgd⟩
  have hgd_le : ∀ r : ℝ, |gd.toFun r| ≤ supNorm gd := fun r => le_ciSup hbdd_gd r
  have hsup_nonneg : 0 ≤ supNorm gd := (abs_nonneg _).trans (hgd_le 0)
  have hbddE : BddAbove (Set.range fun M : {M : ℕ // N0 ≤ M} =>
      eps sc M ^ 3 * ∑' z : Site ℤ, |σ.1.2 (sitePos (eps sc M) z)|) :=
    (GGOS.pairNorm_finite_seminorm_admissible sc N0 gd).2.1 σ
  have heN_le : ε ^ 3 * (∑' z : Site ℤ, |hz z|) ≤ Enorm sc N0 σ :=
    le_ciSup hbddE ⟨N, hN⟩
  change |ε ^ 3 * ∑' z : Site ℤ, hz z * gd.toFun (x.2 z)| ≤ _
  rw [htsum_val]
  calc |ε ^ 3 * ∑ z ∈ S, hz z * gd.toFun (x.2 z)|
      = ε ^ 3 * |∑ z ∈ S, hz z * gd.toFun (x.2 z)| := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg hε.le 3)]
    _ ≤ ε ^ 3 * ∑ z ∈ S, |hz z * gd.toFun (x.2 z)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ S) (pow_nonneg hε.le 3)
    _ ≤ ε ^ 3 * ∑ z ∈ S, |hz z| * supNorm gd := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => ?_) (pow_nonneg hε.le 3)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hgd_le _) (abs_nonneg _)
    _ = supNorm gd * (ε ^ 3 * ∑ z ∈ S, |hz z|) := by
        rw [← Finset.sum_mul]
        ring
    _ = supNorm gd * (ε ^ 3 * ∑' z : Site ℤ, |hz z|) := by
        rw [htsum_abs]
    _ ≤ supNorm gd * Enorm sc N0 σ :=
        mul_le_mul_of_nonneg_left heN_le hsup_nonneg

private lemma measurable_phi (sc : Scale) (N : ℕ) (gd : DensityFn) (σ : T) :
    Measurable (Phi sc N gd σ) := by
  unfold Phi
  refine (measurable_const.mul (.tsum fun q => measurable_const.mul
    ((measurable_pi_apply q).comp measurable_fst))).add (measurable_const.mul (.tsum fun z =>
      measurable_const.mul (gd.measurable.comp ((measurable_pi_apply z).comp measurable_snd))))

private lemma measurable_per (n : ℕ) : Measurable (per n) := by
  unfold per
  refine Measurable.prodMk ?_ ?_
  · exact measurable_pi_iff.mpr fun p => (measurable_pi_apply (castSite n p.1, p.2)).comp measurable_fst
  · exact measurable_pi_iff.mpr fun x => (measurable_pi_apply (castSite n x)).comp measurable_snd

private lemma isBBL_min_abs_phi (sc : Scale) (N : ℕ) (gd : DensityFn) (σ : T) :
    IsBBL (fun x => ((min |Phi sc N gd σ x| 2 : ℝ) : ℂ)) := by
  classical
  have hfin := PairNorm.finite_sample_supports sc N σ
  refine ⟨Complex.continuous_ofReal.measurable.comp
      (((measurable_phi sc N gd σ).abs).min measurable_const),
    ⟨2, fun x => ?_⟩,
    ⟨hfin.2.toFinset, hfin.1.toFinset, fun x y hP hX => ?_⟩⟩
  · rw [Complex.norm_real, Real.norm_of_nonneg (le_min (abs_nonneg _) (by norm_num))]
    exact min_le_right _ _
  · refine congrArg (fun r : ℝ => ((min |r| 2 : ℝ) : ℂ)) ?_
    unfold Phi
    congr 1
    · congr 1
      refine tsum_congr fun q => ?_
      by_cases hq : PairNorm.plaqSample (eps sc N) σ q = 0
      · dsimp only [PairNorm.plaqSample] at hq
        rw [hq, zero_mul, zero_mul]
      · rw [hP q (hfin.2.mem_toFinset.mpr hq)]
    · congr 1
      refine tsum_congr fun z => ?_
      by_cases hz : PairNorm.siteSample (eps sc N) σ z = 0
      · dsimp only [PairNorm.siteSample] at hz
        rw [hz, zero_mul, zero_mul]
      · rw [hX z (hfin.1.mem_toFinset.mpr hz)]

private lemma phi_curvPair_eq_sum (sc : Scale) (N : ℕ) (gd : DensityFn) (σ : T) :
    ∃ P : Finset (Plaq ℤ), ∀ x : Cfg ℤ,
      Phi sc N gd (curvPair σ) x =
        eps sc N ^ (3 / 2 : ℝ) * ∑ p ∈ P, PairNorm.plaqSample (eps sc N) σ p * x.1 p := by
  classical
  have hfinP := (PairNorm.finite_sample_supports sc N σ).2
  refine ⟨hfinP.toFinset, fun x => ?_⟩
  rw [phi_curvPair]
  congr 1
  refine (hasSum_sum_of_ne_finset_zero fun p hp => ?_).tsum_eq
  have hp0 : PairNorm.plaqSample (eps sc N) σ p = 0 := by
    by_contra hne
    exact hp (hfinP.mem_toFinset.mpr hne)
  dsimp only [PairNorm.plaqSample] at hp0 ⊢
  rw [hp0, zero_mul]

private lemma continuous_phi_curvPair (sc : Scale) (N : ℕ) (gd : DensityFn) (σ : T) :
    Continuous (Phi sc N gd (curvPair σ)) := by
  obtain ⟨P, hP_eq⟩ := phi_curvPair_eq_sum sc N gd σ
  rw [funext hP_eq]
  fun_prop

private lemma exists_side_embeds_curvPair (sc : Scale) (N : ℕ) (σ : T) :
    ∃ k : ℕ, ∀ s : Side, k ≤ s.n → Embeds sc N s (curvPair σ) := by
  obtain ⟨K, hK, hσ⟩ := PairNorm.exists_compact_support σ
  obtain ⟨R, hR, hsub⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : E3)
  have hnorm : ∀ x ∈ K, ‖x‖ ≤ R := fun x hx => by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hsub hx
  let ε : ℝ := eps sc N
  have hε : 0 < ε := PairNorm.eps_pos sc N
  let r : ℝ := 2 * (R + ε) / ε
  have hr_pos : 0 < r := div_pos (by positivity) hε
  have hfl_nonneg : 0 ≤ ⌊r⌋ := Int.floor_nonneg.mpr hr_pos.le
  let k : ℕ := Int.toNat (⌊r⌋ + 1)
  have hk_int : (k : ℤ) = ⌊r⌋ + 1 := Int.toNat_of_nonneg (by omega)
  have hr_lt_k : r < (k : ℝ) := by
    have h1 : r < (⌊r⌋ : ℝ) + 1 := Int.lt_floor_add_one r
    have h2 : ((k : ℤ) : ℝ) = (⌊r⌋ : ℝ) + 1 := by
      rw [hk_int, Int.cast_add, Int.cast_one]
    rw [Int.cast_natCast] at h2
    linarith [h1, h2]
  refine ⟨k, fun s hs => ⟨0, ?_, ?_⟩⟩
  · intro p hp i
    have hks : (k : ℝ) ≤ (s.n : ℝ) := Nat.cast_le.mpr hs
    have hr_lt_s : 2 * (R + ε) / ε < (s.n : ℝ) := hr_lt_k.trans_le hks
    have hmul_s : 2 * (R + ε) < (s.n : ℝ) * ε := (div_lt_iff₀ hε).mp hr_lt_s
    have hhalf : R + ε < (s.n : ℝ) * ε / 2 := by linarith [hmul_s]
    have hp' : σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre ε p) ≠ 0 := hp
    have hmemK : plaqCentre ε p ∈ K := hσ.1 p.2.1.1 p.2.1.2 (subset_tsupport _ hp')
    have hcoord : ‖plaqCentre ε p i‖ ≤ R :=
      (norm_le_pi_norm (plaqCentre ε p) i).trans (hnorm _ hmemK)
    rw [Real.norm_eq_abs] at hcoord
    obtain ⟨hlo, hhi⟩ := abs_le.mp hcoord
    dsimp only [plaqCentre] at hlo hhi
    change (0 : E3) i - (s.n : ℝ) * ε / 2 < ε * (p.1 i : ℝ) ∧
      ε * ((p.1 i : ℝ) + if i = p.2.1.1 ∨ i = p.2.1.2 then 1 else 0) <
        (0 : E3) i + (s.n : ℝ) * ε / 2
    simp only [Pi.zero_apply, zero_sub, zero_add]
    by_cases hdir : i = p.2.1.1 ∨ i = p.2.1.2
    · simp only [hdir, ↓reduceIte] at hlo hhi ⊢
      have he1 : ε * ((p.1 i : ℝ) + 1 / 2) = ε * (p.1 i : ℝ) + ε / 2 := by ring
      have he2 : ε * ((p.1 i : ℝ) + 1) = ε * (p.1 i : ℝ) + ε := by ring
      exact ⟨by linarith [hlo, he1, hε, hhalf], by linarith [hhi, he1, he2, hε, hhalf]⟩
    · simp only [hdir, ↓reduceIte, add_zero] at hlo hhi ⊢
      exact ⟨by linarith [hlo, hε, hhalf], by linarith [hhi, hε, hhalf]⟩
  · intro z hz
    change (0 : ℝ) ≠ 0 at hz
    exact absurd rfl hz

private lemma integral_le_of_sq_le {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] {f g : Ω → ℝ} (hf : Integrable f ν) (hg : Integrable g ν)
    {R : ℝ} (hR : 0 ≤ R) (hfg : ∀ ω, f ω ^ 2 ≤ g ω) (hbound : ∫ ω, g ω ∂ν ≤ R ^ 2) :
    ∫ ω, f ω ∂ν ≤ R := by
  have hdelta : ∀ δ : ℝ, 0 < δ → ∫ ω, f ω ∂ν ≤ R + δ := by
    intro δ hδ
    let r : ℝ := R + δ
    have hr : 0 < r := by dsimp only [r]; linarith [hR, hδ]
    have hpt : ∀ ω, (2 * r) * f ω ≤ g ω + r ^ 2 := by
      intro ω
      have hsq : 0 ≤ (f ω - r) ^ 2 := sq_nonneg (f ω - r)
      have hid : f ω ^ 2 + r ^ 2 - (2 * r) * f ω = (f ω - r) ^ 2 := by ring
      linarith [hsq, hid, hfg ω]
    have hint_lhs : Integrable (fun ω => (2 * r) * f ω) ν := hf.const_mul (2 * r)
    have hint_rhs : Integrable (fun ω => g ω + r ^ 2) ν := hg.fun_add (integrable_const (r ^ 2))
    have hle : (2 * r) * ∫ ω, f ω ∂ν ≤ (∫ ω, g ω ∂ν) + r ^ 2 := by
      calc (2 * r) * ∫ ω, f ω ∂ν
          = ∫ ω, (2 * r) * f ω ∂ν := by rw [← integral_const_mul]
        _ ≤ ∫ ω, (g ω + r ^ 2) ∂ν := integral_mono hint_lhs hint_rhs hpt
        _ = (∫ ω, g ω ∂ν) + ∫ _ : Ω, r ^ 2 ∂ν := integral_add hg (integrable_const (r ^ 2))
        _ = (∫ ω, g ω ∂ν) + r ^ 2 := by
            rw [integral_eq_const (Filter.Eventually.of_forall fun _ => rfl)]
    have hRr : R ^ 2 ≤ r ^ 2 := by
      have hid : r ^ 2 - R ^ 2 = δ * (2 * R + δ) := by dsimp only [r]; ring
      have hnn : 0 ≤ δ * (2 * R + δ) := mul_nonneg hδ.le (by linarith [hR, hδ])
      linarith [hid, hnn]
    have h2r : r ^ 2 + r ^ 2 = (2 * r) * r := by ring
    have hle2 : (2 * r) * ∫ ω, f ω ∂ν ≤ (2 * r) * r := by
      linarith [hle, hbound, hRr, h2r]
    by_contra hlt
    have hneg : r - ∫ ω, f ω ∂ν < 0 := by linarith [hlt]
    have hmul : (2 * r) * (r - ∫ ω, f ω ∂ν) < 0 :=
      mul_neg_of_pos_of_neg (by linarith [hr]) hneg
    have hexp : (2 * r) * (r - ∫ ω, f ω ∂ν) = (2 * r) * r - (2 * r) * ∫ ω, f ω ∂ν := by ring
    linarith [hle2, hmul, hexp]
  by_contra hgt
  have hpos : 0 < (∫ ω, f ω ∂ν - R) / 2 := by linarith [hgt]
  have hinst := hdelta _ hpos
  linarith [hinst]

private lemma torus_integral_min_curvPair_le (c : Coeffs) (sc : Scale) (N0 N : ℕ) (hN : N0 ≤ N)
    (gd : DensityFn) (σ : T) (s : Side) (hemb : Embeds sc N s (curvPair σ)) :
    ∫ ω, min |Phi sc N gd (curvPair σ) (per s.n ω)| 2 ∂(torusState s c) ≤ Rnorm sc N0 σ := by
  haveI : IsProbabilityMeasure (torusState s c) := isProbabilityMeasure_torusState c s
  obtain ⟨hInt2, hSqrt⟩ := GGOS.torus_estimate c sc N0 gd (curvPair σ) N hN s hemb
  have hSqrtR :
      Real.sqrt (∫ ω, Phi sc N gd (curvPair σ) (per s.n ω) ^ 2 ∂(torusState s c)) ≤
        Rnorm sc N0 σ :=
    hSqrt.trans (pairNorm_curvPair_le sc N0 gd σ)
  have hR_nonneg : 0 ≤ Rnorm sc N0 σ := (Real.sqrt_nonneg _).trans hSqrtR
  have hSq_le :
      ∫ ω, Phi sc N gd (curvPair σ) (per s.n ω) ^ 2 ∂(torusState s c) ≤ Rnorm sc N0 σ ^ 2 :=
    (Real.sqrt_le_left hR_nonneg).mp hSqrtR
  have hf_meas :
      Measurable (fun ω : Cfg (ZMod s.n) => min |Phi sc N gd (curvPair σ) (per s.n ω)| 2) :=
    (((measurable_phi sc N gd (curvPair σ)).comp (measurable_per s.n)).abs).min measurable_const
  have hf_int :
      Integrable (fun ω : Cfg (ZMod s.n) => min |Phi sc N gd (curvPair σ) (per s.n ω)| 2)
        (torusState s c) :=
    Integrable.mono' (integrable_const (2 : ℝ)) hf_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (le_min (abs_nonneg _) (by norm_num))]
        exact min_le_right _ _)
  have hfg : ∀ ω : Cfg (ZMod s.n),
      (min |Phi sc N gd (curvPair σ) (per s.n ω)| 2) ^ 2 ≤
        Phi sc N gd (curvPair σ) (per s.n ω) ^ 2 := by
    intro ω
    let z := Phi sc N gd (curvPair σ) (per s.n ω)
    let m := min |z| 2
    have hm0 : 0 ≤ m := le_min (abs_nonneg z) (by norm_num)
    have hmz : m ≤ |z| := min_le_left |z| 2
    have hprod : 0 ≤ (|z| - m) * (|z| + m) :=
      mul_nonneg (by linarith [hmz]) (by linarith [abs_nonneg z, hm0])
    have hid : |z| ^ 2 - m ^ 2 = (|z| - m) * (|z| + m) := by ring
    have hsq : |z| ^ 2 = z ^ 2 := sq_abs z
    change m ^ 2 ≤ z ^ 2
    linarith [hprod, hid, hsq]
  exact integral_le_of_sq_le (torusState s c) hf_int hInt2 hR_nonneg hfg hSq_le

/-- [GG-OS] Proposition 4.2, second inequality of (4.1): for a limit point of the torus
states at level `N ≥ N0`, `ω_N(min(|Φ_N(σ)|, 2)) ≤ ‖σ‖`. -/
theorem trunc_le_pairNorm_of_isLimitPoint (sc : Scale) (N0 : ℕ) (gd : DensityFn) (c : Coeffs)
    (ω : (Cfg ℤ → ℂ) → ℂ) (N : ℕ) (hN : N0 ≤ N) (h : IsLimitPoint c ω) (σ : T) :
    (ω fun x => ((min |Phi sc N gd σ x| 2 : ℝ) : ℂ)).re ≤ pairNorm sc N0 gd σ := by
  obtain ⟨L, μ, hL, hprob, _hsupp, hconv, hbbl⟩ := h
  haveI : IsProbabilityMeasure μ := hprob
  have hω_eq : (ω fun x => ((min |Phi sc N gd σ x| 2 : ℝ) : ℂ)).re =
      ∫ x, min |Phi sc N gd σ x| 2 ∂μ := by
    rw [hbbl _ (isBBL_min_abs_phi sc N gd σ), integral_complex_ofReal, Complex.ofReal_re]
  let fPhi : Cfg ℤ → ℝ := fun x => min |Phi sc N gd σ x| 2
  let fCurv : Cfg ℤ → ℝ := fun x => min |Phi sc N gd (curvPair σ) x| 2
  let B : ℝ := supNorm gd * Enorm sc N0 σ
  have hfPhi_int : Integrable fPhi μ :=
    Integrable.mono' (integrable_const (2 : ℝ))
      (((measurable_phi sc N gd σ).abs).min measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (le_min (abs_nonneg _) (by norm_num))]
        exact min_le_right _ _)
  have hfCurv_int : Integrable fCurv μ :=
    Integrable.mono' (integrable_const (2 : ℝ))
      (((measurable_phi sc N gd (curvPair σ)).abs).min measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (le_min (abs_nonneg _) (by norm_num))]
        exact min_le_right _ _)
  have hpt_split : ∀ x : Cfg ℤ, fPhi x ≤ fCurv x + B := by
    intro x
    dsimp only [fPhi, fCurv, B]
    rw [phi_eq_curvPair_add_densityPart sc N gd σ x]
    have h1 := min_abs_add_le (Phi sc N gd (curvPair σ) x) (densityPart sc N gd σ x)
    have h2 := abs_densityPart_le sc N0 N hN gd σ x
    linarith [h1, h2]
  have hint_split : ∫ x, fPhi x ∂μ ≤ (∫ x, fCurv x ∂μ) + B := by
    calc ∫ x, fPhi x ∂μ
        ≤ ∫ x, (fCurv x + B) ∂μ :=
          integral_mono hfPhi_int (hfCurv_int.fun_add (integrable_const B)) hpt_split
      _ = (∫ x, fCurv x ∂μ) + ∫ _ : Cfg ℤ, B ∂μ :=
          integral_add hfCurv_int (integrable_const B)
      _ = (∫ x, fCurv x ∂μ) + B := by
          rw [integral_eq_const (Filter.Eventually.of_forall fun _ => rfl)]
  let G : Cfg ℤ → ℂ := fun x => ((fCurv x : ℝ) : ℂ)
  have hG_bbl : IsBBL G := isBBL_min_abs_phi sc N gd (curvPair σ)
  have hG_cont : Continuous G :=
    Complex.continuous_ofReal.comp
      (((continuous_phi_curvPair sc N gd σ).abs).min continuous_const)
  have hG_lim := hconv G hG_bbl.isLocal hG_cont hG_bbl.bounded
  have h_real_lim : Tendsto
      (fun n => ∫ ω, fCurv (per (L n).n ω) ∂(torusState (L n) c))
      atTop (𝓝 (∫ x, fCurv x ∂μ)) := by
    have hre : Tendsto (fun n => (∫ ω, G (per (L n).n ω) ∂(torusState (L n) c)).re)
        atTop (𝓝 (∫ x, G x ∂μ).re) :=
      (Complex.continuous_re.tendsto _).comp hG_lim
    have h1 : (fun n => (∫ ω, G (per (L n).n ω) ∂(torusState (L n) c)).re) =
        fun n => ∫ ω, fCurv (per (L n).n ω) ∂(torusState (L n) c) := by
      funext n
      dsimp only [G]
      rw [integral_complex_ofReal, Complex.ofReal_re]
    have h2 : (∫ x, G x ∂μ).re = ∫ x, fCurv x ∂μ := by
      dsimp only [G]
      rw [integral_complex_ofReal, Complex.ofReal_re]
    rwa [h1, h2] at hre
  obtain ⟨k, hk_emb⟩ := exists_side_embeds_curvPair sc N σ
  have h_ev : ∀ᶠ n in atTop,
      ∫ ω, fCurv (per (L n).n ω) ∂(torusState (L n) c) ≤ Rnorm sc N0 σ := by
    filter_upwards [hL.eventually (eventually_ge_atTop k)] with n hn
    exact torus_integral_min_curvPair_le c sc N0 N hN gd σ (L n) (hk_emb (L n) hn)
  have hint_curv : ∫ x, fCurv x ∂μ ≤ Rnorm sc N0 σ :=
    le_of_tendsto h_real_lim h_ev
  rw [hω_eq]
  unfold pairNorm
  dsimp only [fPhi, B] at hint_split
  linarith [hint_split, hint_curv]

end GGOS.Work

end

module

public import GGOS.Frozen.Defs.Enorm
public import GGOS.Frozen.Defs.Rnorm
public import GGOS.Frozen.Defs.SupNorm
public import GGOS.Frozen.GaussianDomination
public import GGOS.Frozen.PairNorm
public import GGOS.OS.Work.Phase
public import GGOS.OS.Work.StateRP
public import GGOS.Work.PairNormSeminorm

/-!
# Exponential moments of the smeared field under a limit point
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace GGOS.OS

/-! ### A truncation lemma -/

theorem integrable_of_min_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Y : Ω → ℝ} (hY : Measurable Y) (hY0 : ∀ x, 0 ≤ Y x) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ n : ℕ, ∫ x, min (Y x) n ∂μ ≤ B) : Integrable Y μ ∧ ∫ x, Y x ∂μ ≤ B := by
  have hmono : Monotone fun (n : ℕ) (x : Ω) => ENNReal.ofReal (min (Y x) n) := by
    intro m n hmn x
    exact ENNReal.ofReal_le_ofReal (min_le_min le_rfl (by exact_mod_cast hmn))
  have hsup (x : Ω) : ⨆ n : ℕ, ENNReal.ofReal (min (Y x) n) = ENNReal.ofReal (Y x) := by
    refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)) ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (Y x)
    refine le_trans ?_ (le_iSup (fun n : ℕ => ENNReal.ofReal (min (Y x) n)) n)
    rw [min_eq_left hn]
  have hmeas (n : ℕ) : Measurable fun x => min (Y x) (n : ℝ) := hY.min measurable_const
  have hint (n : ℕ) : Integrable (fun x => min (Y x) (n : ℝ)) μ :=
    Integrable.mono' (integrable_const (n : ℝ)) (hmeas n).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (le_min (hY0 x) (Nat.cast_nonneg n))]
        exact min_le_right _ _)
  have hle : ∫⁻ x, ENNReal.ofReal (Y x) ∂μ ≤ ENNReal.ofReal B := by
    simp_rw [← hsup]
    rw [lintegral_iSup (fun n => (hmeas n).ennreal_ofReal) hmono]
    refine iSup_le fun n => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n)
      (Eventually.of_forall fun x => le_min (hY0 x) (Nat.cast_nonneg n))]
    exact ENNReal.ofReal_le_ofReal (h n)
  have hI : Integrable Y μ := by
    refine ⟨hY.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hY0)]
    exact hle.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hI, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall hY0)] at hle
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hle

/-! ### The two parts of the phase -/

/-- The curvature part of the phase. -/
def curvPart (sc : Scale) (N : ℕ) (σ : T) (x : Cfg ℤ) : ℝ :=
  eps sc N ^ (3 / 2 : ℝ) *
    ∑' p : Plaq ℤ, σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p) * x.1 p

/-- The density part of the phase. -/
def densPart (sc : Scale) (N : ℕ) (gd : DensityFn) (σ : T) (x : Cfg ℤ) : ℝ :=
  eps sc N ^ 3 * ∑' z : Site ℤ, σ.1.2 (sitePos (eps sc N) z) * gd.toFun (x.2 z)

theorem phi_eq (sc : Scale) (N : ℕ) (gd : DensityFn) (σ : T) (x : Cfg ℤ) :
    Phi sc N gd σ x = curvPart sc N σ x + densPart sc N gd σ x := rfl

theorem abs_gd_le (gd : DensityFn) (r : ℝ) : |gd.toFun r| ≤ supNorm gd := by
  obtain ⟨C, hC⟩ := gd.bdd
  exact le_ciSup (f := fun r : ℝ => |gd.toFun r|) ⟨C, Set.forall_mem_range.mpr hC⟩ r

theorem abs_densPart_le (sc : Scale) {N0 N : ℕ} (hN : N0 ≤ N) (gd : DensityFn) (σ : T)
    (x : Cfg ℤ) : |densPart sc N gd σ x| ≤ supNorm gd * Enorm sc N0 σ := by
  have hε : 0 < eps sc N := Work.PairNorm.eps_pos sc N
  have hfin := finite_site_support sc N σ
  have hs0 : 0 ≤ supNorm gd := (abs_nonneg _).trans (abs_gd_le gd 0)
  have hsum : Summable fun z : Site ℤ => |σ.1.2 (sitePos (eps sc N) z)| :=
    summable_of_hasFiniteSupport (hfin.subset fun z hz => by simpa using hz)
  have hsum' : Summable fun z : Site ℤ => |σ.1.2 (sitePos (eps sc N) z) * gd.toFun (x.2 z)| :=
    summable_of_hasFiniteSupport (hfin.subset fun z hz => by
      intro h0
      apply hz
      simp [h0])
  have h1 : |∑' z : Site ℤ, σ.1.2 (sitePos (eps sc N) z) * gd.toFun (x.2 z)| ≤
      supNorm gd * ∑' z : Site ℤ, |σ.1.2 (sitePos (eps sc N) z)| := by
    have hn : ‖∑' z : Site ℤ, σ.1.2 (sitePos (eps sc N) z) * gd.toFun (x.2 z)‖ ≤
        ∑' z : Site ℤ, ‖σ.1.2 (sitePos (eps sc N) z) * gd.toFun (x.2 z)‖ :=
      norm_tsum_le_tsum_norm hsum'
    rw [← tsum_mul_left]
    refine hn.trans (hsum'.tsum_le_tsum (fun z => ?_) (hsum.mul_left _))
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_gd_le gd _) (abs_nonneg _)
  have h2 : eps sc N ^ 3 * ∑' z : Site ℤ, |σ.1.2 (sitePos (eps sc N) z)| ≤ Enorm sc N0 σ :=
    le_ciSup (f := fun M : {M : ℕ // N0 ≤ M} =>
      eps sc M ^ 3 * ∑' z : Site ℤ, |σ.1.2 (sitePos (eps sc M) z)|)
      ((GGOS.pairNorm_finite_seminorm_admissible sc N0 gd).2.1 σ) ⟨N, hN⟩
  unfold densPart
  rw [abs_mul, abs_of_pos (pow_pos hε 3)]
  calc eps sc N ^ 3 * |∑' z : Site ℤ, σ.1.2 (sitePos (eps sc N) z) * gd.toFun (x.2 z)|
      ≤ eps sc N ^ 3 * (supNorm gd * ∑' z : Site ℤ, |σ.1.2 (sitePos (eps sc N) z)|) :=
        mul_le_mul_of_nonneg_left h1 (pow_pos hε 3).le
    _ = supNorm gd * (eps sc N ^ 3 * ∑' z : Site ℤ, |σ.1.2 (sitePos (eps sc N) z)|) := by ring
    _ ≤ supNorm gd * Enorm sc N0 σ := mul_le_mul_of_nonneg_left h2 hs0

theorem rnorm_nonneg (sc : Scale) (N0 : ℕ) (σ : T) : 0 ≤ Rnorm sc N0 σ :=
  Real.iSup_nonneg fun _ => Real.sqrt_nonneg _

theorem enorm_nonneg (sc : Scale) (N0 : ℕ) (σ : T) : 0 ≤ Enorm sc N0 σ :=
  Real.iSup_nonneg fun N => mul_nonneg (pow_pos (Work.PairNorm.eps_pos sc N) 3).le
    (tsum_nonneg fun _ => abs_nonneg _)

theorem supNorm_nonneg (gd : DensityFn) : 0 ≤ supNorm gd :=
  (abs_nonneg _).trans (abs_gd_le gd 0)

theorem sq_le_rnorm_sq (sc : Scale) {N0 N : ℕ} (hN : N0 ≤ N) (gd : DensityFn) (σ : T) :
    eps sc N ^ 3 * ∑' p : Plaq ℤ, (σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p)) ^ 2 ≤
      Rnorm sc N0 σ ^ 2 := by
  have h : Real.sqrt (eps sc N ^ 3 *
      ∑' p : Plaq ℤ, (σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p)) ^ 2) ≤ Rnorm sc N0 σ :=
    le_ciSup (f := fun M : {M : ℕ // N0 ≤ M} => Real.sqrt (eps sc M ^ 3 *
      ∑' p : Plaq ℤ, (σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc M) p)) ^ 2))
      ((GGOS.pairNorm_finite_seminorm_admissible sc N0 gd).1 σ) ⟨N, hN⟩
  exact (Real.sqrt_le_left (rnorm_nonneg sc N0 σ)).mp h

/-! ### The torus -/

theorem castSite_injOn {n : ℕ} {M : ℕ} (hn : 2 * M < n) {x y : Site ℤ}
    (hx : ∀ i, |x i| ≤ M) (hy : ∀ i, |y i| ≤ M) (h : castSite n x = castSite n y) : x = y := by
  funext i
  have hi : ((x i : ℤ) : ZMod n) = ((y i : ℤ) : ZMod n) := congrFun h i
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hi
  have hlt : |y i - x i| < n := by
    have h1 := abs_le.mp (hx i)
    have h2 := abs_le.mp (hy i)
    rw [abs_lt]
    constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd hi hlt
  omega

theorem exists_coord_bound (P : Finset (Plaq ℤ)) : ∃ M : ℕ, ∀ p ∈ P, ∀ i, |p.1 i| ≤ M := by
  refine ⟨∑ p ∈ P, ∑ i, (p.1 i).natAbs, fun p hp i => ?_⟩
  have h1 := Finset.single_le_sum (f := fun p : Plaq ℤ => ∑ i, (p.1 i).natAbs)
    (fun _ _ => Nat.zero_le _) hp
  have h2 := Finset.single_le_sum (f := fun i : Fin 3 => (p.1 i).natAbs)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have h3 : ((p.1 i).natAbs : ℤ) = |p.1 i| := Int.natCast_natAbs _
  rw [← h3]
  exact_mod_cast h2.trans h1

theorem rpow_three_halves_sq {ε : ℝ} (hε : 0 ≤ ε) : (ε ^ (3 / 2 : ℝ)) ^ 2 = ε ^ 3 := by
  rw [← Real.rpow_natCast (ε ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul hε, ← Real.rpow_natCast ε 3]
  norm_num

/-- On the large tori the curvature part is a linear form of the torus curvature whose coefficients
have square sum at most `R(f)²`. -/
theorem exists_torus_coeff (sc : Scale) {N0 N : ℕ} (hN : N0 ≤ N) (gd : DensityFn) (σ : T) :
    ∃ k : ℕ, ∀ s : Side, k ≤ s.n → ∃ a : Plaq (ZMod s.n) → ℝ,
      (∀ ω, curvPart sc N σ (per s.n ω) = ∑ q, a q * ω.1 q) ∧ ∑ q, a q ^ 2 ≤ Rnorm sc N0 σ ^ 2 := by
  classical
  have hε : 0 < eps sc N := Work.PairNorm.eps_pos sc N
  let P : Finset (Plaq ℤ) := (finite_face_support sc N σ).toFinset
  obtain ⟨M, hM⟩ := exists_coord_bound P
  let f : Plaq ℤ → ℝ := fun p => σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p)
  have hf (p : Plaq ℤ) (hp : p ∉ P) : f p = 0 := by
    by_contra h
    exact hp (by simpa [P] using h)
  refine ⟨2 * M + 1, fun s hs => ?_⟩
  let cp : Plaq ℤ → Plaq (ZMod s.n) := fun p => (castSite s.n p.1, p.2)
  have hinj : Set.InjOn cp P := by
    intro p hp q hq h
    refine Prod.ext (castSite_injOn (n := s.n) (M := M) (by omega) (hM p hp) (hM q hq) ?_) ?_
    · exact congrArg Prod.fst h
    · exact congrArg (fun q : Plaq (ZMod s.n) => q.2) h
  let a : Plaq (ZMod s.n) → ℝ := fun q => ∑ p ∈ P, if cp p = q then eps sc N ^ (3 / 2 : ℝ) * f p else 0
  have ha (g : Plaq (ZMod s.n) → ℝ) :
      ∑ q, a q * g q = ∑ p ∈ P, eps sc N ^ (3 / 2 : ℝ) * f p * g (cp p) := by
    simp only [a, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp
  have hacp (p : Plaq ℤ) (hp : p ∈ P) : a (cp p) = eps sc N ^ (3 / 2 : ℝ) * f p := by
    simp only [a]
    rw [Finset.sum_eq_single p]
    · simp
    · intro q hq hqp
      have : cp q ≠ cp p := fun h => hqp (hinj hq hp h)
      simp [this]
    · intro h
      exact absurd hp h
  refine ⟨a, fun ω => ?_, ?_⟩
  · rw [ha]
    unfold curvPart
    have hts : ∑' p : Plaq ℤ, σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p) * (per s.n ω).1 p =
        ∑ p ∈ P, f p * ω.1 (cp p) :=
      tsum_eq_sum fun p hp => by
        have := hf p hp
        simp only [f] at this
        rw [this, zero_mul]
    rw [hts, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => (mul_assoc _ _ _).symm
  · have h1 : ∑ q, a q ^ 2 = ∑ p ∈ P, (eps sc N ^ (3 / 2 : ℝ) * f p) ^ 2 := by
      have := ha a
      simp only [← pow_two] at this
      rw [this]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [hacp p hp, pow_two]
    have h2 : ∑' p : Plaq ℤ, f p ^ 2 = ∑ p ∈ P, f p ^ 2 :=
      tsum_eq_sum fun p hp => by rw [hf p hp]; norm_num
    rw [h1]
    simp only [mul_pow, rpow_three_halves_sq hε.le]
    rw [← Finset.mul_sum, ← h2]
    exact sq_le_rnorm_sq sc hN gd σ

theorem continuous_curvPart (sc : Scale) (N : ℕ) (σ : T) : Continuous (curvPart sc N σ) := by
  have h (x : Cfg ℤ) : ∑' p : Plaq ℤ, σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p) * x.1 p =
      ∑ p ∈ (finite_face_support sc N σ).toFinset,
        σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p) * x.1 p :=
    tsum_eq_sum fun p hp => by
      have : σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p) = 0 := by
        by_contra h
        exact hp (by simpa using h)
      rw [this, zero_mul]
  unfold curvPart
  simp only [h]
  fun_prop

theorem isLocal_curvPart (sc : Scale) (N : ℕ) (σ : T) (f : ℝ → ℂ) :
    IsLocal fun x => f (curvPart sc N σ x) := by
  refine ⟨(finite_face_support sc N σ).toFinset, ∅, fun ω ω' h _ => ?_⟩
  have : curvPart sc N σ ω = curvPart sc N σ ω' := by
    unfold curvPart
    congr 1
    refine tsum_congr fun p => ?_
    by_cases hp : σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p) = 0
    · rw [hp, zero_mul, zero_mul]
    · rw [h p (by simpa using hp)]
  simp only [this]

/-- The exponential moment of the curvature part under a limit point. -/
theorem exp_curvPart {cN : Coeffs} {ωN : (Cfg ℤ → ℂ) → ℂ} {μ : Measure (Cfg ℤ)}
    (h : Represents cN ωN μ) (sc : Scale) {N0 N : ℕ} (hN : N0 ≤ N) (gd : DensityFn) (σ : T) :
    Integrable (fun x => Real.exp (curvPart sc N σ x)) μ ∧
      ∫ x, Real.exp (curvPart sc N σ x) ∂μ ≤ Real.exp (1 / 2 * Rnorm sc N0 σ ^ 2) := by
  have hprob := h.prob
  obtain ⟨L, hL, hlim⟩ := h.lim
  obtain ⟨k, hk⟩ := exists_torus_coeff sc hN gd σ
  have hc := continuous_curvPart sc N σ
  refine integrable_of_min_le (Real.continuous_exp.comp hc).measurable
    (fun x => (Real.exp_pos _).le) (Real.exp_pos _).le fun n => ?_
  let g : Cfg ℤ → ℝ := fun x => min (Real.exp (curvPart sc N σ x)) n
  have hg : Continuous g := (Real.continuous_exp.comp hc).min continuous_const
  have hg0 (x : Cfg ℤ) : 0 ≤ g x := le_min (Real.exp_pos _).le (Nat.cast_nonneg n)
  have hgb (x : Cfg ℤ) : g x ≤ n := min_le_right _ _
  have hl := hlim (fun x => (g x : ℂ))
    (isLocal_curvPart sc N σ fun r => ((min (Real.exp r) n : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp hg) ⟨n, fun x => by
      rw [Complex.norm_real, Real.norm_of_nonneg (hg0 x)]
      exact hgb x⟩
  have hl' : Tendsto (fun m => ∫ ω, g (per (L m).n ω) ∂(torusState (L m) cN)) atTop
      (𝓝 (∫ x, g x ∂μ)) := by
    have hre := (Complex.continuous_re.tendsto _).comp hl
    simp only [integral_complex_ofReal, Function.comp_def, Complex.ofReal_re] at hre
    exact hre
  refine le_of_tendsto hl' ?_
  filter_upwards [hL.eventually (eventually_ge_atTop k)] with m hm
  obtain ⟨a, ha, ha2⟩ := hk (L m) hm
  obtain ⟨hp, hint, hle⟩ := GGOS.gaussian_domination cN (L m) a
  have hmeas : Measurable fun ω : Cfg (ZMod (L m).n) => g (per (L m).n ω) :=
    hg.measurable.comp (measurable_per _)
  calc ∫ ω, g (per (L m).n ω) ∂(torusState (L m) cN)
      ≤ ∫ ω, Real.exp (∑ p, a p * ω.1 p) ∂(torusState (L m) cN) := by
        refine integral_mono (Integrable.mono' (integrable_const (n : ℝ))
          hmeas.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)) hint fun ω => ?_
        · rw [Real.norm_of_nonneg (hg0 _)]
          exact hgb _
        · simp only [g, ha]
          exact min_le_left _ _
    _ ≤ Real.exp (1 / 2 * ∑ p, a p ^ 2) := hle
    _ ≤ Real.exp (1 / 2 * Rnorm sc N0 σ ^ 2) :=
        Real.exp_le_exp.mpr (by linarith)

/-- The exponential moment of the smeared field under a limit point. -/
theorem exp_phi {cN : Coeffs} {ωN : (Cfg ℤ → ℂ) → ℂ} {μ : Measure (Cfg ℤ)}
    (h : Represents cN ωN μ) (sc : Scale) {N0 N : ℕ} (hN : N0 ≤ N) (gd : DensityFn) (σ : T) :
    Integrable (fun x => Real.exp (Phi sc N gd σ x)) μ ∧
      ∫ x, Real.exp (Phi sc N gd σ x) ∂μ ≤
        Real.exp (1 / 2 * Rnorm sc N0 σ ^ 2 + supNorm gd * Enorm sc N0 σ) := by
  obtain ⟨hint, hle⟩ := exp_curvPart h sc hN gd σ
  have hb (x : Cfg ℤ) : Real.exp (Phi sc N gd σ x) ≤
      Real.exp (curvPart sc N σ x) * Real.exp (supNorm gd * Enorm sc N0 σ) := by
    rw [← Real.exp_add, phi_eq]
    exact Real.exp_le_exp.mpr (add_le_add le_rfl
      ((le_abs_self _).trans (abs_densPart_le sc hN gd σ x)))
  have hint' : Integrable (fun x => Real.exp (Phi sc N gd σ x)) μ :=
    Integrable.mono' (hint.mul_const _)
      (Real.measurable_exp.comp (measurable_phi sc N gd σ)).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        exact hb x)
  refine ⟨hint', ?_⟩
  calc ∫ x, Real.exp (Phi sc N gd σ x) ∂μ
      ≤ ∫ x, Real.exp (curvPart sc N σ x) * Real.exp (supNorm gd * Enorm sc N0 σ) ∂μ :=
        integral_mono hint' (hint.mul_const _) hb
    _ = (∫ x, Real.exp (curvPart sc N σ x) ∂μ) * Real.exp (supNorm gd * Enorm sc N0 σ) :=
        integral_mul_const _ _
    _ ≤ Real.exp (1 / 2 * Rnorm sc N0 σ ^ 2) * Real.exp (supNorm gd * Enorm sc N0 σ) :=
        mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

end GGOS.OS

end

end

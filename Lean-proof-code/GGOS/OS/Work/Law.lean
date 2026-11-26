module

public import GGOS.OS.Schwinger
public import GGOS.OS.Work.ExpMoment
public import GGOS.OS.Work.Limit

import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# The law of finitely many smeared fields in the limit

Lévy's theorem and Prokhorov's theorem give, for every finite family of test pairs, the law of the
smeared fields with the generating function of the limit functional ([GG-OS] Lemma 9.3 (c)).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal RealInnerProductSpace

namespace GGOS.OS

/-! ### Existence of a limit law -/

/-- If the characteristic functions of probability measures on a finite-dimensional space converge
pointwise to a function that is continuous at `0`, the measures converge weakly to a probability
measure with that characteristic function. -/
theorem exists_limit_law {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : ℕ → ProbabilityMeasure E)
    {f : E → ℂ} (hf : ContinuousAt f 0)
    (h : ∀ t, Tendsto (fun n => charFun (μ n : Measure E) t) atTop (𝓝 (f t))) :
    ∃ ν : ProbabilityMeasure E, (∀ t, charFun (ν : Measure E) t = f t) ∧
      Tendsto μ atTop (𝓝 ν) := by
  have htight : IsTightMeasureSet {((m : ProbabilityMeasure E) : Measure E) | m ∈ Set.range μ} := by
    have h1 := isTightMeasureSet_of_tendsto_charFun (μ := fun n => (μ n : Measure E)) hf h
    refine h1.subset ?_
    rintro _ ⟨m, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩
  have hcomp := isCompact_closure_of_isTightMeasureSet htight
  obtain ⟨ν, -, hν⟩ := hcomp.exists_clusterPt (f := map μ atTop)
    (le_principal_iff.mpr (mem_map.mpr (Eventually.of_forall fun n =>
      subset_closure ⟨n, rfl⟩)))
  have hmc : MapClusterPt ν atTop μ := hν
  obtain ⟨U, hU, hUν⟩ := mapClusterPt_iff_ultrafilter.mp hmc
  have hchar (t : E) : charFun (ν : Measure E) t = f t := by
    have hl := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hUν
      (innerProbChar t)
    simp only [← charFun_eq_integral_innerProbChar] at hl
    exact tendsto_nhds_unique hl ((h t).mono_left hU)
  refine ⟨ν, hchar, ProbabilityMeasure.tendsto_of_tendsto_charFun fun t => ?_⟩
  rw [hchar]
  exact h t

/-! ### Seminorm inequalities -/

theorem seminorm_zero {p : T → ℝ} (hp : IsSeminorm p) : p 0 = 0 := by
  have h := hp.smul 0 0
  simpa using h

theorem seminorm_sum_smul_le {p : T → ℝ} (hp : IsSeminorm p) {ι : Type*} (s : Finset ι)
    (t : ι → ℝ) (σ : ι → T) : p (∑ j ∈ s, t j • σ j) ≤ ∑ j ∈ s, |t j| * p (σ j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [seminorm_zero hp]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine (hp.add_le _ _).trans (add_le_add ?_ ih)
    rw [hp.smul]

theorem isSeminorm_enorm (sc : Scale) (N0 : ℕ) (gd : DensityFn) : IsSeminorm (Enorm sc N0) := by
  have hb (σ : T) := (GGOS.pairNorm_finite_seminorm_admissible sc N0 gd).2.1 σ
  have hs (N : ℕ) (σ : T) : Summable fun z : Site ℤ => |σ.1.2 (sitePos (eps sc N) z)| :=
    summable_of_hasFiniteSupport ((finite_site_support sc N σ).subset fun z hz => by simpa using hz)
  have hle (σ : T) (N : {N : ℕ // N0 ≤ N}) :
      eps sc N ^ 3 * ∑' z : Site ℤ, |σ.1.2 (sitePos (eps sc N) z)| ≤ Enorm sc N0 σ :=
    le_ciSup (hb σ) N
  have : Nonempty {N : ℕ // N0 ≤ N} := ⟨⟨N0, le_rfl⟩⟩
  refine ⟨enorm_nonneg sc N0, fun σ τ => ?_, fun r σ => ?_⟩
  · refine ciSup_le fun N => ?_
    have hε : 0 < eps sc N ^ 3 := pow_pos (Work.PairNorm.eps_pos sc N) 3
    have h1 : ∑' z : Site ℤ, |(σ + τ).1.2 (sitePos (eps sc N) z)| ≤
        (∑' z : Site ℤ, |σ.1.2 (sitePos (eps sc N) z)|) +
          ∑' z : Site ℤ, |τ.1.2 (sitePos (eps sc N) z)| := by
      rw [← (hs N σ).tsum_add (hs N τ)]
      exact (hs N (σ + τ)).tsum_le_tsum (fun z => abs_add_le _ _) ((hs N σ).add (hs N τ))
    calc eps sc N ^ 3 * ∑' z : Site ℤ, |(σ + τ).1.2 (sitePos (eps sc N) z)|
        ≤ eps sc N ^ 3 * ((∑' z : Site ℤ, |σ.1.2 (sitePos (eps sc N) z)|) +
          ∑' z : Site ℤ, |τ.1.2 (sitePos (eps sc N) z)|) := mul_le_mul_of_nonneg_left h1 hε.le
      _ ≤ Enorm sc N0 σ + Enorm sc N0 τ := by
          rw [mul_add]
          exact add_le_add (hle σ N) (hle τ N)
  · unfold Enorm
    rw [Real.mul_iSup_of_nonneg (abs_nonneg r)]
    refine iSup_congr fun N => ?_
    have h1 : ∑' z : Site ℤ, |(r • σ).1.2 (sitePos (eps sc N) z)| =
        |r| * ∑' z : Site ℤ, |σ.1.2 (sitePos (eps sc N) z)| := by
      rw [← tsum_mul_left]
      refine tsum_congr fun z => ?_
      exact abs_mul r _
    rw [h1]
    ring

/-- The zero density function. -/
def zeroDensity : DensityFn := ⟨fun _ => 0, measurable_const, 0, by simp⟩

theorem isSeminorm_rnorm (sc : Scale) (N0 : ℕ) : IsSeminorm (Rnorm sc N0) := by
  have h := (GGOS.pairNorm_finite_seminorm_admissible sc N0 zeroDensity).2.2.1
  have h0 : supNorm zeroDensity = 0 := by simp [supNorm, zeroDensity]
  have he : pairNorm sc N0 zeroDensity = Rnorm sc N0 := by
    funext σ
    simp [pairNorm, h0]
  rwa [he] at h

theorem isSeminorm_pairNorm (sc : Scale) (N0 : ℕ) (gd : DensityFn) :
    IsSeminorm (pairNorm sc N0 gd) :=
  (GGOS.pairNorm_finite_seminorm_admissible sc N0 gd).2.2.1

/-! ### The vector of the smeared fields -/

/-- The smeared fields of a finite family of test pairs. -/
def fieldVec (sc : Scale) (N : ℕ) (gd : DensityFn) {n : ℕ} (σ : Fin n → T) (x : Cfg ℤ) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j => Phi sc N gd (σ j) x

theorem measurable_fieldVec (sc : Scale) (N : ℕ) (gd : DensityFn) {n : ℕ} (σ : Fin n → T) :
    Measurable (fieldVec sc N gd σ) := by
  refine (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp (measurable_pi_iff.mpr fun j => ?_)
  exact measurable_phi sc N gd (σ j)

theorem inner_fieldVec (sc : Scale) (N : ℕ) (gd : DensityFn) {n : ℕ} (σ : Fin n → T) (x : Cfg ℤ)
    (t : EuclideanSpace ℝ (Fin n)) :
    ⟪fieldVec sc N gd σ x, t⟫ = Phi sc N gd (∑ j, t j • σ j) x := by
  rw [phi_sum_smul, PiLp.inner_apply]
  rfl

variable {sc : Scale} {N0 : ℕ} {gd : DensityFn} {c : ℕ → Coeffs}
  {ω : ℕ → (Cfg ℤ → ℂ) → ℂ} {Nm : ℕ → ℕ} {S : Alg →ₗ[ℂ] ℂ}

theorem charFun_fieldVec {cN : Coeffs} {ωN : (Cfg ℤ → ℂ) → ℂ} {μ : Measure (Cfg ℤ)}
    (h : Represents cN ωN μ) (sc : Scale) (N : ℕ) (gd : DensityFn) {n : ℕ} (σ : Fin n → T)
    (t : EuclideanSpace ℝ (Fin n)) :
    charFun (μ.map (fieldVec sc N gd σ)) t = ωN (expPhi sc N gd (∑ j, t j • σ j)) := by
  rw [charFun_apply, integral_map (measurable_fieldVec sc N gd σ).aemeasurable
    (by fun_prop), h.eq _ (Work.Limit.bbl_exp sc N gd _)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [inner_fieldVec, expPhi, mul_comm Complex.I]

/-- The Gaussian-type bound of the exponential moments of a family. -/
def expBound (sc : Scale) (N0 : ℕ) (gd : DensityFn) {n : ℕ} (σ : Fin n → T) (v : Fin n → ℝ) : ℝ :=
  Real.exp (1 / 2 * (∑ j, |v j| * Rnorm sc N0 (σ j)) ^ 2
    + supNorm gd * ∑ j, |v j| * Enorm sc N0 (σ j))

theorem exp_fieldVec {cN : Coeffs} {ωN : (Cfg ℤ → ℂ) → ℂ} {μ : Measure (Cfg ℤ)}
    (h : Represents cN ωN μ) (sc : Scale) {N0 N : ℕ} (hN : N0 ≤ N) (gd : DensityFn) {n : ℕ}
    (σ : Fin n → T) (v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x => Real.exp ⟪x, v⟫) (μ.map (fieldVec sc N gd σ)) ∧
      ∫ x, Real.exp ⟪x, v⟫ ∂(μ.map (fieldVec sc N gd σ)) ≤ expBound sc N0 gd σ v := by
  obtain ⟨hint, hle⟩ := exp_phi h sc hN gd (∑ j, v j • σ j)
  have hm := measurable_fieldVec sc N gd σ
  have he : (fun x => Real.exp ⟪fieldVec sc N gd σ x, v⟫) =
      fun x => Real.exp (Phi sc N gd (∑ j, v j • σ j) x) := by
    funext x
    rw [inner_fieldVec]
  constructor
  · rw [integrable_map_measure (by fun_prop) hm.aemeasurable]
    change Integrable (fun x => Real.exp ⟪fieldVec sc N gd σ x, v⟫) μ
    rwa [he]
  · rw [integral_map hm.aemeasurable (by fun_prop), he]
    refine hle.trans (Real.exp_le_exp.mpr (add_le_add ?_ ?_))
    · have h1 := seminorm_sum_smul_le (isSeminorm_rnorm sc N0) Finset.univ v σ
      have h0 := rnorm_nonneg sc N0 (∑ j, v j • σ j)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 2) (by norm_num)
    · exact mul_le_mul_of_nonneg_left
        (seminorm_sum_smul_le (isSeminorm_enorm sc N0 gd) Finset.univ v σ) (supNorm_nonneg gd)

/-- The law of a finite family of smeared fields under a limit functional. -/
structure IsLaw (sc : Scale) (N0 : ℕ) (gd : DensityFn) (S : Alg →ₗ[ℂ] ℂ) {n : ℕ} (σ : Fin n → T)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) : Prop where
  prob : IsProbabilityMeasure ν
  char : ∀ t, charFun ν t = S (basisE (∑ j, t j • σ j))
  exp : ∀ v : EuclideanSpace ℝ (Fin n), Integrable (fun x => Real.exp ⟪x, v⟫) ν ∧
    ∫ x, Real.exp ⟪x, v⟫ ∂ν ≤ expBound sc N0 gd σ v

theorem continuousAt_gen (hω : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N))
    (hS : IsLimitFunctional sc N0 gd ω Nm S) {n : ℕ} (σ : Fin n → T) :
    ContinuousAt (fun t : EuclideanSpace ℝ (Fin n) => S (basisE (∑ j, t j • σ j))) 0 := by
  have hb (t : EuclideanSpace ℝ (Fin n)) : ‖S (basisE (∑ j, t j • σ j)) -
      S (basisE (∑ j, (0 : EuclideanSpace ℝ (Fin n)) j • σ j))‖ ≤
      ∑ j, |t j| * pairNorm sc N0 gd (σ j) := by
    have h0 : ∑ j, (0 : EuclideanSpace ℝ (Fin n)) j • σ j = 0 := by simp
    rw [h0]
    refine (basis_lipschitz hω hS _ _).trans ?_
    rw [sub_zero]
    exact seminorm_sum_smul_le (isSeminorm_pairNorm sc N0 gd) Finset.univ t σ
  have hlim : Tendsto (fun t : EuclideanSpace ℝ (Fin n) =>
      ∑ j, |t j| * pairNorm sc N0 gd (σ j)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun t : EuclideanSpace ℝ (Fin n) =>
        ∑ j, |t j| * pairNorm sc N0 gd (σ j) := by fun_prop
    have := hc.tendsto 0
    simpa using this
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun t => norm_nonneg _) hb hlim

/-- The laws of a finite family under representing measures converge weakly to the law of the
family under the limit functional. -/
theorem exists_law (hω : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N))
    (hS : IsLimitFunctional sc N0 gd ω Nm S) {μ : ℕ → Measure (Cfg ℤ)}
    (hμ : ∀ N, N0 ≤ N → Represents (c N) (ω N) (μ N)) {n : ℕ} (σ : Fin n → T) :
    ∃ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)), IsLaw sc N0 gd S σ ν ∧
      ∀ f : BoundedContinuousFunction (EuclideanSpace ℝ (Fin n)) ℝ,
        Tendsto (fun m => ∫ x, f (fieldVec sc (Nm m) gd σ x) ∂(μ (Nm m))) atTop
          (𝓝 (∫ x, f x ∂(ν : Measure (EuclideanSpace ℝ (Fin n))))) := by
  have hprob (m : ℕ) : IsProbabilityMeasure (μ (Nm m)) := (hμ _ (hS.le m)).prob
  have hm (m : ℕ) := measurable_fieldVec sc (Nm m) gd σ
  let P (m : ℕ) : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) :=
    ⟨(μ (Nm m)).map (fieldVec sc (Nm m) gd σ),
      Measure.isProbabilityMeasure_map (hm m).aemeasurable⟩
  obtain ⟨ν, hchar, hlim⟩ := exists_limit_law P (continuousAt_gen hω hS σ) fun t => by
    have h := tendsto_basis hS (∑ j, t j • σ j)
    refine h.congr fun m => ?_
    exact (charFun_fieldVec (hμ _ (hS.le m)) sc (Nm m) gd σ t).symm
  have hconv (f : BoundedContinuousFunction (EuclideanSpace ℝ (Fin n)) ℝ) :
      Tendsto (fun m => ∫ x, f (fieldVec sc (Nm m) gd σ x) ∂(μ (Nm m))) atTop
        (𝓝 (∫ x, f x ∂(ν : Measure (EuclideanSpace ℝ (Fin n))))) := by
    have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim f
    refine h.congr fun m => ?_
    exact integral_map (hm m).aemeasurable f.continuous.aestronglyMeasurable
  refine ⟨ν, ⟨ν.2, hchar, fun v => ?_⟩, hconv⟩
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin n) => Real.exp ⟪x, v⟫ := by fun_prop
  refine integrable_of_min_le hcont.measurable (fun x => (Real.exp_pos _).le)
    (Real.exp_pos _).le fun k => ?_
  let f : BoundedContinuousFunction (EuclideanSpace ℝ (Fin n)) ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun x => min (Real.exp ⟪x, v⟫) k)
      (hcont.min continuous_const) k fun x => by
        rw [Real.norm_of_nonneg (le_min (Real.exp_pos _).le (Nat.cast_nonneg k))]
        exact min_le_right _ _
  refine le_of_tendsto' (hconv f) fun m => ?_
  obtain ⟨hint, hle⟩ := exp_fieldVec (hμ _ (hS.le m)) sc (hS.le m) gd σ v
  have h1 : ∫ x, f (fieldVec sc (Nm m) gd σ x) ∂(μ (Nm m)) =
      ∫ x, f x ∂((μ (Nm m)).map (fieldVec sc (Nm m) gd σ)) :=
    (integral_map (hm m).aemeasurable f.continuous.aestronglyMeasurable).symm
  rw [h1]
  have : IsProbabilityMeasure ((μ (Nm m)).map (fieldVec sc (Nm m) gd σ)) :=
    Measure.isProbabilityMeasure_map (hm m).aemeasurable
  refine (integral_mono (f.integrable _) hint fun x => ?_).trans hle
  exact min_le_left _ _

end GGOS.OS

end

end

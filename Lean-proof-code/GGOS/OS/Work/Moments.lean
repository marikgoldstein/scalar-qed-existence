module

public import GGOS.OS.Work.Law

/-!
# Moments of the limit laws, and convergence of the lattice moments
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace GGOS.OS

/-- Exponential moments with the bound of the family `σ`. -/
structure ExpBounded (sc : Scale) (N0 : ℕ) (gd : DensityFn) {n : ℕ} (σ : Fin n → T)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) : Prop where
  prob : IsProbabilityMeasure ν
  exp : ∀ v : EuclideanSpace ℝ (Fin n), Integrable (fun x => Real.exp ⟪x, v⟫) ν ∧
    ∫ x, Real.exp ⟪x, v⟫ ∂ν ≤ expBound sc N0 gd σ v

theorem IsLaw.expBounded {sc : Scale} {N0 : ℕ} {gd : DensityFn} {S : Alg →ₗ[ℂ] ℂ} {n : ℕ}
    {σ : Fin n → T} {ν : Measure (EuclideanSpace ℝ (Fin n))} (h : IsLaw sc N0 gd S σ ν) :
    ExpBounded sc N0 gd σ ν := ⟨h.prob, h.exp⟩

/-- The vector with entries `±a_j`, the sign given by a set of indices. -/
def signed {n : ℕ} (s : Finset (Fin n)) (a : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j => if j ∈ s then a j else -a j

theorem inner_eq_sum {n : ℕ} (x v : EuclideanSpace ℝ (Fin n)) : ⟪x, v⟫ = ∑ j, v j * x j := by
  rw [PiLp.inner_apply]
  rfl

theorem expBound_signed (sc : Scale) (N0 : ℕ) (gd : DensityFn) {n : ℕ} (σ : Fin n → T)
    (s : Finset (Fin n)) (a : Fin n → ℝ) :
    expBound sc N0 gd σ (signed s a) = expBound sc N0 gd σ a := by
  have h (j : Fin n) : |signed s a j| = |a j| := by
    change |if j ∈ s then a j else -a j| = _
    split_ifs
    · rfl
    · exact abs_neg _
  simp only [expBound, h]

theorem exp_abs_le {n : ℕ} (a : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Real.exp (∑ j, a j * |x j|) ≤ ∑ s : Finset (Fin n), Real.exp ⟪x, signed s a⟫ := by
  classical
  have h : Real.exp (∑ j, a j * |x j|) =
      Real.exp ⟪x, signed (Finset.univ.filter fun j => 0 ≤ x j) a⟫ := by
    rw [inner_eq_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    change _ = (if j ∈ Finset.univ.filter (fun j => 0 ≤ x j) then a j else -a j) * x j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with hj
    · rw [abs_of_nonneg hj]
    · rw [abs_of_neg (not_le.mp hj)]
      ring
  rw [h]
  exact Finset.single_le_sum (f := fun s : Finset (Fin n) => Real.exp ⟪x, signed s a⟫)
    (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ _)

namespace ExpBounded

variable {sc : Scale} {N0 : ℕ} {gd : DensityFn} {n : ℕ} {σ : Fin n → T}
  {ν : Measure (EuclideanSpace ℝ (Fin n))}

theorem exp_abs (h : ExpBounded sc N0 gd σ ν) (a : Fin n → ℝ) :
    Integrable (fun x => Real.exp (∑ j, a j * |x j|)) ν ∧
      ∫ x, Real.exp (∑ j, a j * |x j|) ∂ν ≤ 2 ^ n * expBound sc N0 gd σ a := by
  classical
  have hsum : Integrable (fun x => ∑ s : Finset (Fin n), Real.exp ⟪x, signed s a⟫) ν :=
    integrable_finsetSum _ fun s _ => (h.exp (signed s a)).1
  have hint : Integrable (fun x => Real.exp (∑ j, a j * |x j|)) ν :=
    Integrable.mono' hsum (by fun_prop) (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact exp_abs_le a x)
  refine ⟨hint, (integral_mono hint hsum (exp_abs_le a)).trans ?_⟩
  rw [integral_finsetSum _ fun s _ => (h.exp (signed s a)).1]
  calc ∑ s : Finset (Fin n), ∫ x, Real.exp ⟪x, signed s a⟫ ∂ν
      ≤ ∑ _s : Finset (Fin n), expBound sc N0 gd σ a :=
        Finset.sum_le_sum fun s _ => ((h.exp (signed s a)).2).trans_eq (expBound_signed sc N0 gd σ s a)
    _ = 2 ^ n * expBound sc N0 gd σ a := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- Products of powers are dominated by the exponential. -/
theorem integrable_of_le_exp (h : ExpBounded sc N0 gd σ ν) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Continuous f) (C : ℝ) (a : Fin n → ℝ)
    (hle : ∀ x, |f x| ≤ C * Real.exp (∑ j, a j * |x j|)) : Integrable f ν :=
  Integrable.mono' ((h.exp_abs a).1.const_mul C) hf.aestronglyMeasurable
    (Eventually.of_forall hle)

theorem norm_le_sum (x : EuclideanSpace ℝ (Fin n)) : ‖x‖ ≤ ∑ j, 1 * |x j| := by
  have h := EuclideanSpace.norm_eq x
  have hs : ∑ j, ‖x j‖ ^ 2 ≤ (∑ j, |x j|) ^ 2 := by
    have := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun j => |x j|)
      fun j _ => abs_nonneg _
    simpa only [Real.norm_eq_abs] using this
  simp only [one_mul]
  rw [h]
  exact Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg fun j _ => abs_nonneg _, hs⟩

theorem memLp (h : ExpBounded sc N0 gd σ ν) (k : ℕ) : MemLp id k ν := by
  have := h.prob
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using memLp_zero_iff_aestronglyMeasurable.mpr
      (continuous_id.aestronglyMeasurable (μ := ν))
  · refine (integrable_norm_rpow_iff continuous_id.aestronglyMeasurable
      (by simpa using hk.ne') (ENNReal.natCast_ne_top k)).mp ?_
    simp only [ENNReal.toReal_natCast, Real.rpow_natCast, id_eq]
    refine h.integrable_of_le_exp (by fun_prop) k.factorial (fun _ => 1) fun x => ?_
    rw [abs_of_nonneg (by positivity)]
    have h1 := Real.pow_div_factorial_le_exp ‖x‖ (norm_nonneg x) k
    rw [div_le_iff₀ (by positivity)] at h1
    refine h1.trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (norm_le_sum x)) (by positivity)

/-- The product of the coordinates over a map of index sets, and its square. -/
theorem prod_bound {m : ℕ} (q : Fin m → Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    |∏ i, x (q i)| ≤ Real.exp (∑ j, (m : ℝ) * |x j|) := by
  rw [Finset.abs_prod]
  have h1 (i : Fin m) : |x (q i)| ≤ Real.exp (∑ j, |x j|) := by
    have h2 : |x (q i)| ≤ ∑ j, |x j| :=
      Finset.single_le_sum (f := fun j => |x j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
    exact h2.trans ((by linarith : ∑ j, |x j| ≤ ∑ j, |x j| + 1).trans (Real.add_one_le_exp _))
  calc ∏ i, |x (q i)| ≤ ∏ _i : Fin m, Real.exp (∑ j, |x j|) :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => h1 i
    _ = Real.exp (∑ j, (m : ℝ) * |x j|) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul,
          Finset.mul_sum]

theorem integrable_prod (h : ExpBounded sc N0 gd σ ν) {m : ℕ} (q : Fin m → Fin n) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => ∏ i, x (q i)) ν :=
  h.integrable_of_le_exp (by fun_prop) 1 (fun _ => m) fun x => by
    rw [one_mul]
    exact prod_bound q x

theorem sq_prod_bound (h : ExpBounded sc N0 gd σ ν) {m : ℕ} (q : Fin m → Fin n) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => (∏ i, x (q i)) ^ 2) ν ∧
      ∫ x, (∏ i, x (q i)) ^ 2 ∂ν ≤ 2 ^ n * expBound sc N0 gd σ fun _ => 2 * m := by
  have hb (x : EuclideanSpace ℝ (Fin n)) :
      (∏ i, x (q i)) ^ 2 ≤ Real.exp (∑ j, (2 * m : ℝ) * |x j|) := by
    have h1 := prod_bound q x
    have h2 : (∏ i, x (q i)) ^ 2 = |∏ i, x (q i)| ^ 2 := (sq_abs _).symm
    rw [h2]
    refine (pow_le_pow_left₀ (abs_nonneg _) h1 2).trans_eq ?_
    rw [← Real.exp_nat_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hexp := h.exp_abs fun _ => (2 * m : ℝ)
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin n) => (∏ i, x (q i)) ^ 2) ν :=
    h.integrable_of_le_exp (by fun_prop) 1 (fun _ => 2 * m) fun x => by
      rw [one_mul, abs_of_nonneg (sq_nonneg _)]
      exact hb x
  exact ⟨hint, (integral_mono hint hexp.1 hb).trans hexp.2⟩

end ExpBounded

/-! ### Convergence of moments -/

/-- The truncation of a real number at `±K`. -/
def trunc (K r : ℝ) : ℝ := max (-K) (min K r)

theorem continuous_trunc (K : ℝ) : Continuous (trunc K) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem abs_trunc_le {K : ℝ} (hK : 0 < K) (r : ℝ) : |trunc K r| ≤ K := by
  unfold trunc
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem abs_sub_trunc_le {K : ℝ} (hK : 0 < K) (r : ℝ) : |r - trunc K r| ≤ r ^ 2 / K := by
  by_cases hr : |r| ≤ K
  · obtain ⟨h1, h2⟩ := abs_le.mp hr
    have : trunc K r = r := by
      unfold trunc
      rw [min_eq_right h2, max_eq_right h1]
    rw [this, sub_self, abs_zero]
    positivity
  · have hr' := not_le.mp hr
    have h3 : |r - trunc K r| ≤ |r| := by
      unfold trunc
      rcases le_total 0 r with h0 | h0
      · rw [abs_of_nonneg h0] at hr' ⊢
        rw [min_eq_left hr'.le, max_eq_right (by linarith), abs_of_nonneg (by linarith)]
        linarith
      · rw [abs_of_nonpos h0] at hr' ⊢
        rw [min_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonpos (by linarith)]
        linarith
    refine h3.trans ?_
    rw [le_div_iff₀ hK, ← sq_abs, pow_two]
    exact mul_le_mul_of_nonneg_left hr'.le (abs_nonneg r)

theorem integrable_of_sq {Ω : Type*} [MeasurableSpace Ω] {κ : Measure Ω} [IsProbabilityMeasure κ]
    {Y : Ω → ℝ} (hY : Measurable Y) (hY2 : Integrable (fun x => Y x ^ 2) κ) : Integrable Y κ :=
  Integrable.mono' (hY2.add (integrable_const 1)) hY.aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, Pi.add_apply, ← sq_abs]
      nlinarith [sq_nonneg (|Y x| - 1), abs_nonneg (Y x)])

theorem trunc_error {Ω : Type*} [MeasurableSpace Ω] {κ : Measure Ω} [IsProbabilityMeasure κ]
    {Y : Ω → ℝ} (hY : Measurable Y) (hY2 : Integrable (fun x => Y x ^ 2) κ) {C : ℝ}
    (hYC : ∫ x, Y x ^ 2 ∂κ ≤ C) {K : ℝ} (hK : 0 < K) :
    |∫ x, Y x ∂κ - ∫ x, trunc K (Y x) ∂κ| ≤ C / K := by
  have h1 := integrable_of_sq hY hY2
  have h2 : Integrable (fun x => trunc K (Y x)) κ :=
    Integrable.mono' (integrable_const K) ((continuous_trunc K).measurable.comp hY).aestronglyMeasurable
      (Eventually.of_forall fun x => abs_trunc_le hK _)
  rw [← integral_sub h1 h2]
  calc |∫ x, (Y x - trunc K (Y x)) ∂κ| ≤ ∫ x, |Y x - trunc K (Y x)| ∂κ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, Y x ^ 2 / K ∂κ :=
        integral_mono (h1.sub h2).abs (hY2.div_const K) fun x => abs_sub_trunc_le hK _
    _ = (∫ x, Y x ^ 2 ∂κ) / K := integral_div _ _
    _ ≤ C / K := div_le_div_of_nonneg_right hYC hK.le

/-- Weak convergence and uniformly bounded second moments of a continuous function give the
convergence of its integrals. -/
theorem tendsto_integral_of_sq {Ω : Type*} [MeasurableSpace Ω] {E : Type*}
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] (μ : ℕ → Measure Ω)
    [∀ m, IsProbabilityMeasure (μ m)] (X : ℕ → Ω → E) (hX : ∀ m, Measurable (X m))
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hconv : ∀ f : BoundedContinuousFunction E ℝ,
      Tendsto (fun m => ∫ x, f (X m x) ∂(μ m)) atTop (𝓝 (∫ x, f x ∂ν)))
    {P : E → ℝ} (hP : Continuous P) {C : ℝ}
    (h2 : ∀ m, Integrable (fun x => P (X m x) ^ 2) (μ m) ∧ ∫ x, P (X m x) ^ 2 ∂(μ m) ≤ C)
    (h2ν : Integrable (fun x => P x ^ 2) ν ∧ ∫ x, P x ^ 2 ∂ν ≤ C) :
    Tendsto (fun m => ∫ x, P (X m x) ∂(μ m)) atTop (𝓝 (∫ x, P x ∂ν)) := by
  have hC : 0 ≤ C := (integral_nonneg fun x => sq_nonneg _).trans h2ν.2
  rw [Metric.tendsto_atTop]
  intro ε hε
  let K : ℝ := 4 * C / ε + 1
  have hK : 0 < K := by positivity
  have hCK : C / K < ε / 3 := by
    rw [div_lt_iff₀ hK]
    have : ε / 3 * K = 4 * C / 3 + ε / 3 := by
      simp only [K]
      field_simp
    rw [this]
    linarith
  let f : BoundedContinuousFunction E ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun x => trunc K (P x))
      ((continuous_trunc K).comp hP) K fun x => abs_trunc_le hK _
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp (hconv f) (ε / 3) (by linarith)
  refine ⟨M, fun m hm => ?_⟩
  have e1 := trunc_error (κ := μ m) (Y := fun x => P (X m x)) (hP.measurable.comp (hX m)) (h2 m).1
    (h2 m).2 hK
  have e2 := trunc_error (κ := ν) (Y := P) hP.measurable h2ν.1 h2ν.2 hK
  have e3 := hM m hm
  rw [Real.dist_eq] at e3 ⊢
  have e4 : |∫ x, trunc K (P (X m x)) ∂(μ m) - ∫ x, trunc K (P x) ∂ν| < ε / 3 := e3
  rw [abs_lt] at e4 ⊢
  rw [abs_le] at e1 e2
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e4.1, e4.2]

end GGOS.OS

end

end

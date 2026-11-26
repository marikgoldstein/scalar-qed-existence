module

public import GGOS.Frozen.Defs.TorusState

/-!
# Bounds for the unnormalised torus measure
-/

public section

open MeasureTheory Real Set

namespace GGOS.Work.TorusMass

/-- Completing the square in the squared radius gives an integrable Gaussian majorant. -/
theorem integrable_siteFactor (c : Coeffs) : Integrable (siteFactor c) := by
  let b := 1 - c.δm / 2
  let t := b / (2 * c.lam)
  let C := c.lam * t ^ 2 + b * c.ρ0 ^ 2
  have ht : 2 * c.lam * t = b := by
    dsimp [t]
    field_simp [c.lam_pos.ne']
  have hexp (x : ℝ) :
      -(c.lam * (x ^ 2 - c.ρ0 ^ 2) ^ 2) - 1 / 2 * c.δm * x ^ 2 ≤ C - x ^ 2 := by
    let z := x ^ 2 - c.ρ0 ^ 2
    calc
      _ = -c.lam * z ^ 2 + b * z + b * c.ρ0 ^ 2 - x ^ 2 := by dsimp [b, z]; ring
      _ ≤ C - x ^ 2 := by
        dsimp only [C]
        rw [← ht]
        nlinarith only [mul_nonneg c.lam_pos.le (sq_nonneg (z - t))]
  have hg : Integrable (fun x : ℝ => x * exp (-(x ^ 2))) := by
    simpa only [neg_one_mul] using integrable_mul_exp_neg_mul_sq zero_lt_one
  refine ((hg.comp_add_left c.ρ0).norm.mul_const (exp C)).mono' ?_ (ae_of_all _ fun r => ?_)
  · unfold siteFactor
    fun_prop
  · let x := c.ρ0 + r
    change ‖x * exp _ * exp _‖ ≤ ‖x * exp (-(x ^ 2))‖ * exp C
    simp only [norm_mul, Real.norm_of_nonneg (exp_pos _).le, mul_assoc, ← exp_add]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg x)
    apply exp_le_exp.mpr
    linarith only [hexp x]

/-- A product of summable one-coordinate factors is summable over integer configurations. -/
private theorem summable_prod_int {ι : Type*} [Fintype ι] {f : ℤ → ℝ} (hf : Summable f) :
    Summable (fun m : ι → ℤ => ∏ i, f (m i)) := by
  have hcount : (Measure.pi fun _ : ι => (Measure.count : Measure ℤ)) = Measure.count := by
    apply Measure.ext_of_singleton
    simp
  have hprod := Integrable.fintype_prod (ι := ι) (f := fun _ => f)
    (μ := fun _ => Measure.count) (fun _ => integrable_count_iff.mpr hf.norm)
  rw [hcount, integrable_count_iff] at hprod
  exact hprod.of_norm

private theorem summable_int_gaussian {a : ℝ} (ha : 0 < a) :
    Summable (fun k : ℤ => exp (-a * (k : ℝ) ^ 2)) := by
  have h := summable_pow_mul_jacobiTheta₂_term_bound 0 (div_pos ha pi_pos) 0
  refine h.congr fun k => ?_
  simp only [pow_zero, one_mul, mul_zero, zero_mul, sub_zero]
  congr 1
  field_simp [pi_ne_zero]

private theorem abs_dBond_le {s : Side} {a : ℝ} {B : Bond (ZMod s.n) → ℝ}
    (hB : ∀ b, B b ∈ Ioc (-a) a) (p : Plaq (ZMod s.n)) : |dBond B p| ≤ 4 * a := by
  have hb (b) : |B b| ≤ a := abs_le.mpr ⟨(hB b).1.le, (hB b).2⟩
  unfold dBond
  calc
    _ ≤ (|B _| + |B _| + |B _|) + |B _| := by
      grw [abs_sub, abs_sub, abs_add_le]
    _ ≤ a + a + a + a := by gcongr <;> apply hb
    _ = 4 * a := by ring

/-- A summable majorant for the plaquette products, uniform on the bond box. -/
private theorem exists_summable_curv_bound (s : Side) (c : Coeffs) :
    ∃ G : (Plaq (ZMod s.n) → ℤ) → ℝ, Summable G ∧
      ∀ (B : Bond (ZMod s.n) → ℝ), (∀ b, B b ∈ Ioc (-(π / c.γ)) (π / c.γ)) →
      ∀ m, (∏ p, exp (-(curv c B m p) ^ 2 / 2)) ≤ G m := by
  let a := π / c.γ
  let g (k : ℤ) := exp ((4 * a) ^ 2 / 2) * exp (-(a ^ 2) * (k : ℝ) ^ 2)
  have ha : 0 < a := div_pos pi_pos c.γ_pos
  have hg : Summable g := (summable_int_gaussian (sq_pos_of_pos ha)).mul_left _
  refine ⟨_, summable_prod_int (ι := Plaq (ZMod s.n)) hg, fun B hB m => ?_⟩
  apply Finset.prod_le_prod (fun _ _ => (exp_pos _).le)
  intro p _
  obtain ⟨hlo, hhi⟩ := abs_le.mp (abs_dBond_le hB p)
  have hd : (dBond B p) ^ 2 ≤ (4 * a) ^ 2 := sq_le_sq' hlo hhi
  have hcurv : curv c B m p = dBond B p + 2 * a * (m p : ℝ) := by
    dsimp [curv, a]
    ring
  dsimp only [g]
  rw [hcurv, ← exp_add, exp_le_exp]
  nlinarith only [hd, sq_nonneg (dBond B p + a * (m p : ℝ))]

/-- Removing the hopping factors leaves a product of a site density and a summable flux bound. -/
theorem exists_summable_weight_bound (s : Side) (c : Coeffs) :
    ∃ G : (Plaq (ZMod s.n) → ℤ) → ℝ, Summable G ∧
      ∀ r B, (∀ b, B b ∈ Ioc (-(π / c.γ)) (π / c.γ)) →
      ∀ m, weight s c r B m ≤ |∏ i, siteFactor c (r i)| * G m := by
  obtain ⟨G, hsum, hG⟩ := exists_summable_curv_bound s c
  refine ⟨G, hsum, fun r B hB m => ?_⟩
  let H (b : Bond (ZMod s.n)) := hop c (r b.1) (r (b.1 + unitVec (ZMod s.n) b.2)) (B b)
  have hH (b) : 0 ≤ H b := (exp_pos _).le
  have hH_one : (∏ b, H b) ≤ 1 := by
    apply Finset.prod_le_one (fun b _ => hH b)
    intro b _
    apply exp_le_one_iff.mpr
    exact neg_nonpos.mpr (mul_nonneg (mul_nonneg (by norm_num) c.κ_nonneg) (sq_nonneg _))
  have hsites : (∏ i, siteFactor c (r i)) * (∏ b, H b) ≤ |∏ i, siteFactor c (r i)| := by
    simpa only [mul_one] using mul_le_mul (le_abs_self _) hH_one
      (Finset.prod_nonneg fun b _ => hH b) (abs_nonneg _)
  exact mul_le_mul hsites (hG B hB m) (Finset.prod_nonneg fun _ _ => (exp_pos _).le)
    (abs_nonneg _)

/-- The total bond mass is the interval length raised to the number of bonds. -/
theorem bondMeasure_univ (s : Side) (c : Coeffs) :
    bondMeasure s c univ =
      ENNReal.ofReal (2 * (π / c.γ)) ^ Fintype.card (Bond (ZMod s.n)) := by
  simp only [bondMeasure, Measure.pi_univ, Measure.restrict_apply_univ, Real.volume_Ioc,
    Finset.prod_const, Finset.card_univ, sub_neg_eq_add, two_mul]

/-- On the whole configuration space the curvature pushforward preserves each sector's mass. -/
theorem torusMeasure_univ_eq (s : Side) (c : Coeffs) :
    torusMeasure s c univ = ∑' m : {m : Plaq (ZMod s.n) → ℤ // IsClosedForm m},
      ∫⁻ x, ENNReal.ofReal (weight s c x.1 x.2 m.1) ∂(siteMeasure s c).prod (bondMeasure s c) := by
  rw [torusMeasure, Measure.sum_apply _ MeasurableSet.univ]
  refine tsum_congr fun m => ?_
  have hmap : Measurable (fun x : (Site (ZMod s.n) → ℝ) × (Bond (ZMod s.n) → ℝ) =>
      (curv c x.2 m.1, x.1)) := by
    unfold curv dBond
    fun_prop
  rw [Measure.map_apply hmap MeasurableSet.univ, preimage_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]

end GGOS.Work.TorusMass

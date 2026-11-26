module

public import Mathlib
public import GGOS.Frozen.Defs.TorusState
public import GGOS.Frozen.Defs.Phi
public import GGOS.Frozen.Defs.Per
public import GGOS.Frozen.Defs.Embeds
public import GGOS.Frozen.Defs.PairNorm
public import GGOS.Frozen.PairNorm
public import GGOS.Work.TorusMass

public section

open MeasureTheory Real

/-!
# The torus estimate of [GG-OS] Proposition 4.2 from the Gaussian second-moment bound
-/

namespace GGOS.Work

private lemma eps_pos' (sc : Scale) (N : ℕ) : 0 < eps sc N :=
  div_pos sc.a0_pos (by positivity)

private lemma rpow_three_halves_sq {ε : ℝ} (hε : 0 ≤ ε) :
    (ε ^ (3 / 2 : ℝ)) ^ 2 = ε ^ 3 := by
  rw [← Real.rpow_natCast (ε ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul hε]
  have h32 : (3 / 2 : ℝ) * ((2 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
  rw [h32, Real.rpow_natCast]

private lemma sq_sum_eq_sum_sq_of_inj {α : Type*} (F : Finset α) (b : α → ℝ)
    (hF : ∀ y ∈ F, ∀ z ∈ F, b y ≠ 0 → b z ≠ 0 → y = z) :
    (∑ y ∈ F, b y) ^ 2 = ∑ y ∈ F, b y ^ 2 := by
  by_cases h : ∃ x, x ∈ F ∧ b x ≠ 0
  · rcases h with ⟨x, hx, hbx⟩
    have hzero : ∀ y ∈ F, y ≠ x → b y = 0 := by
      intro y hy hyx
      by_contra hby
      exact hyx (hF y hy x hx hby hbx)
    have h1 : ∑ y ∈ F, b y = b x :=
      Finset.sum_eq_single x hzero (fun hnot => absurd hx hnot)
    have h2 : ∑ y ∈ F, b y ^ 2 = b x ^ 2 :=
      Finset.sum_eq_single x
        (fun y hy hyx => by rw [hzero y hy hyx]; norm_num)
        (fun hnot => absurd hx hnot)
    rw [h1, h2]
  · have hzero : ∀ y ∈ F, b y = 0 := by
      intro y hy
      by_contra hby
      exact h ⟨y, hy, hby⟩
    have h1 : ∑ y ∈ F, b y = 0 := Finset.sum_eq_zero hzero
    have h2 : ∑ y ∈ F, b y ^ 2 = 0 :=
      Finset.sum_eq_zero fun y hy => by rw [hzero y hy]; norm_num
    rw [h1, h2]
    norm_num

private noncomputable def embedBox (ε : ℝ) (c0 : E3) (n : ℕ) : Finset (Site ℤ) :=
  Fintype.piFinset fun i : Fin 3 =>
    Finset.Icc ⌈(c0 i - (n : ℝ) * ε / 2) / ε⌉ ⌊(c0 i + (n : ℝ) * ε / 2) / ε⌋

private lemma mem_embedBox {ε : ℝ} (hε : 0 < ε) {c0 : E3} {n : ℕ} {x : Site ℤ}
    (hx : ∀ i : Fin 3, c0 i - (n : ℝ) * ε / 2 < ε * (x i : ℝ) ∧
      ε * (x i : ℝ) < c0 i + (n : ℝ) * ε / 2) :
    x ∈ embedBox ε c0 n := by
  apply Fintype.mem_piFinset.mpr
  intro i
  have h1 : (c0 i - (n : ℝ) * ε / 2) / ε ≤ (x i : ℝ) :=
    (div_le_iff₀ hε).mpr (by linarith [(hx i).1, mul_comm ε (x i : ℝ), mul_comm (n : ℝ) ε])
  have h2 : (x i : ℝ) ≤ (c0 i + (n : ℝ) * ε / 2) / ε :=
    (le_div_iff₀ hε).mpr (by linarith [(hx i).2, mul_comm ε (x i : ℝ), mul_comm (n : ℝ) ε])
  exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr h1, Int.le_floor.mpr h2⟩

private lemma castSite_eq_imp_eq {ε : ℝ} (hε : 0 < ε) {c0 : E3} {n : ℕ} {x y : Site ℤ}
    (hx : ∀ i : Fin 3, c0 i - (n : ℝ) * ε / 2 < ε * (x i : ℝ) ∧
      ε * (x i : ℝ) < c0 i + (n : ℝ) * ε / 2)
    (hy : ∀ i : Fin 3, c0 i - (n : ℝ) * ε / 2 < ε * (y i : ℝ) ∧
      ε * (y i : ℝ) < c0 i + (n : ℝ) * ε / 2)
    (hcast : castSite n x = castSite n y) : x = y := by
  funext i
  have hmod : ((x i : ℤ) : ZMod n) = ((y i : ℤ) : ZMod n) := congrFun hcast i
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hmod
  obtain ⟨k, hk⟩ := hmod
  have hne : (n : ℝ) * ε = ε * (n : ℝ) := mul_comm _ _
  have hdiff_lo : ε * (-(n : ℝ)) < ε * ((y i : ℝ) - (x i : ℝ)) := by
    have h1 : ε * (-(n : ℝ)) = -(ε * (n : ℝ)) := mul_neg _ _
    have h2 : ε * ((y i : ℝ) - (x i : ℝ)) = ε * (y i : ℝ) - ε * (x i : ℝ) := mul_sub _ _ _
    linarith [(hx i).2, (hy i).1, hne, h1, h2]
  have hdiff_hi : ε * ((y i : ℝ) - (x i : ℝ)) < ε * (n : ℝ) := by
    have h2 : ε * ((y i : ℝ) - (x i : ℝ)) = ε * (y i : ℝ) - ε * (x i : ℝ) := mul_sub _ _ _
    linarith [(hx i).1, (hy i).2, hne, h2]
  have hlo_real : ((-(n : ℤ) : ℤ) : ℝ) < ((y i - x i : ℤ) : ℝ) := by
    by_contra hge
    have hle : ((y i - x i : ℤ) : ℝ) ≤ ((-(n : ℤ) : ℤ) : ℝ) := le_of_not_gt hge
    have hm := mul_le_mul_of_nonneg_left hle hε.le
    simp only [Int.cast_neg, Int.cast_natCast, Int.cast_sub] at hm
    linarith [hdiff_lo, hm]
  have hhi_real : ((y i - x i : ℤ) : ℝ) < (((n : ℤ) : ℤ) : ℝ) := by
    by_contra hge
    have hle : (((n : ℤ) : ℤ) : ℝ) ≤ ((y i - x i : ℤ) : ℝ) := le_of_not_gt hge
    have hm := mul_le_mul_of_nonneg_left hle hε.le
    simp only [Int.cast_natCast, Int.cast_sub] at hm
    linarith [hdiff_hi, hm]
  have hlo_int : -(n : ℤ) < y i - x i := Int.cast_lt.mp hlo_real
  have hhi_int : y i - x i < (n : ℤ) := Int.cast_lt.mp hhi_real
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  have hk_gt : ¬ k ≤ -1 := by
    intro hle
    have hm := mul_le_mul_of_nonneg_left hle hn0
    rw [mul_neg_one, ← hk] at hm
    omega
  have hk_lt : ¬ 1 ≤ k := by
    intro hge
    have hm := mul_le_mul_of_nonneg_left hge hn0
    rw [mul_one, ← hk] at hm
    omega
  have hk0 : k = 0 := by omega
  rw [hk0, mul_zero] at hk
  omega

private lemma sq_add_le_weighted {r b : ℝ} (hr : 0 < r) (hb : 0 < b) (x y : ℝ) :
    (x + y) ^ 2 ≤ ((r + b) / r) * x ^ 2 + ((r + b) / b) * y ^ 2 := by
  have h1 : r * ((r + b) / r) = r + b := mul_div_cancel₀ (r + b) hr.ne'
  have h2 : b * ((r + b) / b) = r + b := mul_div_cancel₀ (r + b) hb.ne'
  have hid : r * b * (((r + b) / r) * x ^ 2 + ((r + b) / b) * y ^ 2 - (x + y) ^ 2) =
      (b * x - r * y) ^ 2 := by
    calc r * b * (((r + b) / r) * x ^ 2 + ((r + b) / b) * y ^ 2 - (x + y) ^ 2)
        = b * (r * ((r + b) / r)) * x ^ 2 + r * (b * ((r + b) / b)) * y ^ 2 -
            r * b * (x + y) ^ 2 := by ring
      _ = b * (r + b) * x ^ 2 + r * (r + b) * y ^ 2 - r * b * (x + y) ^ 2 := by rw [h1, h2]
      _ = (b * x - r * y) ^ 2 := by ring
  by_contra hlt
  have hneg : ((r + b) / r) * x ^ 2 + ((r + b) / b) * y ^ 2 - (x + y) ^ 2 < 0 := by
    linarith [hlt]
  have hmul : r * b * (((r + b) / r) * x ^ 2 + ((r + b) / b) * y ^ 2 - (x + y) ^ 2) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos hr hb) hneg
  linarith [hid, hmul, sq_nonneg (b * x - r * y)]

private lemma integrable_and_sqrt_integral_add_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX_meas : Measurable X) (hY_meas : Measurable Y)
    (hX2 : Integrable (fun ω => X ω ^ 2) μ)
    {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hintX : ∫ ω, X ω ^ 2 ∂μ ≤ R ^ 2) (hY_abs : ∀ ω, |Y ω| ≤ B) :
    Integrable (fun ω => (X ω + Y ω) ^ 2) μ ∧
      Real.sqrt (∫ ω, (X ω + Y ω) ^ 2 ∂μ) ≤ R + B := by
  have hY_sq : ∀ ω, Y ω ^ 2 ≤ B ^ 2 := by
    intro ω
    have h := abs_le.mp (hY_abs ω)
    exact sq_le_sq' h.1 h.2
  have hY2 : Integrable (fun ω => Y ω ^ 2) μ :=
    Integrable.mono' (integrable_const (B ^ 2))
      ((continuous_pow 2).comp_aestronglyMeasurable hY_meas.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (sq_nonneg (Y ω))]
        exact hY_sq ω)
  have hXY_meas : Measurable (fun ω => X ω + Y ω) := hX_meas.fun_add hY_meas
  have hXY2 : Integrable (fun ω => (X ω + Y ω) ^ 2) μ :=
    Integrable.mono' ((hX2.const_mul (2 : ℝ)).fun_add (hY2.const_mul (2 : ℝ)))
      ((continuous_pow 2).comp_aestronglyMeasurable hXY_meas.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (sq_nonneg (X ω + Y ω))]
        have hsub : 0 ≤ (X ω - Y ω) ^ 2 := sq_nonneg (X ω - Y ω)
        have hid : (2 : ℝ) * X ω ^ 2 + (2 : ℝ) * Y ω ^ 2 - (X ω + Y ω) ^ 2 =
            (X ω - Y ω) ^ 2 := by ring
        linarith [hsub, hid])
  refine ⟨hXY2, ?_⟩
  have hintY : ∫ ω, Y ω ^ 2 ∂μ ≤ B ^ 2 := by
    calc ∫ ω, Y ω ^ 2 ∂μ
        ≤ ∫ _ : Ω, B ^ 2 ∂μ := integral_mono hY2 (integrable_const (B ^ 2)) hY_sq
      _ = B ^ 2 := integral_eq_const (Filter.Eventually.of_forall fun _ => rfl)
  have hdelta : ∀ δ : ℝ, 0 < δ → Real.sqrt (∫ ω, (X ω + Y ω) ^ 2 ∂μ) ≤ R + B + 2 * δ := by
    intro δ hδ
    let r : ℝ := R + δ
    let b : ℝ := B + δ
    have hr : 0 < r := by dsimp only [r]; linarith [hR, hδ]
    have hb : 0 < b := by dsimp only [b]; linarith [hB, hδ]
    have hcr : 0 ≤ (r + b) / r := div_nonneg (by linarith [hr, hb]) hr.le
    have hcb : 0 ≤ (r + b) / b := div_nonneg (by linarith [hr, hb]) hb.le
    have hXr : ∫ ω, X ω ^ 2 ∂μ ≤ r ^ 2 := by
      have h1 : r ^ 2 - R ^ 2 = δ * (2 * R + δ) := by dsimp only [r]; ring
      have h2 : 0 ≤ δ * (2 * R + δ) := mul_nonneg hδ.le (by linarith [hR, hδ])
      have hRr : R ^ 2 ≤ r ^ 2 := by linarith [h1, h2]
      exact hintX.trans hRr
    have hYb : ∫ ω, Y ω ^ 2 ∂μ ≤ b ^ 2 := by
      have h1 : b ^ 2 - B ^ 2 = δ * (2 * B + δ) := by dsimp only [b]; ring
      have h2 : 0 ≤ δ * (2 * B + δ) := mul_nonneg hδ.le (by linarith [hB, hδ])
      have hBb : B ^ 2 ≤ b ^ 2 := by linarith [h1, h2]
      exact hintY.trans hBb
    have hdom_int : Integrable
        (fun ω => ((r + b) / r) * X ω ^ 2 + ((r + b) / b) * Y ω ^ 2) μ :=
      (hX2.const_mul ((r + b) / r)).fun_add (hY2.const_mul ((r + b) / b))
    have hintXY : ∫ ω, (X ω + Y ω) ^ 2 ∂μ ≤ (r + b) ^ 2 := by
      calc ∫ ω, (X ω + Y ω) ^ 2 ∂μ
          ≤ ∫ ω, (((r + b) / r) * X ω ^ 2 + ((r + b) / b) * Y ω ^ 2) ∂μ :=
            integral_mono hXY2 hdom_int (fun ω => sq_add_le_weighted hr hb (X ω) (Y ω))
        _ = ((r + b) / r) * (∫ ω, X ω ^ 2 ∂μ) + ((r + b) / b) * (∫ ω, Y ω ^ 2 ∂μ) := by
            rw [integral_add (hX2.const_mul ((r + b) / r)) (hY2.const_mul ((r + b) / b)),
              integral_const_mul, integral_const_mul]
        _ ≤ ((r + b) / r) * r ^ 2 + ((r + b) / b) * b ^ 2 :=
            add_le_add (mul_le_mul_of_nonneg_left hXr hcr) (mul_le_mul_of_nonneg_left hYb hcb)
        _ = (r * ((r + b) / r)) * r + (b * ((r + b) / b)) * b := by ring
        _ = (r + b) * r + (r + b) * b := by
            rw [mul_div_cancel₀ (r + b) hr.ne', mul_div_cancel₀ (r + b) hb.ne']
        _ = (r + b) ^ 2 := by ring
    calc Real.sqrt (∫ ω, (X ω + Y ω) ^ 2 ∂μ)
        ≤ Real.sqrt ((r + b) ^ 2) := Real.sqrt_le_sqrt hintXY
      _ = r + b := Real.sqrt_sq (by linarith [hr, hb])
      _ = R + B + 2 * δ := by dsimp only [r, b]; ring
  by_contra hgt
  have hpos : 0 < (Real.sqrt (∫ ω, (X ω + Y ω) ^ 2 ∂μ) - (R + B)) / 4 := by linarith [hgt]
  have hinst := hdelta _ hpos
  linarith [hinst]

/-- [GG-OS] Proposition 4.2 (torus inequality), assuming the second-moment half of Theorem 3.1
(`hmom`, which is a conjunct of `GGOS.gaussian_moments`). -/
theorem torus_estimate_of_second_moment (c : Coeffs) (sc : Scale) (N0 : ℕ) (gd : DensityFn)
    (σ : T) (N : ℕ) (hN : N0 ≤ N) (s : Side) (hemb : Embeds sc N s σ)
    (hmom : ∀ a : Plaq (ZMod s.n) → ℝ,
      Integrable (fun ω : Cfg (ZMod s.n) => (∑ p, a p * ω.1 p) ^ 2) (torusState s c) ∧
        ∫ ω, (∑ p, a p * ω.1 p) ^ 2 ∂(torusState s c) ≤ ∑ p, a p ^ 2) :
    Integrable (fun ω : Cfg (ZMod s.n) => Phi sc N gd σ (per s.n ω) ^ 2) (torusState s c) ∧
      Real.sqrt (∫ ω, Phi sc N gd σ (per s.n ω) ^ 2 ∂(torusState s c)) ≤ pairNorm sc N0 gd σ := by
  haveI : IsProbabilityMeasure (torusState s c) := isProbabilityMeasure_torusState c s
  let ε : ℝ := eps sc N
  have hε : 0 < ε := eps_pos' sc N
  let fp : Plaq ℤ → ℝ := fun p => σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre ε p)
  let hz : Site ℤ → ℝ := fun z => σ.1.2 (sitePos ε z)
  let castPlaq : Plaq ℤ → Plaq (ZMod s.n) := fun p => (castSite s.n p.1, p.2)
  obtain ⟨c0, hplaq, hsite⟩ := hemb
  have hplaq_box : ∀ p : Plaq ℤ, fp p ≠ 0 →
      ∀ i : Fin 3, c0 i - (s.n : ℝ) * ε / 2 < ε * (p.1 i : ℝ) ∧
        ε * (p.1 i : ℝ) < c0 i + (s.n : ℝ) * ε / 2 := by
    intro p hp i
    obtain ⟨hlo, hhi⟩ := hplaq p hp i
    refine ⟨hlo, ?_⟩
    have hnonneg : (0 : ℝ) ≤ if i = p.2.1.1 ∨ i = p.2.1.2 then 1 else 0 := by
      split_ifs <;> norm_num
    have hle : ε * (p.1 i : ℝ) ≤
        ε * ((p.1 i : ℝ) + if i = p.2.1.1 ∨ i = p.2.1.2 then 1 else 0) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hnonneg) hε.le
    exact hle.trans_lt hhi
  have hsite_box : ∀ z : Site ℤ, hz z ≠ 0 →
      ∀ i : Fin 3, c0 i - (s.n : ℝ) * ε / 2 < ε * (z i : ℝ) ∧
        ε * (z i : ℝ) < c0 i + (s.n : ℝ) * ε / 2 := by
    intro z hzz i
    have habs : |ε * (z i : ℝ) - c0 i| < (s.n : ℝ) * ε / 2 := hsite z hzz i
    obtain ⟨h1, h2⟩ := abs_lt.mp habs
    exact ⟨by linarith [h1], by linarith [h2]⟩
  let S : Finset (Site ℤ) := embedBox ε c0 s.n
  let P : Finset (Plaq ℤ) := S ×ˢ Finset.univ
  have hfp_out : ∀ p ∉ P, fp p = 0 := by
    intro p hp
    by_contra hne
    have hmem : p ∈ P :=
      Finset.mem_product.mpr ⟨mem_embedBox hε (hplaq_box p hne), Finset.mem_univ p.2⟩
    exact hp hmem
  have hhz_out : ∀ z ∉ S, hz z = 0 := by
    intro z hzs
    by_contra hne
    exact hzs (mem_embedBox hε (hsite_box z hne))
  have hcast_inj : ∀ p q : Plaq ℤ, fp p ≠ 0 → fp q ≠ 0 → castPlaq p = castPlaq q → p = q := by
    intro p q hp hq heq
    have h1 : castSite s.n p.1 = castSite s.n q.1 := congrArg Prod.fst heq
    have h2 : p.2 = q.2 := by
      have h := congrArg Prod.snd heq
      exact h
    exact Prod.ext (castSite_eq_imp_eq hε (hplaq_box p hp) (hplaq_box q hq) h1) h2
  let b : Plaq ℤ → ℝ := fun p => ε ^ (3 / 2 : ℝ) * fp p
  let a : Plaq (ZMod s.n) → ℝ := fun q => ∑ p ∈ P with castPlaq p = q, b p
  let X : Cfg (ZMod s.n) → ℝ := fun ω => ∑ q : Plaq (ZMod s.n), a q * ω.1 q
  let Y : Cfg (ZMod s.n) → ℝ := fun ω => ε ^ 3 * ∑ z ∈ S, hz z * gd.toFun (ω.2 (castSite s.n z))
  have hPhi_eq : ∀ ω : Cfg (ZMod s.n), Phi sc N gd σ (per s.n ω) = X ω + Y ω := by
    intro ω
    have htsum_p : (∑' p : Plaq ℤ, fp p * (per s.n ω).1 p) = ∑ p ∈ P, fp p * ω.1 (castPlaq p) := by
      have hzero : ∀ p ∉ P, fp p * (per s.n ω).1 p = 0 := by
        intro p hp
        rw [hfp_out p hp, zero_mul]
      exact (hasSum_sum_of_ne_finset_zero hzero).tsum_eq
    have htsum_z : (∑' z : Site ℤ, hz z * gd.toFun ((per s.n ω).2 z)) =
        ∑ z ∈ S, hz z * gd.toFun (ω.2 (castSite s.n z)) := by
      have hzero : ∀ z ∉ S, hz z * gd.toFun ((per s.n ω).2 z) = 0 := by
        intro z hzs
        rw [hhz_out z hzs, zero_mul]
      exact (hasSum_sum_of_ne_finset_zero hzero).tsum_eq
    have hX_sum : ε ^ (3 / 2 : ℝ) * ∑ p ∈ P, fp p * ω.1 (castPlaq p) = X ω := by
      dsimp only [X, a, b]
      calc ε ^ (3 / 2 : ℝ) * ∑ p ∈ P, fp p * ω.1 (castPlaq p)
          = ∑ p ∈ P, (ε ^ (3 / 2 : ℝ) * fp p) * ω.1 (castPlaq p) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun p _ => ?_
            ring
        _ = ∑ q : Plaq (ZMod s.n), ∑ p ∈ P with castPlaq p = q,
              (ε ^ (3 / 2 : ℝ) * fp p) * ω.1 (castPlaq p) :=
            (Finset.sum_fiberwise P castPlaq
              (fun p => (ε ^ (3 / 2 : ℝ) * fp p) * ω.1 (castPlaq p))).symm
        _ = ∑ q : Plaq (ZMod s.n),
              (∑ p ∈ P with castPlaq p = q, ε ^ (3 / 2 : ℝ) * fp p) * ω.1 q := by
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun p hp => ?_
            rw [(Finset.mem_filter.mp hp).2]
    change ε ^ (3 / 2 : ℝ) * (∑' p : Plaq ℤ, fp p * (per s.n ω).1 p) +
        ε ^ 3 * (∑' z : Site ℤ, hz z * gd.toFun ((per s.n ω).2 z)) = X ω + Y ω
    rw [htsum_p, htsum_z, hX_sum]
  have ha_sq : (∑ q : Plaq (ZMod s.n), a q ^ 2) = ε ^ 3 * ∑' p : Plaq ℤ, fp p ^ 2 := by
    have hfib : (∑ q : Plaq (ZMod s.n), a q ^ 2) = ∑ p ∈ P, b p ^ 2 := by
      calc ∑ q : Plaq (ZMod s.n), a q ^ 2
          = ∑ q : Plaq (ZMod s.n), ∑ p ∈ P with castPlaq p = q, b p ^ 2 := by
            refine Finset.sum_congr rfl fun q _ => ?_
            refine sq_sum_eq_sum_sq_of_inj (P.filter fun p => castPlaq p = q) b ?_
            intro p₁ hp₁ p₂ hp₂ hb₁ hb₂
            have hfp₁ : fp p₁ ≠ 0 := fun h0 => hb₁ (by dsimp only [b]; rw [h0, mul_zero])
            have hfp₂ : fp p₂ ≠ 0 := fun h0 => hb₂ (by dsimp only [b]; rw [h0, mul_zero])
            have hc₁ : castPlaq p₁ = q := (Finset.mem_filter.mp hp₁).2
            have hc₂ : castPlaq p₂ = q := (Finset.mem_filter.mp hp₂).2
            exact hcast_inj p₁ p₂ hfp₁ hfp₂ (hc₁.trans hc₂.symm)
        _ = ∑ p ∈ P, b p ^ 2 := Finset.sum_fiberwise P castPlaq (fun p => b p ^ 2)
    have htsum_fp2 : (∑' p : Plaq ℤ, fp p ^ 2) = ∑ p ∈ P, fp p ^ 2 := by
      have hzero : ∀ p ∉ P, fp p ^ 2 = 0 := by
        intro p hp
        rw [hfp_out p hp]
        norm_num
      exact (hasSum_sum_of_ne_finset_zero hzero).tsum_eq
    rw [hfib, htsum_fp2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    dsimp only [b]
    rw [mul_pow, rpow_three_halves_sq hε.le]
  have hbddR : BddAbove (Set.range fun M : {M : ℕ // N0 ≤ M} =>
      Real.sqrt (eps sc M ^ 3 *
        ∑' p : Plaq ℤ, (σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc M) p)) ^ 2)) :=
    (GGOS.pairNorm_finite_seminorm_admissible sc N0 gd).1 σ
  have hrN_le : Real.sqrt (ε ^ 3 * ∑' p : Plaq ℤ, fp p ^ 2) ≤ Rnorm sc N0 σ :=
    le_ciSup hbddR ⟨N, hN⟩
  have hR_nonneg : 0 ≤ Rnorm sc N0 σ := (Real.sqrt_nonneg _).trans hrN_le
  obtain ⟨hX2_int, hX2_mom⟩ := hmom a
  have hX2_le : ∫ ω, X ω ^ 2 ∂(torusState s c) ≤ Rnorm sc N0 σ ^ 2 :=
    (hX2_mom.trans_eq ha_sq).trans ((Real.sqrt_le_left hR_nonneg).mp hrN_le)
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
  have htsum_hz : (∑' z : Site ℤ, |hz z|) = ∑ z ∈ S, |hz z| := by
    have hzero : ∀ z ∉ S, |hz z| = 0 := by
      intro z hzs
      rw [hhz_out z hzs, abs_zero]
    exact (hasSum_sum_of_ne_finset_zero hzero).tsum_eq
  have hE_nonneg : 0 ≤ Enorm sc N0 σ := by
    have h0 : 0 ≤ ε ^ 3 * ∑' z : Site ℤ, |hz z| := by
      rw [htsum_hz]
      exact mul_nonneg (pow_nonneg hε.le 3) (Finset.sum_nonneg fun z _ => abs_nonneg (hz z))
    exact h0.trans heN_le
  have hB_nonneg : 0 ≤ supNorm gd * Enorm sc N0 σ := mul_nonneg hsup_nonneg hE_nonneg
  have hY_abs : ∀ ω : Cfg (ZMod s.n), |Y ω| ≤ supNorm gd * Enorm sc N0 σ := by
    intro ω
    dsimp only [Y]
    calc |ε ^ 3 * ∑ z ∈ S, hz z * gd.toFun (ω.2 (castSite s.n z))|
        = ε ^ 3 * |∑ z ∈ S, hz z * gd.toFun (ω.2 (castSite s.n z))| := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg hε.le 3)]
      _ ≤ ε ^ 3 * ∑ z ∈ S, |hz z * gd.toFun (ω.2 (castSite s.n z))| :=
          mul_le_mul_of_nonneg_left
            (Finset.abs_sum_le_sum_abs _ S) (pow_nonneg hε.le 3)
      _ ≤ ε ^ 3 * ∑ z ∈ S, |hz z| * supNorm gd := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => ?_) (pow_nonneg hε.le 3)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hgd_le _) (abs_nonneg _)
      _ = supNorm gd * (ε ^ 3 * ∑ z ∈ S, |hz z|) := by
          rw [← Finset.sum_mul]
          ring
      _ = supNorm gd * (ε ^ 3 * ∑' z : Site ℤ, |hz z|) := by
          rw [htsum_hz]
      _ ≤ supNorm gd * Enorm sc N0 σ :=
          mul_le_mul_of_nonneg_left heN_le hsup_nonneg
  have hX_meas : Measurable X :=
    Finset.measurable_sum Finset.univ fun q _ =>
      measurable_const.mul ((measurable_pi_apply q).comp measurable_fst)
  have hY_meas : Measurable Y :=
    (Finset.measurable_sum S fun z _ =>
      (gd.measurable.comp ((measurable_pi_apply (castSite s.n z)).comp measurable_snd)).const_mul
        (hz z)).const_mul (ε ^ 3)
  have hmain := integrable_and_sqrt_integral_add_sq_le (torusState s c) hX_meas hY_meas hX2_int
    hR_nonneg hB_nonneg hX2_le hY_abs
  simp_rw [hPhi_eq]
  exact hmain

end GGOS.Work

end

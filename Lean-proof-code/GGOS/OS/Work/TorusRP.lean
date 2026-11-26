module

public import GGOS.OS.Work.TorusReflection

/-!
# Reflection positivity of the torus state: the half weight

The weight is the product of a half weight, which depends on the closed upper half only, and of its
reflection: the factors of the open upper half enter with exponent one, those of the plane with
exponent one half ([GG-OS], proof of Theorem 9.7, site plane).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexOrder

namespace GGOS.OS

/-! ### The closed upper half -/

section Time

variable {n : ℕ} [NeZero n]

theorem val_neg_sub_one (t : ZMod n) : (-t - 1).val = n - 1 - t.val := by
  have ht := ZMod.val_lt t
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have h : -t - 1 = ((n - 1 - t.val : ℕ) : ZMod n) := by
    rw [Nat.cast_sub (by omega : t.val ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n)]
    simp
    ring
  rw [h, ZMod.val_natCast_of_lt (by omega)]

/-- A cell with base site `x` and time extent `δ` lies in the closed upper half. -/
def up (δ : ℕ) (x : Site (ZMod n)) : Prop := (x 2).val + δ ≤ n / 2

omit [NeZero n] in
theorem up_mono {δ δ' : ℕ} (h : δ ≤ δ') {x : Site (ZMod n)} (hx : up δ' x) : up δ x := by
  unfold up at *
  omega

omit [NeZero n] in
theorem up_add_unit {δ : ℕ} {μ : Fin 3} (hμ : μ ≠ 2) {x : Site (ZMod n)} (hx : up δ x) :
    up δ (x + unitVec (ZMod n) μ) := by
  unfold up at *
  simpa [unitVec, Pi.single_eq_of_ne hμ.symm] using hx

theorem up_add_unit_two {x : Site (ZMod n)} (hx : up 1 x) :
    up 0 (x + unitVec (ZMod n) 2) := by
  unfold up at *
  have hlt := ZMod.val_lt (x 2)
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have h : (x + unitVec (ZMod n) 2) 2 = (((x 2).val + 1 : ℕ) : ZMod n) := by
    simp [unitVec]
  rw [h, ZMod.val_natCast_of_lt (by omega)]
  omega

theorem up_cover (hn : Even n) {δ : ℕ} (hδ : δ ≤ 1) (x : Site (ZMod n)) :
    up δ x ∨ up δ (flip (δ : ZMod n) x) := by
  have ht := ZMod.val_lt (x 2)
  obtain ⟨k, hk⟩ := hn
  unfold up
  rw [flip_two]
  interval_cases δ
  · simp only [Nat.cast_zero, sub_zero, add_zero]
    rw [ZMod.neg_val]
    split_ifs <;> omega
  · simp only [Nat.cast_one]
    rw [val_neg_sub_one]
    omega

theorem up_plane (hn : Even n) {δ : ℕ} (hδ : δ ≤ 1) {x : Site (ZMod n)} (h : up δ x)
    (h' : up δ (flip (δ : ZMod n) x)) : δ = 0 ∧ flip (δ : ZMod n) x = x := by
  have ht := ZMod.val_lt (x 2)
  obtain ⟨k, hk⟩ := hn
  unfold up at h h'
  rw [flip_two] at h'
  interval_cases δ
  · refine ⟨rfl, ?_⟩
    simp only [Nat.cast_zero, sub_zero, add_zero] at h h'
    have hx : -x 2 = x 2 := by
      rw [ZMod.neg_val] at h'
      by_cases h0 : x 2 = 0
      · simp [h0]
      · rw [ite_eq_right h0] at h'
        have hv : (x 2).val + (x 2).val = n := by omega
        have : x 2 + x 2 = 0 := by
          have h2 : (((x 2).val + (x 2).val : ℕ) : ZMod n) = ((n : ℕ) : ZMod n) := by rw [hv]
          simpa using h2
        exact neg_eq_of_add_eq_zero_left this
    funext i
    by_cases hi : i = 2
    · subst hi
      simp [flip, hx]
    · simp [flip, Function.update_of_ne hi]
  · simp only [Nat.cast_one] at h'
    rw [val_neg_sub_one] at h'
    omega

end Time

/-- The time extent of a bond. -/
def bExt (μ : Fin 3) : ℕ := if μ = 2 then 1 else 0

/-- The time extent of a plaquette. -/
def pExt (d : Dir2) : ℕ := if d.1.2 = 2 then 1 else 0

theorem bExt_le (μ : Fin 3) : bExt μ ≤ 1 := by unfold bExt; split_ifs <;> omega

theorem pExt_le (d : Dir2) : pExt d ≤ 1 := by unfold pExt; split_ifs <;> omega

theorem bShift_eq {n : ℕ} (μ : Fin 3) : (bShift μ : ZMod n) = ((bExt μ : ℕ) : ZMod n) := by
  unfold bShift bExt
  split_ifs <;> simp

theorem pShift_eq {n : ℕ} (d : Dir2) : (pShift d : ZMod n) = ((pExt d : ℕ) : ZMod n) := by
  unfold pShift pExt
  split_ifs <;> simp

theorem bSign_eq_one {μ : Fin 3} (h : bExt μ = 0) : bSign μ = 1 := by
  unfold bExt at h
  unfold bSign
  split_ifs at *
  simp_all

theorem pSign_eq_one {d : Dir2} (h : pExt d = 0) : pSign d = 1 := by
  unfold pExt at h
  unfold pSign
  split_ifs at *
  simp_all

theorem bSign_cases (μ : Fin 3) : bSign μ = 1 ∨ bSign μ = -1 := by
  unfold bSign
  split_ifs <;> simp

theorem pSign_cases (d : Dir2) : pSign d = 1 ∨ pSign d = -1 := by
  unfold pSign
  split_ifs <;> simp

/-! ### The reflection of the product measure -/

theorem measurePreserving_sign_Ioc (a : ℝ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    MeasurePreserving (fun x : ℝ => ε * x) ((volume : Measure ℝ).restrict (Set.Ioc (-a) a))
      ((volume : Measure ℝ).restrict (Set.Ioc (-a) a)) := by
  rcases hε with rfl | rfl
  · simp only [one_mul]
    exact MeasurePreserving.id _
  · rw [restrict_Ioc_eq_restrict_Icc]
    have hs : Neg.neg ⁻¹' Set.Icc (-a) a = Set.Icc (-a) a := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Icc]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    have hp := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
      (measurableSet_Icc (a := -a) (b := a))
    rw [hs] at hp
    simpa only [neg_one_mul] using hp

theorem map_neg_count : Measure.map (fun m : ℤ => -m) Measure.count = Measure.count := by
  refine Measure.ext_iff_singleton.mpr fun m => ?_
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton m)]
  have : (fun m : ℤ => -m) ⁻¹' {m} = {-m} := by
    ext k
    simp
  rw [this, Measure.count_singleton, Measure.count_singleton]

theorem measurePreserving_sign_int {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    MeasurePreserving (fun x : ℝ => ε * x) intMeasure intMeasure := by
  rcases hε with rfl | rfl
  · simp only [one_mul]
    exact MeasurePreserving.id _
  · refine ⟨by fun_prop, ?_⟩
    unfold intMeasure
    rw [Measure.map_map (by fun_prop) measurableEmbedding_intCast.measurable]
    have : (fun x : ℝ => -1 * x) ∘ (Int.cast : ℤ → ℝ) = (Int.cast : ℤ → ℝ) ∘ fun m => -m := by
      funext m
      simp
    rw [this, ← Measure.map_map measurableEmbedding_intCast.measurable (measurable_of_countable _),
      map_neg_count]

variable (s : Side) (c : Coeffs)

/-- The reflection in the site planes `x_3 = 0` and `x_3 = L/2` of the torus. -/
def torusRefl : IndexRefl (cellMeasure c (n := s.n)) where
  r := Sum.map (flip 0) (Sum.map rBond rPlaq)
  invol k := by
    rcases k with k | k | k
    · simp only [Sum.map_inl, flip_flip]
    · simp only [Sum.map_inr, Sum.map_inl, rBond_rBond]
    · simp only [Sum.map_inr, rPlaq_rPlaq]
  sgn := Sum.elim (fun _ => 1) (Sum.elim (fun b => bSign b.2) fun p => pSign p.2)
  sgn_mul k := by
    rcases k with k | k | k
    · simp
    · rcases bSign_cases k.2 with h | h <;> simp [rBond, h]
    · rcases pSign_cases k.2 with h | h <;> simp [rPlaq, h]
  mp k := by
    rcases k with k | k | k
    · simp only [Sum.elim_inl, one_mul]
      exact MeasurePreserving.id ((volume : Measure ℝ).restrict (Set.Ici (-c.ρ0)))
    · exact measurePreserving_sign_Ioc (Real.pi / c.γ) (bSign_cases k.2)
    · exact measurePreserving_sign_int (pSign_cases k.2)
  U := Sum.elim (up 0) (Sum.elim (fun b => up (bExt b.2) b.1) fun p => up (pExt p.2) p.1)
  cover k := by
    rcases k with k | k | k
    · simpa using up_cover s.even (Nat.zero_le 1) k
    · simpa [rBond, bShift_eq] using up_cover s.even (bExt_le k.2) k.1
    · simpa [rPlaq, pShift_eq] using up_cover s.even (pExt_le k.2) k.1
  plane k := by
    rcases k with k | k | k
    · intro h h'
      have := up_plane s.even (Nat.zero_le 1) (x := k) h (by simpa using h')
      refine ⟨?_, rfl⟩
      simpa using this.2
    · intro h h'
      have := up_plane s.even (bExt_le k.2) (x := k.1) h (by simpa [rBond, bShift_eq] using h')
      refine ⟨?_, bSign_eq_one this.1⟩
      simp only [Sum.map_inr, Sum.map_inl, rBond, bShift_eq, this.2]
    · intro h h'
      have := up_plane s.even (pExt_le k.2) (x := k.1) h (by simpa [rPlaq, pShift_eq] using h')
      refine ⟨?_, pSign_eq_one this.1⟩
      simp only [Sum.map_inr, rPlaq, pShift_eq, this.2]

/-! ### The half weight -/

namespace IndexRefl

variable {K : Type*} {ν : K → Measure ℝ} (R : IndexRefl ν)

open Classical in
/-- The share of the closed upper half in the factor of a cell: one above the plane, one half in the
plane, zero below. -/
def share (k : K) : ℝ := if R.U k then (if R.U (R.r k) then 1 / 2 else 1) else 0

theorem share_nonneg (k : K) : 0 ≤ R.share k := by
  unfold share
  split_ifs <;> norm_num

theorem share_add (k : K) : R.share k + R.share (R.r k) = 1 := by
  unfold share
  rw [R.invol]
  by_cases h : R.U k
  · by_cases h' : R.U (R.r k)
    · simp only [h, h', ite_true]; norm_num
    · simp only [h, h', ite_true, ite_false]; norm_num
  · have h' := (R.cover k).resolve_left h
    simp only [h, h', ite_true, ite_false]; norm_num

theorem share_eq_zero {k : K} (h : ¬ R.U k) : R.share k = 0 := by
  unfold share
  simp only [h, ite_false]

end IndexRefl

/-- A product of powers with the shares, times its reflection. -/
theorem prod_share {A : Type*} [Fintype A] (ρ : A → A) (hρ : Function.Involutive ρ)
    (h φ : A → ℝ) (hφ : ∀ a, 0 ≤ φ a) (hh : ∀ a, 0 ≤ h a) (hsum : ∀ a, h a + h (ρ a) = 1) :
    (∏ a, φ a ^ h a) * (∏ a, φ (ρ a) ^ h a) = ∏ a, φ a := by
  have h1 : ∏ a, φ (ρ a) ^ h a = ∏ a, φ a ^ h (ρ a) := by
    rw [← Equiv.prod_comp (hρ.toPerm ρ) fun a => φ a ^ h (ρ a)]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp only [Function.Involutive.coe_toPerm, hρ a]
  rw [h1, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Real.rpow_add_of_nonneg (hφ a) (hh a) (hh _), hsum, Real.rpow_one]

/-- The share of a cell of the torus. -/
abbrev shr (k : Cell s.n) : ℝ := (torusRefl s c).share k

/-- The half weight. -/
def halfWeight (x : Cell s.n → ℝ) : ℝ :=
  (∏ z, |siteFactor c (x (.inl z))| ^ shr s c (.inl z)) *
    (∏ b, hopCell c x b ^ shr s c (.inr (.inl b))) *
    (∏ p, Real.exp (-(curvCell c x p) ^ 2 / 2) ^ shr s c (.inr (.inr p))) *
    ∏ z, closedCell x z ^ shr s c (.inr (.inl (z, 2)))

variable {s}

theorem act_site (x : Cell s.n → ℝ) (z : Site (ZMod s.n)) :
    (torusRefl s c).act x (.inl z) = x (.inl (flip 0 z)) :=
  one_mul _

theorem act_bond (x : Cell s.n → ℝ) (b : Bond (ZMod s.n)) :
    (torusRefl s c).act x (.inr (.inl b)) = bSign b.2 * x (.inr (.inl (rBond b))) := rfl

theorem act_plaq (x : Cell s.n → ℝ) (p : Plaq (ZMod s.n)) :
    (torusRefl s c).act x (.inr (.inr p)) = pSign p.2 * x (.inr (.inr (rPlaq p))) := rfl

theorem curvCell_act (x : Cell s.n → ℝ) (p : Plaq (ZMod s.n)) :
    curvCell c ((torusRefl s c).act x) p = pSign p.2 * curvCell c x (rPlaq p) := by
  unfold curvCell
  have h1 : dBond (bondPart ((torusRefl s c).act x)) p =
      pSign p.2 * dBond (bondPart x) (rPlaq p) := dBond_refl (bondPart x) p
  have h2 : plaqPart ((torusRefl s c).act x) p = pSign p.2 * plaqPart x (rPlaq p) := rfl
  rw [h1, h2]
  ring

theorem closedCell_act (x : Cell s.n → ℝ) (z : Site (ZMod s.n)) :
    closedCell ((torusRefl s c).act x) z = closedCell x (flip 1 z) := by
  unfold closedCell
  have h : dPlaqR (plaqPart ((torusRefl s c).act x)) z = -dPlaqR (plaqPart x) (flip 1 z) :=
    dPlaqR_refl (plaqPart x) z
  rw [h]
  simp only [neg_eq_zero]

theorem hopCell_act (x : Cell s.n → ℝ) (b : Bond (ZMod s.n)) :
    hopCell c ((torusRefl s c).act x) b = hopCell c x (rBond b) := by
  obtain ⟨z, μ⟩ := b
  unfold hopCell bondPart
  rw [act_site, act_site, act_bond]
  by_cases hμ : μ = 2
  · subst hμ
    simp only [bSign, rBond, bShift, ite_true, flip_zero_add_unit_two, neg_one_mul,
      flip_one_add_unit_two]
    exact TorusSymmetry.hop_reverse c _ _ _
  · simp only [bSign, rBond, bShift, ite_eq_right hμ, flip_add_unit hμ, one_mul]

theorem cfgOf_act (x : Cell s.n → ℝ) :
    cfgOf c ((torusRefl s c).act x) = reflCfg (cfgOf c x) := by
  refine Prod.ext (funext fun p => ?_) (funext fun z => ?_)
  · exact curvCell_act c x p
  · exact act_site c x z

theorem hopCell_pos (x : Cell s.n → ℝ) (b : Bond (ZMod s.n)) : 0 < hopCell c x b :=
  Real.exp_pos _

theorem closedCell_nonneg (x : Cell s.n → ℝ) (z : Site (ZMod s.n)) : 0 ≤ closedCell x z := by
  unfold closedCell
  split_ifs <;> norm_num

/-- The weight is the half weight times its reflection. -/
theorem halfWeight_mul (x : Cell s.n → ℝ) :
    halfWeight s c x * halfWeight s c ((torusRefl s c).act x) = cellWeight c x := by
  have h1 := prod_share (flip (0 : ZMod s.n)) (fun z => flip_flip 0 z)
    (fun z => shr s c (.inl z)) (fun z => |siteFactor c (x (.inl z))|) (fun z => abs_nonneg _)
    (fun z => (torusRefl s c).share_nonneg _) (fun z => (torusRefl s c).share_add (.inl z))
  have h2 := prod_share (rBond (n := s.n)) rBond_rBond
    (fun b => shr s c (.inr (.inl b))) (fun b => hopCell c x b) (fun b => (hopCell_pos c x b).le)
    (fun b => (torusRefl s c).share_nonneg _) (fun b => (torusRefl s c).share_add (.inr (.inl b)))
  have h3 := prod_share (rPlaq (n := s.n)) rPlaq_rPlaq
    (fun p => shr s c (.inr (.inr p))) (fun p => Real.exp (-(curvCell c x p) ^ 2 / 2))
    (fun p => (Real.exp_pos _).le)
    (fun p => (torusRefl s c).share_nonneg _) (fun p => (torusRefl s c).share_add (.inr (.inr p)))
  have h4 := prod_share (flip (1 : ZMod s.n)) (fun z => flip_flip 1 z)
    (fun z => shr s c (.inr (.inl (z, 2)))) (fun z => closedCell x z)
    (fun z => closedCell_nonneg x z) (fun z => (torusRefl s c).share_nonneg _)
    (fun z => by
      have hr : (torusRefl s c).r (.inr (.inl (z, 2))) = .inr (.inl (flip 1 z, 2)) := by
        simp [torusRefl, rBond, bShift]
      have := (torusRefl s c).share_add (.inr (.inl (z, 2)))
      rwa [hr] at this)
  have hp (p : Plaq (ZMod s.n)) : Real.exp (-(curvCell c ((torusRefl s c).act x) p) ^ 2 / 2) =
      Real.exp (-(curvCell c x (rPlaq p)) ^ 2 / 2) := by
    rw [curvCell_act]
    rcases pSign_cases p.2 with h | h <;> simp [h]
  unfold halfWeight cellWeight
  simp only [act_site, hopCell_act, closedCell_act, hp]
  rw [← h1, ← h2, ← h3, ← h4]
  ring

/-! ### The half weight depends on the closed upper half only -/

theorem bExt_two : bExt 2 = 1 := rfl

theorem bExt_ne {μ : Fin 3} (h : μ ≠ 2) : bExt μ = 0 := by
  unfold bExt
  simp [h]

/-- Agreement of two configurations on the closed upper half. -/
def AgreeUp (x y : Cell s.n → ℝ) : Prop :=
  (∀ z, up 0 z → x (.inl z) = y (.inl z)) ∧
    (∀ b : Bond (ZMod s.n), up (bExt b.2) b.1 → x (.inr (.inl b)) = y (.inr (.inl b))) ∧
    ∀ p : Plaq (ZMod s.n), up (pExt p.2) p.1 → x (.inr (.inr p)) = y (.inr (.inr p))

theorem agreeUp_of_U {x y : Cell s.n → ℝ} (h : ∀ k, (torusRefl s c).U k → x k = y k) :
    AgreeUp x y :=
  ⟨fun z hz => h (.inl z) hz, fun b hb => h (.inr (.inl b)) hb, fun p hp => h (.inr (.inr p)) hp⟩

theorem hopCell_congr {x y : Cell s.n → ℝ} (h : AgreeUp x y) {b : Bond (ZMod s.n)}
    (hb : up (bExt b.2) b.1) : hopCell c x b = hopCell c y b := by
  obtain ⟨z, μ⟩ := b
  unfold hopCell bondPart
  rw [h.1 z (up_mono (Nat.zero_le _) hb), h.2.1 (z, μ) hb]
  congr 1
  by_cases hμ : μ = 2
  · subst hμ
    exact h.1 _ (up_add_unit_two hb)
  · refine h.1 _ (up_add_unit hμ ?_)
    rwa [bExt_ne hμ] at hb

theorem dBond_congr {x y : Cell s.n → ℝ} (h : AgreeUp x y) {p : Plaq (ZMod s.n)}
    (hp : up (pExt p.2) p.1) : dBond (bondPart x) p = dBond (bondPart y) p := by
  obtain ⟨z, d⟩ := p
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have hb (z' : Site (ZMod s.n)) (μ : Fin 3) (hz : up (bExt μ) z') :
      bondPart x (z', μ) = bondPart y (z', μ) := h.2.1 (z', μ) hz
  rcases dir2_cases d with rfl | rfl | rfl
  · have hz : up 0 z := hp
    simp only [dBond, d01]
    rw [hb z 0 hz, hb (z + unitVec _ 0) 1 (up_add_unit h02 hz),
      hb (z + unitVec _ 1) 0 (up_add_unit h12 hz), hb z 1 hz]
  · have hz : up 1 z := hp
    have hz0 : up 0 z := up_mono (Nat.zero_le _) hz
    simp only [dBond, d02]
    rw [hb z 0 hz0, hb (z + unitVec _ 0) 2 (up_add_unit h02 hz),
      hb (z + unitVec _ 2) 0 (up_add_unit_two hz), hb z 2 hz]
  · have hz : up 1 z := hp
    have hz0 : up 0 z := up_mono (Nat.zero_le _) hz
    simp only [dBond, d12]
    rw [hb z 1 hz0, hb (z + unitVec _ 1) 2 (up_add_unit h12 hz),
      hb (z + unitVec _ 2) 1 (up_add_unit_two hz), hb z 2 hz]

theorem curvCell_congr {x y : Cell s.n → ℝ} (h : AgreeUp x y) {p : Plaq (ZMod s.n)}
    (hp : up (pExt p.2) p.1) : curvCell c x p = curvCell c y p := by
  unfold curvCell
  rw [dBond_congr h hp]
  have : plaqPart x p = plaqPart y p := h.2.2 p hp
  rw [this]

theorem closedCell_congr {x y : Cell s.n → ℝ} (h : AgreeUp x y) {z : Site (ZMod s.n)}
    (hz : up 1 z) : closedCell x z = closedCell y z := by
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have hp (z' : Site (ZMod s.n)) (d : Dir2) (hz : up (pExt d) z') :
      plaqPart x (z', d) = plaqPart y (z', d) := h.2.2 (z', d) hz
  have hz0 : up 0 z := up_mono (Nat.zero_le _) hz
  unfold closedCell dPlaqR
  rw [hp (z + unitVec _ 0) d12 (up_add_unit h02 hz), hp z d12 hz,
    hp (z + unitVec _ 1) d02 (up_add_unit h12 hz), hp z d02 hz,
    hp (z + unitVec _ 2) d01 (up_add_unit_two hz), hp z d01 hz0]

theorem halfWeight_congr {x y : Cell s.n → ℝ} (h : AgreeUp x y) :
    halfWeight s c x = halfWeight s c y := by
  have key (k : Cell s.n) (a b : ℝ) (hab : (torusRefl s c).U k → a = b) :
      a ^ shr s c k = b ^ shr s c k := by
    by_cases hk : (torusRefl s c).U k
    · rw [hab hk]
    · rw [shr, (torusRefl s c).share_eq_zero hk, Real.rpow_zero, Real.rpow_zero]
  unfold halfWeight
  congr 1
  · congr 1
    · congr 1
      · exact Finset.prod_congr rfl fun z _ => key _ _ _ fun hk => by rw [h.1 z hk]
      · exact Finset.prod_congr rfl fun b _ => key _ _ _ fun hk => hopCell_congr c h hk
    · exact Finset.prod_congr rfl fun p _ => key _ _ _ fun hk => by rw [curvCell_congr c h hk]
  · exact Finset.prod_congr rfl fun z _ => key _ _ _ fun hk => closedCell_congr h hk

theorem measurable_halfWeight : Measurable (halfWeight s c) := by
  unfold halfWeight
  refine ((Measurable.mul ?_ ?_).mul ?_).mul ?_
  · exact Finset.measurable_prod _ fun z _ =>
      ((measurable_siteFactor c).comp (measurable_pi_apply _)).abs.pow_const _
  · exact Finset.measurable_prod _ fun b _ => (measurable_hopCell c b).pow_const _
  · refine Finset.measurable_prod _ fun p _ => ?_
    have := measurable_curvCell c p
    exact Measurable.pow_const (by fun_prop) _
  · exact Finset.measurable_prod _ fun z _ => (measurable_closedCell z).pow_const _

theorem measurable_reflCfg {n : ℕ} : Measurable (reflCfg (n := n)) := by
  unfold reflCfg
  refine Measurable.prodMk (measurable_pi_iff.mpr fun p => ?_) (measurable_pi_iff.mpr fun z => ?_)
  · exact ((measurable_pi_apply _).comp measurable_fst).const_mul _
  · exact (measurable_pi_apply _).comp measurable_snd

variable (s)

/-- **Reflection positivity of the torus state** ([GG-OS] Theorem 9.7, site plane `c = 0`): for `F`
a measurable function of the curvature and density variables of the closed half `x_3 ∈ [0, L/2]`. -/
theorem torus_rp (F : Cfg (ZMod s.n) → ℂ) (hF : Measurable F)
    (hup : ∀ ω ω' : Cfg (ZMod s.n), (∀ p, up (pExt p.2) p.1 → ω.1 p = ω'.1 p) →
      (∀ z, up 0 z → ω.2 z = ω'.2 z) → F ω = F ω') :
    0 ≤ ∫ ω, starRingEnd ℂ (F (pull (timeRefl (ZMod s.n)) ω)) * F ω ∂(torusState s c) := by
  have hF' : Measurable fun ω => starRingEnd ℂ (F (pull (timeRefl (ZMod s.n)) ω)) * F ω := by
    simp only [pull_timeRefl]
    exact (Complex.continuous_conj.measurable.comp (hF.comp measurable_reflCfg)).mul hF
  rw [integral_torusState s c _ hF']
  have hG := (torusRefl s c).integral_nonneg
    (fun x => (halfWeight s c x : ℂ) * F (cfgOf c x))
    ((Complex.measurable_ofReal.comp (measurable_halfWeight c)).mul
      (hF.comp (measurable_cfgOf c)))
    (fun x y hxy => by
      have h := agreeUp_of_U c hxy
      have h1 := halfWeight_congr c h
      have h2 : F (cfgOf c x) = F (cfgOf c y) :=
        hup _ _ (fun p hp => curvCell_congr c h hp) fun z hz => h.1 z hz
      simp only [h1, h2])
  have heq : (fun x : Cell s.n → ℝ => (cellWeight c x : ℂ) *
      (starRingEnd ℂ (F (pull (timeRefl (ZMod s.n)) (cfgOf c x))) * F (cfgOf c x))) =
      fun x => starRingEnd ℂ ((halfWeight s c ((torusRefl s c).act x) : ℂ) *
        F (cfgOf c ((torusRefl s c).act x))) * ((halfWeight s c x : ℂ) * F (cfgOf c x)) := by
    funext x
    rw [pull_timeRefl, cfgOf_act, ← halfWeight_mul, map_mul, Complex.conj_ofReal]
    push_cast
    ring
  rw [heq, Complex.real_smul]
  exact mul_nonneg (Complex.zero_le_real.mpr ENNReal.toReal_nonneg) hG

end GGOS.OS

end

end

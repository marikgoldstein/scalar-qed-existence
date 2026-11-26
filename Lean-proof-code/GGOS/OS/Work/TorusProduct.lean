module

public import GGOS.Frozen.Defs.TorusState
public import GGOS.OS.Work.ProductRP

/-!
# The torus measure as an image of a weighted product measure

The sum over the closed Villain variables is written as an integral against counting measure, with
the closedness constraint as one factor of the weight per cube ([GG-OS], proof of Theorem 9.7).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GGOS.OS

/-- The cells of the torus that carry a variable: sites, bonds, plaquettes. -/
abbrev Cell (n : ℕ) := Site (ZMod n) ⊕ (Bond (ZMod n) ⊕ Plaq (ZMod n))

/-- Counting measure on the integers, on the real line. -/
def intMeasure : Measure ℝ := (Measure.count : Measure ℤ).map (Int.cast : ℤ → ℝ)

theorem measurableEmbedding_intCast : MeasurableEmbedding (Int.cast : ℤ → ℝ) :=
  Int.isClosedEmbedding_coe_real.measurableEmbedding

instance : SigmaFinite intMeasure := measurableEmbedding_intCast.sigmaFinite_map

/-- The reference measure of one variable. -/
def cellMeasure (c : Coeffs) {n : ℕ} : Cell n → Measure ℝ
  | .inl _ => (volume : Measure ℝ).restrict (Set.Ici (-c.ρ0))
  | .inr (.inl _) => (volume : Measure ℝ).restrict (Set.Ioc (-(Real.pi / c.γ)) (Real.pi / c.γ))
  | .inr (.inr _) => intMeasure

instance (c : Coeffs) {n : ℕ} (k : Cell n) : SigmaFinite (cellMeasure c k) := by
  rcases k with k | k | k
  · exact inferInstanceAs (SigmaFinite ((volume : Measure ℝ).restrict _))
  · exact inferInstanceAs (SigmaFinite ((volume : Measure ℝ).restrict _))
  · exact inferInstanceAs (SigmaFinite intMeasure)

variable (s : Side) (c : Coeffs)

instance : SigmaFinite (siteMeasure s c) := by
  unfold siteMeasure
  infer_instance

instance : SigmaFinite (bondMeasure s c) := by
  unfold bondMeasure
  infer_instance

/-- The configuration of the cells with given site, bond and plaquette variables. -/
def glueCells {n : ℕ} (z : ((Site (ZMod n) → ℝ) × (Bond (ZMod n) → ℝ)) × (Plaq (ZMod n) → ℤ)) :
    Cell n → ℝ :=
  Sum.elim z.1.1 (Sum.elim z.1.2 fun p => (z.2 p : ℝ))

theorem measurable_glueCells {n : ℕ} : Measurable (glueCells (n := n)) := by
  refine measurable_pi_iff.mpr fun k => ?_
  rcases k with k | k | k
  · change Measurable fun z : ((Site (ZMod n) → ℝ) × (Bond (ZMod n) → ℝ)) × (Plaq (ZMod n) → ℤ) =>
      z.1.1 k
    fun_prop
  · change Measurable fun z : ((Site (ZMod n) → ℝ) × (Bond (ZMod n) → ℝ)) × (Plaq (ZMod n) → ℤ) =>
      z.1.2 k
    fun_prop
  · change Measurable fun z : ((Site (ZMod n) → ℝ) × (Bond (ZMod n) → ℝ)) × (Plaq (ZMod n) → ℤ) =>
      ((z.2 k : ℤ) : ℝ)
    exact measurableEmbedding_intCast.measurable.comp ((measurable_pi_apply k).comp measurable_snd)

theorem pi_count {P : Type*} [Fintype P] :
    Measure.pi (fun _ : P => (Measure.count : Measure ℤ)) = Measure.count := by
  refine Measure.ext_iff_singleton.mpr fun m => ?_
  rw [Measure.pi_singleton, Measure.count_singleton]
  simp

/-- The product of the cell measures. -/
theorem map_glueCells :
    Measure.map glueCells (((siteMeasure s c).prod (bondMeasure s c)).prod
      (Measure.count : Measure (Plaq (ZMod s.n) → ℤ))) =
      Measure.pi (cellMeasure c (n := s.n)) := by
  refine (Measure.pi_eq fun t ht => ?_).symm
  rw [Measure.map_apply measurable_glueCells (MeasurableSet.univ_pi ht)]
  have hpre : glueCells ⁻¹' (Set.univ.pi t) =
      ((Set.univ.pi fun x => t (.inl x)) ×ˢ (Set.univ.pi fun b => t (.inr (.inl b)))) ×ˢ
        (Set.univ.pi fun p => (Int.cast : ℤ → ℝ) ⁻¹' t (.inr (.inr p))) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod, Sum.forall, glueCells,
      Sum.elim_inl, Sum.elim_inr, and_assoc]
  rw [hpre, Measure.prod_prod, Measure.prod_prod, ← pi_count, Measure.pi_pi, siteMeasure,
    bondMeasure, Measure.pi_pi, Measure.pi_pi, Fintype.prod_sum_type, Fintype.prod_sum_type,
    mul_assoc]
  congr 2
  refine congrArg _ (funext fun p => ?_)
  change _ = intMeasure _
  rw [intMeasure, Measure.map_apply measurableEmbedding_intCast.measurable (ht _)]

variable {s}

/-- The real version of `(dm)_c`. -/
def dPlaqR {n : ℕ} (m : Plaq (ZMod n) → ℝ) (x : Site (ZMod n)) : ℝ :=
  (m (x + unitVec (ZMod n) 0, d12) - m (x, d12)) - (m (x + unitVec (ZMod n) 1, d02) - m (x, d02))
    + (m (x + unitVec (ZMod n) 2, d01) - m (x, d01))

/-- The bond variables of a configuration of the cells. -/
abbrev bondPart {n : ℕ} (x : Cell n → ℝ) (b : Bond (ZMod n)) : ℝ := x (.inr (.inl b))

/-- The plaquette variables of a configuration of the cells. -/
abbrev plaqPart {n : ℕ} (x : Cell n → ℝ) (p : Plaq (ZMod n)) : ℝ := x (.inr (.inr p))

/-- The curvature of a configuration of the cells. -/
def curvCell {n : ℕ} (x : Cell n → ℝ) (p : Plaq (ZMod n)) : ℝ :=
  dBond (bondPart x) p + 2 * Real.pi / c.γ * plaqPart x p

/-- The gauge-invariant configuration of a configuration of the cells. -/
def cfgOf {n : ℕ} (x : Cell n → ℝ) : Cfg (ZMod n) := (curvCell c x, fun z => x (.inl z))

/-- The hopping factor of a bond. -/
def hopCell {n : ℕ} (x : Cell n → ℝ) (b : Bond (ZMod n)) : ℝ :=
  hop c (x (.inl b.1)) (x (.inl (b.1 + unitVec (ZMod n) b.2))) (bondPart x b)

/-- The closedness factor of a cube. -/
def closedCell {n : ℕ} (x : Cell n → ℝ) (z : Site (ZMod n)) : ℝ :=
  if dPlaqR (plaqPart x) z = 0 then 1 else 0

/-- The weight of a configuration of the cells, with the modulus of the site factors. -/
def cellWeight (x : Cell s.n → ℝ) : ℝ :=
  (∏ z, |siteFactor c (x (.inl z))|) * (∏ b, hopCell c x b) *
    (∏ p, Real.exp (-(curvCell c x p) ^ 2 / 2)) * ∏ z, closedCell x z

theorem measurable_curvCell {n : ℕ} (p : Plaq (ZMod n)) :
    Measurable fun x : Cell n → ℝ => curvCell c x p := by
  unfold curvCell dBond bondPart plaqPart
  fun_prop

theorem measurable_cfgOf {n : ℕ} : Measurable (cfgOf c (n := n)) := by
  refine Measurable.prodMk (measurable_pi_iff.mpr fun p => measurable_curvCell c p) ?_
  exact measurable_pi_iff.mpr fun z => measurable_pi_apply _

theorem measurable_siteFactor : Measurable (siteFactor c) := by
  unfold siteFactor
  fun_prop

theorem measurable_hopCell {n : ℕ} (b : Bond (ZMod n)) :
    Measurable fun x : Cell n → ℝ => hopCell c x b := by
  unfold hopCell hop bondPart
  fun_prop

theorem measurable_closedCell {n : ℕ} (z : Site (ZMod n)) :
    Measurable fun x : Cell n → ℝ => closedCell x z := by
  unfold closedCell
  refine Measurable.ite (measurableSet_eq_fun ?_ measurable_const) measurable_const measurable_const
  unfold dPlaqR plaqPart
  fun_prop

theorem measurable_cellWeight : Measurable (cellWeight c (s := s)) := by
  unfold cellWeight
  refine ((Measurable.mul ?_ ?_).mul ?_).mul ?_
  · exact Finset.measurable_prod _ fun z _ =>
      ((measurable_siteFactor c).comp (measurable_pi_apply _)).abs
  · exact Finset.measurable_prod _ fun b _ => measurable_hopCell c b
  · refine Finset.measurable_prod _ fun p _ => ?_
    have := measurable_curvCell c p
    fun_prop
  · exact Finset.measurable_prod _ fun z _ => measurable_closedCell z

theorem cellWeight_nonneg (x : Cell s.n → ℝ) : 0 ≤ cellWeight c x := by
  unfold cellWeight
  refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_
  · exact Finset.prod_nonneg fun z _ => abs_nonneg _
  · exact Finset.prod_nonneg fun b _ => (Real.exp_pos _).le
  · exact Finset.prod_nonneg fun p _ => (Real.exp_pos _).le
  · refine Finset.prod_nonneg fun z _ => ?_
    unfold closedCell
    split_ifs <;> norm_num

theorem siteFactor_nonneg {r : ℝ} (hr : -c.ρ0 ≤ r) : 0 ≤ siteFactor c r := by
  unfold siteFactor
  have : 0 ≤ c.ρ0 + r := by linarith
  positivity

theorem dPlaqR_intCast {n : ℕ} (m : Plaq (ZMod n) → ℤ) (z : Site (ZMod n)) :
    dPlaqR (fun p => (m p : ℝ)) z = ((dPlaq m z : ℤ) : ℝ) := by
  simp [dPlaqR, dPlaq]

theorem prod_closedCell_glue (v : (Site (ZMod s.n) → ℝ) × (Bond (ZMod s.n) → ℝ))
    (m : Plaq (ZMod s.n) → ℤ) [Decidable (IsClosedForm m)] :
    ∏ z, closedCell (glueCells (v, m)) z = if IsClosedForm m then 1 else 0 := by
  have h (z : Site (ZMod s.n)) : closedCell (glueCells (v, m)) z =
      if dPlaq m z = 0 then 1 else 0 := by
    unfold closedCell
    have : dPlaqR (plaqPart (glueCells (v, m))) z = ((dPlaq m z : ℤ) : ℝ) := dPlaqR_intCast m z
    rw [this]
    simp only [Int.cast_eq_zero]
  simp only [h]
  by_cases hcl : IsClosedForm m
  · rw [ite_eq_left hcl]
    exact Finset.prod_eq_one fun z _ => ite_eq_left (hcl z)
  · rw [ite_eq_right hcl]
    obtain ⟨z, hz⟩ := not_forall.mp hcl
    exact Finset.prod_eq_zero (Finset.mem_univ z) (ite_eq_right hz)

theorem cellWeight_glue (v : (Site (ZMod s.n) → ℝ) × (Bond (ZMod s.n) → ℝ))
    (hv : ∀ z, -c.ρ0 ≤ v.1 z) (m : Plaq (ZMod s.n) → ℤ) [Decidable (IsClosedForm m)] :
    cellWeight c (glueCells (v, m)) = weight s c v.1 v.2 m * if IsClosedForm m then 1 else 0 := by
  unfold cellWeight
  rw [prod_closedCell_glue]
  congr 1
  unfold weight
  congr 1
  · congr 1
    exact Finset.prod_congr rfl fun z _ => abs_of_nonneg (siteFactor_nonneg c (hv z))

theorem cfgOf_glue {n : ℕ} (v : (Site (ZMod n) → ℝ) × (Bond (ZMod n) → ℝ))
    (m : Plaq (ZMod n) → ℤ) : cfgOf c (glueCells (v, m)) = (curv c v.2 m, v.1) := rfl

variable (s)

theorem ae_site_ge : ∀ᵐ v ∂((siteMeasure s c).prod (bondMeasure s c)), ∀ z, -c.ρ0 ≤ v.1 z := by
  have h1 : ∀ᵐ r ∂(siteMeasure s c), ∀ z, -c.ρ0 ≤ r z := by
    rw [ae_all_iff]
    intro z
    have := Measure.tendsto_eval_ae_ae (μ := fun _ : Site (ZMod s.n) =>
      (volume : Measure ℝ).restrict (Set.Ici (-c.ρ0))) (i := z)
    exact this.eventually (ae_restrict_mem measurableSet_Ici)
  exact (Measure.quasiMeasurePreserving_fst (μ := siteMeasure s c)
    (ν := bondMeasure s c)).ae h1

/-- The torus measure is the image of the weighted product measure. -/
theorem torusMeasure_eq : torusMeasure s c =
    Measure.map (cfgOf c) ((Measure.pi (cellMeasure c (n := s.n))).withDensity
      fun x => ENNReal.ofReal (cellWeight c x)) := by
  classical
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  let Φ : (Cell s.n → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal (cellWeight c x) * F (cfgOf c x)
  have hW : Measurable fun x : Cell s.n → ℝ => ENNReal.ofReal (cellWeight c x) :=
    (measurable_cellWeight c).ennreal_ofReal
  have hFc : Measurable fun x : Cell s.n → ℝ => F (cfgOf c x) := hF.comp (measurable_cfgOf c)
  have hΦ : Measurable Φ := hW.mul hFc
  have hR : ∫⁻ ω, F ω ∂(Measure.map (cfgOf c) ((Measure.pi (cellMeasure c (n := s.n))).withDensity
      fun x => ENNReal.ofReal (cellWeight c x))) =
      ∫⁻ x, Φ x ∂(Measure.pi (cellMeasure c (n := s.n))) := by
    rw [lintegral_map hF (measurable_cfgOf c), lintegral_withDensity_eq_lintegral_mul _ hW hFc]
    rfl
  have hprod := lintegral_prod_symm (μ := (siteMeasure s c).prod (bondMeasure s c))
    (ν := (Measure.count : Measure (Plaq (ZMod s.n) → ℤ)))
    (fun z => Φ (glueCells z)) (hΦ.comp measurable_glueCells).aemeasurable
  have hclosed (m : Plaq (ZMod s.n) → ℤ) (hm : IsClosedForm m) :
      ∫⁻ ω, F ω ∂(Measure.map
        (fun x : (Site (ZMod s.n) → ℝ) × (Bond (ZMod s.n) → ℝ) => (curv c x.2 m, x.1))
        (((siteMeasure s c).prod (bondMeasure s c)).withDensity
          fun x => ENNReal.ofReal (weight s c x.1 x.2 m))) =
      ∫⁻ v, Φ (glueCells (v, m)) ∂((siteMeasure s c).prod (bondMeasure s c)) := by
    have hcfg : Measurable fun v : (Site (ZMod s.n) → ℝ) × (Bond (ZMod s.n) → ℝ) =>
        ((curv c v.2 m, v.1) : Cfg (ZMod s.n)) := by
      refine Measurable.prodMk (measurable_pi_iff.mpr fun p => ?_) measurable_fst
      unfold curv dBond
      fun_prop
    have hw : Measurable fun v : (Site (ZMod s.n) → ℝ) × (Bond (ZMod s.n) → ℝ) =>
        ENNReal.ofReal (weight s c v.1 v.2 m) := by
      refine Measurable.ennreal_ofReal ?_
      unfold weight siteFactor hop curv dBond
      fun_prop
    refine (lintegral_map hF hcfg).trans ((lintegral_withDensity_eq_lintegral_mul
      ((siteMeasure s c).prod (bondMeasure s c)) hw (hF.comp hcfg)).trans ?_)
    refine lintegral_congr_ae ((ae_site_ge s c).mono fun v hv => ?_)
    have h1 := cellWeight_glue c v hv m
    rw [ite_eq_left hm, mul_one] at h1
    simp only [Φ, Pi.mul_apply, Function.comp_apply, h1, cfgOf_glue]
  have hnot (m : Plaq (ZMod s.n) → ℤ) (hm : ¬ IsClosedForm m) :
      ∫⁻ v, Φ (glueCells (v, m)) ∂((siteMeasure s c).prod (bondMeasure s c)) = 0 := by
    have hae : (fun v : (Site (ZMod s.n) → ℝ) × (Bond (ZMod s.n) → ℝ) => Φ (glueCells (v, m)))
        =ᵐ[(siteMeasure s c).prod (bondMeasure s c)] fun _ => 0 := by
      refine (ae_site_ge s c).mono fun v hv => ?_
      have h1 := cellWeight_glue c v hv m
      rw [ite_eq_right hm, mul_zero] at h1
      simp only [Φ, h1, ENNReal.ofReal_zero, zero_mul]
    exact (lintegral_congr_ae hae).trans lintegral_zero
  rw [hR, ← map_glueCells, lintegral_map hΦ measurable_glueCells, hprod, lintegral_count,
    torusMeasure, lintegral_sum_measure, ← tsum_subtype_eq_of_support_subset
      (s := {m : Plaq (ZMod s.n) → ℤ | IsClosedForm m})
      (f := fun m => ∫⁻ v, Φ (glueCells (v, m)) ∂((siteMeasure s c).prod (bondMeasure s c)))]
  · exact tsum_congr fun m => hclosed m.1 m.2
  · intro m hm
    by_contra h
    exact hm (hnot m h)

/-- Integrals against the torus state. -/
theorem integral_torusState (f : Cfg (ZMod s.n) → ℂ) (hf : Measurable f) :
    ∫ ω, f ω ∂(torusState s c) = ((torusMeasure s c Set.univ)⁻¹).toReal •
      ∫ x, (cellWeight c x : ℂ) * f (cfgOf c x) ∂(Measure.pi (cellMeasure c (n := s.n))) := by
  rw [torusState, integral_smul_measure, torusMeasure_eq,
    integral_map (measurable_cfgOf c).aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (measurable_cellWeight c).ennreal_ofReal
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (cellWeight_nonneg c x), Complex.real_smul]

end GGOS.OS

end

end

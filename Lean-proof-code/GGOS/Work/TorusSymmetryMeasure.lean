module

public import GGOS.Work.TorusSymmetryClosed
public import GGOS.Work.TorusSymmetryWeight
public import GGOS.Frozen.Defs.TorusState

/-!
# Change of variables in the Villain sum and the normalized torus measure
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace GGOS.TorusSymmetry

variable {R : Type*} [CommRing R]

abbrev Variables (R : Type*) [CommRing R] := (Site R → ℝ) × (Bond R → ℝ)

def realSign (u : ℤˣ) : ℝ ≃ᵐ ℝ where
  toEquiv := (sign u).toEquiv
  measurable_toFun := by
    unfold sign
    split
    · exact measurable_id
    · exact measurable_neg
  measurable_invFun := by
    unfold sign
    split
    · exact measurable_id
    · exact measurable_neg

/-- Reindex the site and bond variables, then orient each bond in its stored direction. -/
def variablesEquiv (g : LatSym R) : Variables R ≃ᵐ Variables R :=
  (MeasurableEquiv.arrowCongr' (siteEquiv g).symm (.refl ℝ)).prodCongr
    ((MeasurableEquiv.arrowCongr' (bondEquiv g).symm (.refl ℝ)).trans
      (MeasurableEquiv.piCongrRight fun b => realSign (g.sgn b.2)))

/-- Adding the missing endpoint does not change restricted Lebesgue measure.
The resulting closed interval is preserved exactly by negation. -/
private theorem measurePreserving_realSign (u : ℤˣ) (a : ℝ) :
    MeasurePreserving (realSign u) (volume.restrict (Set.Ioc (-a) a))
      (volume.restrict (Set.Ioc (-a) a)) := by
  by_cases h : u = 1
  · simpa [realSign, sign, h] using MeasurePreserving.id (volume.restrict (Set.Ioc (-a) a))
  · rw [restrict_Ioc_eq_restrict_Icc]
    have hs : Neg.neg ⁻¹' Set.Icc (-a) a = Set.Icc (-a) a := by
      ext x
      change (-a ≤ -x ∧ -x ≤ a) ↔ -a ≤ x ∧ x ≤ a
      constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
    have hp := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
      (measurableSet_Icc (a := -a) (b := a))
    rw [hs] at hp
    simp only [realSign, sign, h, ite_false]
    exact hp

private theorem measurePreserving_reindex {I : Type*} [Fintype I] (e : I ≃ I)
    (μ : Measure ℝ) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.arrowCongr' e.symm (.refl ℝ))
      (Measure.pi fun _ : I => μ) (Measure.pi fun _ : I => μ) :=
  measurePreserving_arrowCongr' _ _ _ _ fun _ => MeasurePreserving.id μ

theorem measurePreserving_variables (s : Side) (c : Coeffs) (g : LatSym (ZMod s.n)) :
    MeasurePreserving (variablesEquiv g)
      ((siteMeasure s c).prod (bondMeasure s c)) ((siteMeasure s c).prod (bondMeasure s c)) := by
  unfold siteMeasure bondMeasure
  apply MeasurePreserving.prod (measurePreserving_reindex (siteEquiv g) _)
  exact (measurePreserving_pi _ _ fun b : Bond (ZMod s.n) =>
    measurePreserving_realSign (g.sgn b.2) (Real.pi / c.γ)).comp
      (measurePreserving_reindex (bondEquiv g) _)

theorem measurable_pull (g : LatSym R) : Measurable (pull g) := by
  unfold pull
  apply Measurable.prodMk
  · refine measurable_pi_iff.mpr fun p => ?_
    unfold evalAnti
    split_ifs <;> fun_prop
  · exact measurable_pi_iff.mpr fun x => (measurable_pi_apply _).comp measurable_snd

private def config (c : Coeffs) (m : Plaq R → ℤ) (v : Variables R) : Cfg R :=
  (curv c v.2 m, v.1)

private theorem measurable_config (c : Coeffs) (m : Plaq R → ℤ) : Measurable (config c m) := by
  refine Measurable.prodMk (measurable_pi_iff.mpr fun p => ?_) measurable_fst
  unfold curv dBond
  fun_prop

private def weightedMeasure (s : Side) (c : Coeffs) (m : Plaq (ZMod s.n) → ℤ) :
    Measure (Variables (ZMod s.n)) :=
  ((siteMeasure s c).prod (bondMeasure s c)).withDensity
    fun v => ENNReal.ofReal (weight s c v.1 v.2 m)

private theorem map_weightedMeasure (s : Side) (c : Coeffs) (g : LatSym (ZMod s.n))
    (m : Plaq (ZMod s.n) → ℤ) :
    (weightedMeasure s c m).map (variablesEquiv g) = weightedMeasure s c (faceField g m) := by
  ext t ht
  rw [MeasurableEquiv.map_apply]
  simp only [weightedMeasure, withDensity_apply _ ((variablesEquiv g).measurable ht),
    withDensity_apply _ ht]
  have hW (v : Variables (ZMod s.n)) :
      weight s c (variablesEquiv g v).1 (variablesEquiv g v).2 (faceField g m) =
        weight s c v.1 v.2 m := weight_invariant s c g v.1 v.2 m
  simpa only [hW] using (measurePreserving_variables s c g).setLIntegral_comp_preimage_emb
    (variablesEquiv g).measurableEmbedding
    (fun v => ENNReal.ofReal (weight s c v.1 v.2 (faceField g m))) t

private def summand (s : Side) (c : Coeffs) (m : {m : Plaq (ZMod s.n) → ℤ // IsClosedForm m}) :
    Measure (Cfg (ZMod s.n)) :=
  (weightedMeasure s c m.1).map (config c m.1)

private theorem map_summand (s : Side) (c : Coeffs) (g : LatSym (ZMod s.n))
    (m : {m : Plaq (ZMod s.n) → ℤ // IsClosedForm m}) :
    (summand s c m).map (pull g) = summand s c (closedEquiv g m) := by
  unfold summand
  rw [closedEquiv_apply, Measure.map_map (measurable_pull g) (measurable_config c m.1),
    ← map_weightedMeasure s c g m.1,
    Measure.map_map (measurable_config c _) (variablesEquiv g).measurable]
  apply congrArg (fun f => Measure.map f _)
  funext v
  change pull g (curv c v.2 m.1, v.1) = (curv c (bondField g v.2) (faceField g m.1), _)
  rw [pull_eq_faceField]
  exact Prod.ext (funext fun p => (curv_bondField c g v.2 m.1 p).symm) rfl

theorem map_torusState (s : Side) (c : Coeffs) (g : LatSym (ZMod s.n)) :
    (torusState s c).map (pull g) = torusState s c := by
  have hm : (torusMeasure s c).map (pull g) = torusMeasure s c := by
    change (Measure.sum (summand s c)).map _ = Measure.sum (summand s c)
    rw [Measure.map_sum (measurable_pull g).aemeasurable]
    simp_rw [map_summand]
    exact Measure.sum_comp_equiv (closedEquiv g) (summand s c)
  rw [torusState, Measure.map_smul, hm]

end GGOS.TorusSymmetry

end

end

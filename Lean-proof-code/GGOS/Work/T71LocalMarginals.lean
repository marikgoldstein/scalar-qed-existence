module

public import GGOS.Frozen.Defs.IsLocal

/-!
# Finite-dimensional marginals of lattice configurations
-/

public section

open MeasureTheory

namespace GGOS.Work

/-- Bounded continuous local observables determine a finite measure on configurations. -/
theorem measure_eq_of_integral_local_eq {μ ν : Measure (Cfg ℤ)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ F : Cfg ℤ → ℂ, IsLocal F → Continuous F → (∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) →
      ∫ x, F x ∂μ = ∫ x, F x ∂ν) :
    μ = ν := by
  let e := (MeasurableEquiv.sumPiEquivProdPi (fun _ : Plaq ℤ ⊕ Site ℤ => ℝ)).symm
  have he : Continuous e :=
    (Homeomorph.sumPiEquivProdPi (Plaq ℤ) (Site ℤ) (fun _ => ℝ)).symm.continuous
  apply e.measurableEmbedding.map_injective
  have hν : IsProjectiveLimit (ν.map e) (fun I => (ν.map e).map I.restrict) :=
    fun _ => rfl
  refine IsProjectiveLimit.unique ?_ hν
  intro I
  let π : Cfg ℤ → I → ℝ := I.restrict ∘ e
  have hπ : Continuous π := (Finset.continuous_restrict I).comp he
  have localize (f : (I → ℝ) → ℂ) : IsLocal (f ∘ π) := by
    refine ⟨I.toLeft, I.toRight, fun w w' hp hx => congrArg f ?_⟩
    funext ⟨i, hi⟩
    cases i with
    | inl p => exact hp p (Finset.mem_toLeft.mpr hi)
    | inr x => exact hx x (Finset.mem_toRight.mpr hi)
  simp only [Measure.map_map (Finset.measurable_restrict I) e.measurable]
  change μ.map π = ν.map π
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hπ.measurable.aemeasurable f.continuous.aestronglyMeasurable,
    integral_map hπ.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, ← integral_complex_ofReal]
  exact h _ (localize (fun z => (f z : ℂ)))
    (Complex.continuous_ofReal.comp (f.continuous.comp hπ))
    ⟨‖f‖, fun w => by simpa only [Complex.norm_real] using f.norm_coe_le_norm (π w)⟩

end GGOS.Work

end

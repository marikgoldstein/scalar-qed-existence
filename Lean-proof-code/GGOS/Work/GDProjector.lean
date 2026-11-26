module

public import GGOS.Work.GDFourier
public import GGOS.Work.GDLattice

/-!
# Character projection onto closed integer plaquette fields
-/

@[expose] public section

open MeasureTheory Real Set Classical

namespace GGOS.Work.GD

/-- The product of unit-length intervals for the cube multipliers. -/
noncomputable def cubeMeasure (X : Type*) [Fintype X] : Measure (X → ℝ) :=
  Measure.pi fun _ => (volume : Measure ℝ).restrict (Ioc 0 1)

instance (X : Type*) [Fintype X] : IsFiniteMeasure (cubeMeasure X) := by
  unfold cubeMeasure
  infer_instance

variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]

/-- The cube integral of the modulation is exactly the indicator of the closed sectors. -/
theorem integral_cube_character (m : Plaq R → ℤ) :
    ∫ t, wave (∑ p, cubeAdj t p * m p) ∂cubeMeasure (Site R) =
      if IsClosedForm m then 1 else 0 := by
  classical
  have h (k : ℤ) : ∫ x in Ioc (0 : ℝ) 1, wave (x * k) = if k = 0 then 1 else 0 := by
    simpa only [zero_add, div_one, Complex.ofReal_one, mul_comm (k : ℝ)] using
      integral_wave_period 0 1 zero_lt_one k
  simp_rw [pair_cubeAdj, wave_sum]
  unfold cubeMeasure
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => wave (x * dPlaq m i))]
  simp_rw [h]
  by_cases hm : IsClosedForm m
  · simp only [hm, ↓reduceIte]
    apply Finset.prod_eq_one
    intro x _
    simp only [show dPlaq m x = 0 from hm x, ↓reduceIte]
  · obtain ⟨x, hx⟩ : ∃ x, dPlaq m x ≠ 0 := not_forall.mp hm
    simp only [hm, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [hx])

/-- Inserting the cube projector into an absolutely summable sector sum. -/
theorem closed_tsum_eq_integral {f : (Plaq R → ℤ) → ℂ} (hf : Summable f) :
    (∑' m : {m : Plaq R → ℤ // IsClosedForm m}, f m.1) =
      ∫ t, ∑' m, f m * wave (∑ p, cubeAdj t p * m p) ∂cubeMeasure (Site R) := by
  classical
  let F (m : Plaq R → ℤ) (t : Site R → ℝ) := f m * wave (∑ p, cubeAdj t p * m p)
  have hn (m t) : ‖F m t‖ = ‖f m‖ := by simp [F]
  have h := hasSum_integral_bounded (μ := cubeMeasure (Site R)) (F := F) hf.norm
    (fun m => by apply Continuous.aestronglyMeasurable; unfold F cubeAdj wave; fun_prop) (fun m => ae_of_all _ fun t => (hn m t).le)
    (ae_of_all _ fun t => (hf.norm.of_norm_bounded fun m => (hn m t).le).hasSum)
  rw [← h.tsum_eq]
  trans ∑' m, {v : Plaq R → ℤ | IsClosedForm v}.indicator f m
  · exact tsum_subtype _ f
  refine tsum_congr fun m => ?_
  simp only [F, integral_const_mul, integral_cube_character, indicator_apply, mem_ofPred_eq]
  split <;> simp_all

end GGOS.Work.GD

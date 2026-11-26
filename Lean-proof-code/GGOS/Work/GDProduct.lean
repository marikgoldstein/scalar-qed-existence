module

public import GGOS.Work.GDPoisson

/-!
# Poisson summation over a finite family of plaquettes
-/

@[expose] public section

namespace GGOS.Work.GD

variable {ι : Type*} [Fintype ι]

noncomputable def gaussProd (u : ℝ) (y : ι → ℝ) (m : ι → ℤ) : ℝ :=
  ∏ i, gauss u ((m i : ℝ) + y i)

noncomputable def coeffProd (u : ℝ) (q : ι → ℝ) (m : ι → ℤ) : ℝ :=
  ∏ i, coeff u ((m i : ℝ) - q i)

theorem gaussProd_pos (u : ℝ) (y : ι → ℝ) (m : ι → ℤ) : 0 < gaussProd u y m :=
  Finset.prod_pos fun _ _ => gauss_pos _ _

theorem coeffProd_pos {u : ℝ} (hu : 0 < u) (q : ι → ℝ) (m : ι → ℤ) : 0 < coeffProd u q m :=
  Finset.prod_pos fun _ _ => coeff_pos hu _

theorem summable_coeffProd {u : ℝ} (hu : 0 < u) (q : ι → ℝ) :
    Summable (coeffProd u q) :=
  summable_prod (f := fun i (k : ℤ) => coeff u (k - q i)) (fun i => summable_coeff hu (q i))

/-- A majorant for the Gaussian product uniform on a rectangular set of displacements. -/
theorem gaussProd_majorant {u : ℝ} (hu : 0 < u) (M : ι → ℝ) :
    ∃ g : (ι → ℤ) → ℝ, Summable g ∧ ∀ (y : ι → ℝ), (∀ i, |y i| ≤ M i) →
      ∀ m, gaussProd u y m ≤ g m := by
  let g (i : ι) (k : ℤ) := Real.exp (Real.pi * u * M i ^ 2) * gauss (u / 2) k
  have hg (i : ι) : Summable (g i) := (summable_gauss (half_pos hu)).mul_left _
  refine ⟨fun m => ∏ i, g i (m i), summable_prod hg, fun y hy m => ?_⟩
  exact Finset.prod_le_prod (fun _ _ => (gauss_pos _ _).le) (fun i _ => gauss_shift_le hu (hy i) _)

theorem poisson_prod {u : ℝ} (hu : 0 < u) (y q : ι → ℝ) :
    (∑' m : ι → ℤ, (gaussProd u y m : ℂ) * wave (∑ i, q i * m i)) =
      ∑' m : ι → ℤ, (coeffProd u q m : ℂ) * wave (∑ i, ((m i : ℝ) - q i) * y i) := by
  have h₁ (i : ι) : Summable (fun k : ℤ => (gauss u (k + y i) : ℂ) * wave (q i * k)) := by
    apply (summable_gauss_shift hu (y i)).of_norm_bounded
    intro k
    simp [Real.norm_of_nonneg (gauss_pos _ _).le]
  have h₂ (i : ι) : Summable (fun k : ℤ => (coeff u (k - q i) : ℂ) *
      wave ((k - q i) * y i)) := by
    apply (summable_coeff hu (q i)).of_norm_bounded
    intro k
    simp [Real.norm_of_nonneg (coeff_pos hu _).le]
  simp only [gaussProd, coeffProd, Complex.ofReal_prod, wave_sum, ← Finset.prod_mul_distrib]
  rw [tsum_prod h₁, tsum_prod h₂]
  simp_rw [poisson_gauss hu]

end GGOS.Work.GD

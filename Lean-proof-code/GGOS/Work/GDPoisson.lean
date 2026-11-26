module

public import GGOS.Work.GDFourier

/-!
# Poisson transformation of a shifted, modulated lattice Gaussian
-/

@[expose] public section

open Real

namespace GGOS.Work.GD

/-- The Gaussian in lattice units. -/
noncomputable def gauss (u x : ℝ) : ℝ := Real.exp (-π * u * x ^ 2)

/-- Its Fourier transform, evaluated at the dual frequency. -/
noncomputable def coeff (u x : ℝ) : ℝ := (1 / u ^ (1 / 2 : ℝ)) * gauss u⁻¹ x

theorem gauss_pos (u x : ℝ) : 0 < gauss u x := Real.exp_pos _

theorem coeff_pos {u : ℝ} (hu : 0 < u) (x : ℝ) : 0 < coeff u x :=
  mul_pos (one_div_pos.mpr (Real.rpow_pos_of_pos hu _)) (gauss_pos _ _)

theorem summable_gauss {u : ℝ} (hu : 0 < u) :
    Summable (fun k : ℤ => gauss u k) := by
  refine (summable_pow_mul_jacobiTheta₂_term_bound 0 hu 0).congr fun k => ?_
  simp [gauss, mul_assoc]

/-- A single summable envelope works for all displacements in a bounded interval. -/
theorem gauss_shift_le {u x M : ℝ} (hu : 0 < u) (hx : |x| ≤ M) (k : ℤ) :
    gauss u ((k : ℝ) + x) ≤ Real.exp (π * u * M ^ 2) * gauss (u / 2) k := by
  have hx2 := sq_le_sq' (abs_le.mp hx).1 (abs_le.mp hx).2
  unfold gauss
  rw [← Real.exp_add, Real.exp_le_exp]
  have h : ((k : ℝ) + x) ^ 2 + M ^ 2 ≥ (k : ℝ) ^ 2 / 2 := by
    nlinarith only [sq_nonneg ((k : ℝ) + 2 * x), hx2]
  nlinarith only [mul_le_mul_of_nonneg_left h (mul_pos pi_pos hu).le]

theorem summable_gauss_shift {u : ℝ} (hu : 0 < u) (x : ℝ) :
    Summable (fun k : ℤ => gauss u ((k : ℝ) + x)) := by
  apply ((summable_gauss (half_pos hu)).mul_left (Real.exp (π * u * |x| ^ 2))).of_norm_bounded
  intro k
  rw [Real.norm_of_nonneg (gauss_pos _ _).le]
  exact gauss_shift_le hu le_rfl k

theorem summable_coeff {u : ℝ} (hu : 0 < u) (s : ℝ) :
    Summable (fun k : ℤ => coeff u ((k : ℝ) - s)) :=
  (summable_gauss_shift (inv_pos.mpr hu) (-s)).mul_left _

/-- The one-dimensional Poisson step of [GG-OS] (3.2), after completing the square.
Both phase variables are in units of a full turn. -/
theorem poisson_gauss {u : ℝ} (hu : 0 < u) (x s : ℝ) :
    (∑' k : ℤ, (gauss u (k + x) : ℂ) * wave (s * k)) =
      ∑' m : ℤ, (coeff u (m - s) : ℂ) * wave ((m - s) * x) := by
  let b : ℂ := -(u : ℂ) * x + Complex.I * s
  let A := Complex.exp (-(π : ℂ) * u * x ^ 2)
  have hi (m : ℤ) :
      (m : ℂ) + Complex.I * b = m - s - Complex.I * (u * x : ℂ) := by
    dsimp [b]
    ring_nf
    rw [Complex.I_sq]
    ring
  have h₁ (k : ℤ) : (gauss u (k + x) : ℂ) * wave (s * k) =
      A * Complex.exp (-(π : ℂ) * u * k ^ 2 + 2 * π * b * k) := by
    unfold gauss wave A b
    push_cast
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have h₂ (m : ℤ) : A * Complex.exp (-(π : ℂ) / u * (m + Complex.I * b) ^ 2) =
      (gauss u⁻¹ (m - s) : ℂ) * wave ((m - s) * x) := by
    rw [hi]
    unfold gauss wave A
    push_cast
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    field_simp [Complex.ofReal_ne_zero.mpr hu.ne']
    ring_nf
    rw [Complex.I_sq]
    ring
  simp_rw [h₁]
  rw [tsum_mul_left, Complex.tsum_exp_neg_quadratic (a := (u : ℂ)) hu b, mul_left_comm,
    ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro m
  rw [h₂, coeff, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_cpow hu.le, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    mul_assoc]

end GGOS.Work.GD

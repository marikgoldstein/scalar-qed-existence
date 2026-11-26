module

public import GGOS.Work.TorusSymmetryBoundary
public import GGOS.Frozen.Defs.Weight

/-!
# Invariance of the site, hopping and curvature factors
-/

public section

noncomputable section

namespace GGOS.TorusSymmetry

private theorem phase_reverse (a b : ℂ) (t : ℝ) :
    ‖Complex.exp (Complex.I * ((-t : ℝ) : ℂ)) * a - b‖ =
      ‖Complex.exp (Complex.I * (t : ℂ)) * b - a‖ := by
  let z := Complex.exp (Complex.I * (t : ℂ))
  have hz : ‖z‖ = 1 := Complex.norm_exp_I_mul_ofReal t
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  simp only [Complex.ofReal_neg, mul_neg, Complex.exp_neg]
  change ‖z⁻¹ * a - b‖ = ‖z * b - a‖
  calc
    ‖z⁻¹ * a - b‖ = ‖z * (z⁻¹ * a - b)‖ := by rw [norm_mul, hz, one_mul]
    _ = ‖a - z * b‖ := by rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hz0, one_mul]
    _ = ‖z * b - a‖ := norm_sub_rev _ _

theorem hop_reverse (c : Coeffs) (r r' θ : ℝ) : hop c r' r (-θ) = hop c r r' θ := by
  simp only [hop, mul_neg, phase_reverse]

private theorem hop_bondField {R : Type*} [CommRing R] (c : Coeffs) (g : LatSym R)
    (ρ : Site R → ℝ) (B : Bond R → ℝ) (b : Bond R) :
    hop c (ρ (g.act b.1)) (ρ (g.act (b.1 + unitVec R b.2))) (bondField g B b) =
      hop c (ρ (bondEquiv g b).1) (ρ ((bondEquiv g b).1 + unitVec R (bondEquiv g b).2))
        (B (bondEquiv g b)) := by
  obtain ⟨x,i⟩ := b
  change hop c (ρ (g.act x)) (ρ (g.act (x + unitVec R i)))
    (sign (g.sgn i) (B (g.act x + g.corner i, g.perm i))) =
    hop c (ρ (g.act x + g.corner i)) (ρ (g.act x + g.corner i + unitVec R (g.perm i)))
      (B (g.act x + g.corner i, g.perm i))
  rw [act_add_unitVec]
  by_cases h : g.sgn i = 1 <;> simp [sign, LatSym.corner, h, hop_reverse]

private theorem faceSign_sq {R : Type*} [CommRing R] (g : LatSym R) (d : Dir2) (a : ℝ) :
    (faceSign g d a) ^ 2 = a ^ 2 := by
  by_cases ho : g.perm d.1.1 < g.perm d.1.2 <;>
    by_cases hi : g.sgn d.1.1 = 1 <;> by_cases hj : g.sgn d.1.2 = 1 <;>
    simp [faceSign, sign, ho, hi, hj]

theorem weight_invariant (s : Side) (c : Coeffs) (g : LatSym (ZMod s.n))
    (ρ : Site (ZMod s.n) → ℝ) (B : Bond (ZMod s.n) → ℝ) (m : Plaq (ZMod s.n) → ℤ) :
    weight s c (fun x => ρ (g.act x)) (bondField g B) (faceField g m) = weight s c ρ B m := by
  unfold weight
  simp_rw [hop_bondField, curv_bondField, faceField_apply, faceSign_sq]
  exact congrArg₂ (· * ·)
    (congrArg₂ (· * ·) ((siteEquiv g).prod_comp fun x => siteFactor c (ρ x))
      ((bondEquiv g).prod_comp fun b => hop c (ρ b.1) (ρ (b.1 + unitVec _ b.2)) (B b)))
    ((plaqEquiv g).prod_comp fun p => Real.exp (-(curv c B m p) ^ 2 / 2))

end GGOS.TorusSymmetry

end

end

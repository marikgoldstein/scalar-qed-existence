module

public import Mathlib
public import GGOS.Frozen.Defs.BasisE
public import GGOS.Frozen.Defs.LatSymAct
public import GGOS.Frozen.Defs.MkT
public import GGOS.Infra.Alg
public import GGOS.Infra.LatSym
public import GGOS.Infra.T

/-!
# Euclidean motions with linear part in the cubic group, and their action on test pairs

A motion `x ↦ O x + y` of `ℝ³` with `O` a signed permutation matrix is a `LatSym ℝ`: it acts on
points by `LatSym.act`, on test pairs by push-forward (the 2-form as a 2-form), and on the algebra
by `γ e_σ = e_{γσ}` ([GG-OS] Section 9, "Euclidean invariance without rotations").
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The inverse of the motion `x ↦ g x`. -/
def LatSym.invAct {R : Type*} [CommRing R] (g : LatSym R) (y : Site R) : Site R :=
  fun μ => (((g.sgn μ : ℤˣ) : ℤ) : R) * (y (g.perm μ) - g.shift (g.perm μ))

theorem LatSym.invAct_act {R : Type*} [CommRing R] (g : LatSym R) (x : Site R) :
    g.invAct (g.act x) = x := by
  funext i
  rcases Int.units_eq_one_or (g.sgn i) with h | h <;> simp [LatSym.invAct, LatSym.act, h]

theorem LatSym.act_invAct {R : Type*} [CommRing R] (g : LatSym R) (y : Site R) :
    g.act (g.invAct y) = y := by
  funext j
  obtain ⟨i, rfl⟩ := g.perm.surjective j
  rcases Int.units_eq_one_or (g.sgn i) with h | h <;> simp [LatSym.invAct, LatSym.act, h]

theorem LatSym.contDiff_invAct (g : LatSym ℝ) : ContDiff ℝ smoothTop (g.invAct : E3 → E3) :=
  contDiff_pi.2 fun i => contDiff_const.mul ((contDiff_apply ℝ ℝ (g.perm i)).sub contDiff_const)

theorem LatSym.contDiff_act (g : LatSym ℝ) : ContDiff ℝ smoothTop (g.act : E3 → E3) :=
  contDiff_pi.2 fun i =>
    (contDiff_const.mul (contDiff_apply ℝ ℝ (g.perm.symm i))).add contDiff_const

/-- The inverse motion as a homeomorphism. -/
def LatSym.invHomeo (g : LatSym ℝ) : E3 ≃ₜ E3 where
  toFun := g.invAct
  invFun := g.act
  left_inv := g.act_invAct
  right_inv := g.invAct_act
  continuous_toFun := g.contDiff_invAct.continuous
  continuous_invFun := g.contDiff_act.continuous

/-- The push-forward of a test pair `σ = (f, h)` under the motion `g`, `O e_μ = sgn μ • e_{perm μ}`:
`(g f)_{αβ}(ξ) = ∑_{μν} O_{αμ} O_{βν} f_{μν}(g⁻¹ ξ)` and `(g h)(ξ) = h(g⁻¹ ξ)`. -/
def pushT (g : LatSym ℝ) (σ : T) : T :=
  mkT (fun α β ξ => (((g.sgn (g.perm.symm α) * g.sgn (g.perm.symm β) : ℤˣ) : ℤ) : ℝ) *
      σ.1.1 (g.perm.symm α) (g.perm.symm β) (g.invAct ξ), fun ξ => σ.1.2 (g.invAct ξ))
    { antisymm := by
        intro α β x
        change _ * _ = -(_ * _)
        rw [σ.isTestPair.antisymm (g.perm.symm α) (g.perm.symm β) (g.invAct x), mul_comm
          (g.sgn (g.perm.symm α)) (g.sgn (g.perm.symm β)), mul_neg]
      smooth_f := fun α β =>
        contDiff_const.mul ((σ.isTestPair.smooth_f _ _).comp g.contDiff_invAct)
      compact_f := fun α β =>
        ((σ.isTestPair.compact_f _ _).comp_homeomorph g.invHomeo).mul_left
      smooth_h := σ.isTestPair.smooth_h.comp g.contDiff_invAct
      compact_h := σ.isTestPair.compact_h.comp_homeomorph g.invHomeo }

/-- `γ e_σ = e_{γσ}`, extended linearly to `𝒜`. -/
def pushA (g : LatSym ℝ) (a : Alg) : Alg := AddMonoidAlgebra.mapDomain (pushT g) a

/-- The reflection `x_j ↦ 2c - x_j` of `ℝ³` in the plane `{x_j = c}`. -/
def reflPlane (j : Fin 3) (c : ℝ) : LatSym ℝ where
  perm := Equiv.refl _
  sgn := Function.update (fun _ => 1) j (-1)
  shift := Pi.single j (2 * c)

/-- The antilinear map `Θ_{j,c}`, `Θ_{j,c} e_σ = e_{-γσ}` with `γ` the reflection in `{x_j = c}`. -/
def ThetaPlane (j : Fin 3) (c : ℝ) (a : Alg) : Alg :=
  AddMonoidAlgebra.mapDomain (fun σ => -pushT (reflPlane j c) σ)
    (AddMonoidAlgebra.ofCoeff (a.coeff.mapRange (starRingEnd ℂ) (map_zero _)))

/-- `σ` is supported in the open half space `{x_j > c}`. -/
def SupportedAbove (j : Fin 3) (c : ℝ) (σ : T) : Prop :=
  (∀ μ ν, tsupport (σ.1.1 μ ν) ⊆ {ξ : E3 | c < ξ j}) ∧ tsupport σ.1.2 ⊆ {ξ : E3 | c < ξ j}

/-- `𝒜_+^{(j,c)}`: the span of the `e_σ` with `σ` supported in `{x_j > c}`. -/
def AplusPlane (j : Fin 3) (c : ℝ) : Submodule ℂ Alg :=
  Submodule.span ℂ {a | ∃ σ, SupportedAbove j c σ ∧ a = basisE σ}

end GGOS

end

end

module

public import Mathlib
public import GGOS.Frozen.Defs.BasisE
public import GGOS.Frozen.Defs.IsLimitPoint
public import GGOS.Frozen.Defs.MkT
public import GGOS.Frozen.Defs.Transl
public import GGOS.Infra.Alg
public import GGOS.Infra.T

/-!
# Rotations of test pairs, OS1 with rotations, and limit points along dyadic sequences of sides

The transport of a test pair by `O ∈ O(3)` ([GG-OS] Definition 12.7), the axiom OS1 for the whole
Euclidean group, and the limit points of the torus states along a dyadic sequence of sides
([GG-OS] Definition 14.1).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The orthogonal group `O(3)`. -/
abbrev O3 := Matrix.orthogonalGroup (Fin 3) ℝ

/-- `x ↦ O x`. -/
def O3.act (O : O3) (x : E3) : E3 := Matrix.mulVec (O : Matrix (Fin 3) (Fin 3) ℝ) x

/-- `x ↦ O⁻¹ x = Oᵀ x`. -/
def O3.invAct (O : O3) (x : E3) : E3 := Matrix.mulVec (O : Matrix (Fin 3) (Fin 3) ℝ).transpose x

theorem O3.act_invAct (O : O3) (x : E3) : O3.act O (O3.invAct O x) = x := by
  unfold O3.act O3.invAct
  rw [Matrix.mulVec_mulVec, (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp O.2, Matrix.one_mulVec]

theorem O3.invAct_act (O : O3) (x : E3) : O3.invAct O (O3.act O x) = x := by
  unfold O3.act O3.invAct
  rw [Matrix.mulVec_mulVec, (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp O.2, Matrix.one_mulVec]

theorem contDiff_mulVec (M : Matrix (Fin 3) (Fin 3) ℝ) :
    ContDiff ℝ smoothTop (fun x : E3 => Matrix.mulVec M x) := by
  refine contDiff_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℝ j)

/-- `x ↦ O⁻¹ x` as a homeomorphism. -/
def O3.invHomeo (O : O3) : E3 ≃ₜ E3 where
  toFun := O3.invAct O
  invFun := O3.act O
  left_inv := O3.act_invAct O
  right_inv := O3.invAct_act O
  continuous_toFun := (contDiff_mulVec _).continuous
  continuous_invFun := (contDiff_mulVec _).continuous

theorem hasCompactSupport_sum_fin3 {g : Fin 3 → E3 → ℝ} (h : ∀ i, HasCompactSupport (g i)) :
    HasCompactSupport (fun x => ∑ i, g i x) := by
  have e : (fun x => ∑ i, g i x) = g 0 + g 1 + g 2 := by
    funext x
    simp [Fin.sum_univ_three]
  rw [e]
  exact ((h 0).add (h 1)).add (h 2)

theorem rot_antisymm (O : Matrix (Fin 3) (Fin 3) ℝ) (f : Fin 3 → Fin 3 → ℝ)
    (hf : ∀ μ ν, f μ ν = -f ν μ) (α β : Fin 3) :
    ∑ μ, ∑ ν, O α μ * O β ν * f μ ν = -(∑ μ, ∑ ν, O β μ * O α ν * f μ ν) := by
  have h1 : ∑ μ, ∑ ν, O β μ * O α ν * f μ ν = ∑ μ, ∑ ν, O β ν * O α μ * f ν μ :=
    Finset.sum_comm
  rw [h1, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [hf ν μ]
  ring

/-- The components of the transported 2-form. -/
def rotF (O : O3) (σ : T) (α β : Fin 3) (x : E3) : ℝ :=
  ∑ μ, ∑ ν, (O : Matrix (Fin 3) (Fin 3) ℝ) α μ * (O : Matrix (Fin 3) (Fin 3) ℝ) β ν *
    σ.1.1 μ ν (O3.invAct O x)

theorem rotF_smooth (O : O3) (σ : T) (α β : Fin 3) : ContDiff ℝ smoothTop (rotF O σ α β) := by
  unfold rotF
  refine ContDiff.sum fun μ _ => ContDiff.sum fun ν _ => ?_
  exact contDiff_const.mul ((σ.isTestPair.smooth_f μ ν).comp (contDiff_mulVec _))

theorem rotF_compact (O : O3) (σ : T) (α β : Fin 3) : HasCompactSupport (rotF O σ α β) := by
  have hterm (μ ν : Fin 3) : HasCompactSupport (fun x =>
      (O : Matrix (Fin 3) (Fin 3) ℝ) α μ * (O : Matrix (Fin 3) (Fin 3) ℝ) β ν *
        σ.1.1 μ ν (O3.invAct O x)) := by
    have h := ((σ.isTestPair.compact_f μ ν).comp_homeomorph (O3.invHomeo O)).mul_left
      (f := fun _ : E3 => (O : Matrix (Fin 3) (Fin 3) ℝ) α μ * (O : Matrix (Fin 3) (Fin 3) ℝ) β ν)
    exact h
  have hrow (μ : Fin 3) : HasCompactSupport (fun x => ∑ ν,
      (O : Matrix (Fin 3) (Fin 3) ℝ) α μ * (O : Matrix (Fin 3) (Fin 3) ℝ) β ν *
        σ.1.1 μ ν (O3.invAct O x)) :=
    hasCompactSupport_sum_fin3 (g := fun ν x => (O : Matrix (Fin 3) (Fin 3) ℝ) α μ *
      (O : Matrix (Fin 3) (Fin 3) ℝ) β ν * σ.1.1 μ ν (O3.invAct O x)) (hterm μ)
  exact hasCompactSupport_sum_fin3 (g := fun μ x => ∑ ν,
      (O : Matrix (Fin 3) (Fin 3) ℝ) α μ * (O : Matrix (Fin 3) (Fin 3) ℝ) β ν *
        σ.1.1 μ ν (O3.invAct O x)) hrow

theorem rotF_antisymm (O : O3) (σ : T) (α β : Fin 3) (x : E3) :
    rotF O σ α β x = -rotF O σ β α x :=
  rot_antisymm (O : Matrix (Fin 3) (Fin 3) ℝ) (fun μ ν => σ.1.1 μ ν (O3.invAct O x))
    (fun μ ν => σ.isTestPair.antisymm μ ν _) α β

/-- The transport `O · σ` of a test pair by `O ∈ O(3)` ([GG-OS] Definition 12.7): the push-forward,
`(O·f)_{αβ}(x) = ∑_{μν} O_{αμ} O_{βν} f_{μν}(O⁻¹ x)` (the 2-form transforming as a 2-form) and
`(O·h)(x) = h(O⁻¹ x)`. -/
def rotT (O : O3) (σ : T) : T :=
  mkT (rotF O σ, fun x => σ.1.2 (O3.invAct O x))
    { antisymm := rotF_antisymm O σ
      smooth_f := rotF_smooth O σ
      compact_f := rotF_compact O σ
      smooth_h := σ.isTestPair.smooth_h.comp (contDiff_mulVec _)
      compact_h := σ.isTestPair.compact_h.comp_homeomorph (O3.invHomeo O) }

/-- OS1: invariance under the whole Euclidean group, every motion `x ↦ O x + y` with `O ∈ O(3)`. -/
def OS1 (S : Alg →ₗ[ℂ] ℂ) : Prop :=
  ∀ (O : O3) (y : E3) (σ : T), S (basisE (transl y (rotT O σ))) = S (basisE σ)

/-- [GG-OS] Definition 14.1 at level `N`: `ω` is a limit point of the torus states along a dyadic
sequence of sides `L_n = 2^{k_n} L_*` (`k` increasing), with `L_* = n_* ε_N` and `L_*/2 ∈ a_0 ℤ`,
that is `n_* = 2 j 5^N` sites per side. The convergence clauses are those of `GGOS.IsLimitPoint`. -/
def IsDyadicLimitPoint (N : ℕ) (c : Coeffs) (ω : (Cfg ℤ → ℂ) → ℂ) : Prop :=
  ∃ (L : ℕ → Side) (μ : Measure (Cfg ℤ)) (j : ℕ) (k : ℕ → ℕ), 0 < j ∧ StrictMono k ∧
    (∀ n, (L n).n = 2 ^ k n * (2 * j * 5 ^ N)) ∧
    IsProbabilityMeasure μ ∧ μ (OmegaN c.ρ0)ᶜ = 0 ∧
    (∀ F : Cfg ℤ → ℂ, IsLocal F → Continuous F → (∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) →
      Tendsto (fun n => ∫ x, F (per (L n).n x) ∂(torusState (L n) c)) atTop
        (𝓝 (∫ x, F x ∂μ))) ∧
    ∀ F : Cfg ℤ → ℂ, IsBBL F → ω F = ∫ x, F x ∂μ

end GGOS

end

end

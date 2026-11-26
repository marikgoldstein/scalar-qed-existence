module

public import Mathlib
public import GGOS.Frozen.Defs.BasisE
public import GGOS.Infra.Alg
public import GGOS.Infra.Ambient
public import GGOS.Infra.T
public import GGOS.OS.Schwinger

/-!
# Schwartz 2-forms, and OS0 on Schwartz test functions

[GG-OS] Theorem 9.4 (i), (iii), for the curvature: the generating functional and the Schwinger
functions extend from smooth compactly supported 2-forms to Schwartz 2-forms.
-/

@[expose] public section

noncomputable section

namespace GGOS

/-- Real Schwartz 2-forms on `ℝ³`: antisymmetric matrices of Schwartz functions. -/
def schwartzForms : Submodule ℝ (Fin 3 → Fin 3 → SchwartzMap E3 ℝ) where
  carrier := {g | ∀ μ ν, g μ ν = -g ν μ}
  add_mem' := by
    intro a b ha hb μ ν
    change a μ ν + b μ ν = -(a ν μ + b ν μ)
    rw [ha μ ν, hb μ ν, neg_add]
  zero_mem' := by
    intro μ ν
    change (0 : SchwartzMap E3 ℝ) = -0
    rw [neg_zero]
  smul_mem' := by
    intro r a ha μ ν
    change r • a μ ν = -(r • a ν μ)
    rw [ha μ ν, smul_neg]

/-- `sup_x (1 + |x|²)² max_{μν} |g_{μν}(x)|`, the norm of `OS0.tempered`, for a Schwartz 2-form. -/
def formWeightNorm (g : schwartzForms) : ℝ :=
  ⨆ x : E3, (1 + ∑ i, x i ^ 2) ^ 2 *
    Finset.univ.sup' Finset.univ_nonempty fun q : Fin 3 × Fin 3 =>
      |(g : Fin 3 → Fin 3 → SchwartzMap E3 ℝ) q.1 q.2 x|

/-- OS0 on Schwartz test functions, for the curvature ([GG-OS] Theorem 9.4 (i), (iii)): the generating
functional extends to a continuous function on Schwartz 2-forms, and every curvature Schwinger
function extends to a continuous multilinear form on Schwartz 2-forms (a tempered distribution), with
the bound (E0′) of `OS0.tempered` and the same constant `C`. -/
def OS0Schwartz (C : ℝ) (S : Alg →ₗ[ℂ] ℂ) : Prop :=
  (∃ Z : schwartzForms → ℂ, Continuous Z ∧
      ∀ (g : schwartzForms) (σ : T), σ.1.2 = 0 →
        (∀ μ ν x, (g : Fin 3 → Fin 3 → SchwartzMap E3 ℝ) μ ν x = σ.1.1 μ ν x) →
          Z g = S (basisE σ)) ∧
    ∀ n : ℕ, ∃ Sh : ContinuousMultilinearMap ℝ (fun _ : Fin n => schwartzForms) ℝ,
      (∀ (g : Fin n → schwartzForms) (σ : Fin n → T),
        (∀ i, (σ i).1.2 = 0 ∧
          ∀ μ ν x, ((g i : schwartzForms) : Fin 3 → Fin 3 → SchwartzMap E3 ℝ) μ ν x = (σ i).1.1 μ ν x) →
            ((Sh g : ℝ) : ℂ) = schwinger S σ) ∧
      ∀ g : Fin n → schwartzForms,
        |Sh g| ≤ C ^ n * Real.sqrt n.factorial * ∏ i, formWeightNorm (g i)

end GGOS

end

end

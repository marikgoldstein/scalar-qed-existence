module

public import Mathlib
public import GGOS.Frozen.Defs.BasisE
public import GGOS.Infra.Alg
public import GGOS.Infra.T

/-!
# The generating functional and the Schwinger functions of a functional on the algebra
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- The generating function `t ↦ S(e_{∑_j t_j σ_j})`, `t ∈ ℝⁿ`, of a finite family of test pairs. -/
def genFun (S : Alg →ₗ[ℂ] ℂ) {n : ℕ} (σ : Fin n → T) (t : Fin n → ℝ) : ℂ :=
  S (basisE (∑ j, t j • σ j))

/-- The Schwinger function `S_n(σ_1, …, σ_n) = (-i)ⁿ ∂_{t_1} ⋯ ∂_{t_n} S(e_{∑_j t_j σ_j})` at
`t = 0`: the `n`-point function of the smeared field, read off from the generating functional. -/
def schwinger (S : Alg →ₗ[ℂ] ℂ) {n : ℕ} (σ : Fin n → T) : ℂ :=
  (-Complex.I) ^ n * iteratedFDeriv ℝ n (genFun S σ) 0 (fun j => Pi.single j 1)

/-- The weighted sup norm `sup_x (1 + |x|²)² max(|f_{μν}(x)|, |h(x)|)` of a test pair, the larger of
the two norms `‖f‖_w`, `‖h‖_w` of [GG-OS] Section 9; component by component it is the derivative-free
term of the Schwartz norm `|·|_4` of Osterwalder and Schrader. -/
def weightNorm (σ : T) : ℝ :=
  ⨆ x : E3, (1 + ∑ i, x i ^ 2) ^ 2 *
    max (Finset.univ.sup' Finset.univ_nonempty fun q : Fin 3 × Fin 3 => |σ.1.1 q.1 q.2 x|) |σ.1.2 x|

end GGOS

end

end

module

public import Mathlib
public import GGOS.Frozen.Defs.Enorm
public import GGOS.Frozen.Defs.PairNorm
public import GGOS.Frozen.Defs.Phi
public import GGOS.Frozen.Defs.Rnorm
public import GGOS.Frozen.Defs.SupNorm
public import GGOS.Infra.IsBBL
public import GGOS.OS.LimitFunctionalDef
public import GGOS.Infra.Motion
public import GGOS.OS.Schwinger

/-!
# The Osterwalder–Schrader axioms OS0, OS1 without rotations, OS2 and OS3 for a functional

From [GG-OS] Section 9: Theorem 9.4 (OS0), Proposition 9.6 (OS1, rotations excepted), Propositions
9.9 and 9.11 (OS2), Proposition 9.12 (OS3).  The clauses taken from Theorem 9.4 (ii), (iii) and from
Propositions 9.11 and 9.12 (a), which are printed for the curvature, are stated for the joint field of
the curvature and of the bounded density function (`OS0.two_point` and `OS3.odd` for the curvature
alone), with the norm `‖(f, h)‖ = R(f) + ‖g_d‖_∞ E(h)` of Definition 4.1, and for real `C_c^∞` test
pairs.  Not stated: `0 ≤ Z(f, 0) ≤ 1`, the extension to Schwartz or complex test functions, rotations,
OS4, the measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ComplexOrder

namespace GGOS

/-- The charge conjugation of a test pair, `(f, h) ↦ (-f, h)`. -/
def chargeT (σ : T) : T :=
  mkT (fun μ ν ξ => -σ.1.1 μ ν ξ, σ.1.2)
    { antisymm := fun μ ν x => congrArg Neg.neg (σ.isTestPair.antisymm μ ν x)
      smooth_f := fun μ ν => (σ.isTestPair.smooth_f μ ν).neg
      compact_f := fun μ ν => (σ.isTestPair.compact_f μ ν).neg
      smooth_h := σ.isTestPair.smooth_h
      compact_h := σ.isTestPair.compact_h }

/-- OS0, regularity ([GG-OS], from Theorem 9.4 (i)-(iii); real test pairs).  `C` is the constant of
`tempered`. -/
structure OS0 (sc : Scale) (N0 : ℕ) (gd : DensityFn) (C : ℝ) (S : Alg →ₗ[ℂ] ℂ) : Prop where
  /-- normalisation -/
  one : S (basisE 0) = 1
  /-- continuity of the generating functional in the norm of Definition 4.1 -/
  continuity : ∀ σ τ : T, ‖S (basisE σ) - S (basisE τ)‖ ≤ pairNorm sc N0 gd (σ - τ)
  /-- the generating function of every finite family extends to an entire function `Ψ` with
  `|Ψ(z)| ≤ Ψ(Re z)`, and with a Gaussian bound times the exponential of the density part -/
  entire : ∀ (k : ℕ) (σ : Fin k → T), ∃ Ψ : (Fin k → ℂ) → ℂ, Differentiable ℂ Ψ ∧
    (∀ t : Fin k → ℝ, Ψ (fun j => Complex.I * (t j : ℂ)) = genFun S σ t) ∧
    (∀ z : Fin k → ℂ, ‖Ψ z‖ ≤ (Ψ fun j => ((z j).re : ℂ)).re) ∧
    ∀ z : Fin k → ℂ, ‖Ψ z‖ ≤ Real.exp (1 / 2 * (∑ j, |(z j).re| * Rnorm sc N0 (σ j)) ^ 2
      + supNorm gd * ∑ j, |(z j).re| * Enorm sc N0 (σ j))
  /-- the growth condition of the Schwinger functions in the norm of Definition 4.1 -/
  growth : ∀ (n : ℕ) (σ : Fin n → T),
    ‖schwinger S σ‖ ≤ Real.exp n * Real.sqrt n.factorial * ∏ i, pairNorm sc N0 gd (σ i)
  /-- the Osterwalder–Schrader growth condition (E0′), in product form on real `C_c^∞` test pairs, with
  the constant `C`; the extension to Schwartz functions is not stated -/
  tempered : ∀ (n : ℕ) (σ : Fin n → T),
    ‖schwinger S σ‖ ≤ C ^ n * Real.sqrt n.factorial * ∏ i, weightNorm (σ i)
  /-- `S_2(f, f) ≤ R(f)²` for the curvature -/
  two_point : ∀ σ : T, σ.1.2 = 0 → ‖schwinger S ![σ, σ]‖ ≤ Rnorm sc N0 σ ^ 2

/-- OS1 without rotations: invariance under all translations of `ℝ³`, the reflections in the
coordinate planes and the cubic group about every point ([GG-OS] Proposition 9.6). -/
structure OS1Cubic (S : Alg →ₗ[ℂ] ℂ) : Prop where
  /-- invariance of the functional -/
  invariant : ∀ (g : LatSym ℝ) (a : Alg), S (pushA g a) = S a
  /-- invariance of the Schwinger functions -/
  schwinger_invariant : ∀ (g : LatSym ℝ) (n : ℕ) (σ : Fin n → T),
    schwinger S (fun i => pushT g (σ i)) = schwinger S σ

/-- OS2, reflection positivity, for the reflection in every plane `{x_j = c}`
([GG-OS] Propositions 9.9 and 9.11; for real test pairs, the latter extended to the joint field). -/
structure OS2 (S : Alg →ₗ[ℂ] ℂ) : Prop where
  /-- the reflection of the functional -/
  conj : ∀ (j : Fin 3) (c : ℝ) (a : Alg), S (ThetaPlane j c a) = starRingEnd ℂ (S a)
  /-- the form `⟨a, b⟩ = S(Θ a · b)` is Hermitian -/
  hermitian : ∀ (j : Fin 3) (c : ℝ) (a b : Alg),
    S (ThetaPlane j c a * b) = starRingEnd ℂ (S (ThetaPlane j c b * a))
  /-- the form is positive semidefinite on `𝒜_+` -/
  nonneg : ∀ (j : Fin 3) (c : ℝ), ∀ a ∈ AplusPlane j c, 0 ≤ S (ThetaPlane j c a * a)
  /-- positivity for polynomials of the field: for `P = ∑_α c_α ∏_i Φ(σ_{αi})` with sources in
  `{x_j > c}`, `S(θ(P) P) ≥ 0` -/
  polynomial : ∀ (j : Fin 3) (c : ℝ) (m : ℕ) (d : Fin m → ℕ)
    (σ : (α : Fin m) → Fin (d α) → T) (_ : ∀ α i, SupportedAbove j c (σ α i)) (w : Fin m → ℂ),
    0 ≤ ∑ α, ∑ β, starRingEnd ℂ (w α) * w β *
      schwinger S (Fin.append (fun i => pushT (reflPlane j c) (σ α i)) (σ β))

/-- OS3, symmetry ([GG-OS], from Proposition 9.12): the Schwinger functions are symmetric, multilinear and
real on real test pairs; the generating functional is invariant under charge conjugation, and the
curvature Schwinger functions of odd order vanish. -/
structure OS3 (S : Alg →ₗ[ℂ] ℂ) : Prop where
  symmetric : ∀ (n : ℕ) (π : Equiv.Perm (Fin n)) (σ : Fin n → T),
    schwinger S (fun i => σ (π i)) = schwinger S σ
  map_add : ∀ (n : ℕ) (σ : Fin n → T) (i : Fin n) (τ τ' : T),
    schwinger S (Function.update σ i (τ + τ')) =
      schwinger S (Function.update σ i τ) + schwinger S (Function.update σ i τ')
  map_smul : ∀ (n : ℕ) (σ : Fin n → T) (i : Fin n) (r : ℝ) (τ : T),
    schwinger S (Function.update σ i (r • τ)) = (r : ℂ) * schwinger S (Function.update σ i τ)
  real : ∀ (n : ℕ) (σ : Fin n → T), (schwinger S σ).im = 0
  charge : ∀ σ : T, S (basisE (chargeT σ)) = S (basisE σ)
  odd : ∀ (n : ℕ) (_ : Odd n) (σ : Fin n → T), (∀ i, (σ i).1.2 = 0) → schwinger S σ = 0

end GGOS

end

end

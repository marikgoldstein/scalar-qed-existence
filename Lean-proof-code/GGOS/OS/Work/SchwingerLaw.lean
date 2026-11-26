module

public import GGOS.OS.Work.Moments

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# The Schwinger functions are the moments of the limit laws
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace GGOS.OS

variable {sc : Scale} {N0 : ℕ} {gd : DensityFn} {S : Alg →ₗ[ℂ] ℂ}

theorem genFun_eq {n : ℕ} {σ : Fin n → T} {ν : Measure (EuclideanSpace ℝ (Fin n))}
    (h : IsLaw sc N0 gd S σ ν) :
    genFun S σ = charFun ν ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm := by
  funext t
  exact (h.char _).symm

/-- The Schwinger function is the mixed moment of the law of the family. -/
theorem schwinger_eq {n : ℕ} {σ : Fin n → T} {ν : Measure (EuclideanSpace ℝ (Fin n))}
    (h : IsLaw sc N0 gd S σ ν) : schwinger S σ = ((∫ x, ∏ i, x i ∂ν : ℝ) : ℂ) := by
  have hp := h.prob
  have hm := h.expBounded.memLp n
  have hcd : ContDiff ℝ n (charFun ν) := contDiff_charFun hm
  let L : (Fin n → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n) := (EuclideanSpace.equiv (Fin n) ℝ).symm
  have h1 : iteratedFDeriv ℝ n (genFun S σ) 0 =
      (iteratedFDeriv ℝ n (charFun ν) (L 0)).compContinuousLinearMap
        fun _ => (L : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n)) := by
    rw [genFun_eq h]
    exact ContinuousLinearMap.iteratedFDeriv_comp_right
      (L : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n)) hcd 0 le_rfl
  have h2 (y : EuclideanSpace ℝ (Fin n)) (j : Fin n) : ⟪y, L (Pi.single j 1)⟫ = y j := by
    rw [inner_eq_sum]
    have (i : Fin n) : L (Pi.single j 1) i = (Pi.single j (1 : ℝ) : Fin n → ℝ) i := rfl
    simp only [this]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      rw [Pi.single_eq_of_ne hi, zero_mul]
    · simp
  have hL0 : L 0 = 0 := map_zero L
  have h3 := iteratedFDeriv_charFun (μ := ν) (t := (0 : EuclideanSpace ℝ (Fin n))) hm
    (fun j => L (Pi.single j 1))
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, h2] at h3
  have h4 : iteratedFDeriv ℝ n (genFun S σ) 0 (fun j => Pi.single j 1) =
      iteratedFDeriv ℝ n (charFun ν) 0 (fun j => L (Pi.single j 1)) := by
    rw [h1, hL0]
    rfl
  have hI : (-Complex.I) ^ n * Complex.I ^ n = 1 := by
    rw [← mul_pow]
    simp
  unfold schwinger
  rw [h4, h3, ← mul_assoc, hI, one_mul]
  exact integral_complex_ofReal

/-! ### Convergence of the lattice correlation functions -/

variable {c : ℕ → Coeffs} {ω : ℕ → (Cfg ℤ → ℂ) → ℂ} {Nm : ℕ → ℕ}

theorem expBounded_fieldVec {cN : Coeffs} {ωN : (Cfg ℤ → ℂ) → ℂ} {μ : Measure (Cfg ℤ)}
    (h : Represents cN ωN μ) (sc : Scale) {N0 N : ℕ} (hN : N0 ≤ N) (gd : DensityFn) {n : ℕ}
    (σ : Fin n → T) : ExpBounded sc N0 gd σ (μ.map (fieldVec sc N gd σ)) :=
  ⟨by
    have := h.prob
    exact Measure.isProbabilityMeasure_map (measurable_fieldVec sc N gd σ).aemeasurable,
   fun v => exp_fieldVec h sc hN gd σ v⟩

theorem continuous_prod_coord {n m : ℕ} (q : Fin m → Fin n) :
    Continuous fun x : EuclideanSpace ℝ (Fin n) => ∏ i, x (q i) := by
  fun_prop

/-- The lattice moments of a family, along any map of indices: integrability. -/
theorem integrable_lattice_prod {cN : Coeffs} {ωN : (Cfg ℤ → ℂ) → ℂ} {μ : Measure (Cfg ℤ)}
    (h : Represents cN ωN μ) (sc : Scale) {N0 N : ℕ} (hN : N0 ≤ N) (gd : DensityFn) {n m : ℕ}
    (σ : Fin n → T) (q : Fin m → Fin n) :
    Integrable (fun x => ∏ i, Phi sc N gd (σ (q i)) x) μ := by
  have hb := (expBounded_fieldVec h sc hN gd σ).integrable_prod q
  exact (integrable_map_measure (continuous_prod_coord q).aestronglyMeasurable
    (measurable_fieldVec sc N gd σ).aemeasurable).mp hb

theorem lattice_sq_bound {cN : Coeffs} {ωN : (Cfg ℤ → ℂ) → ℂ} {μ : Measure (Cfg ℤ)}
    (h : Represents cN ωN μ) (sc : Scale) {N0 N : ℕ} (hN : N0 ≤ N) (gd : DensityFn) {n m : ℕ}
    (σ : Fin n → T) (q : Fin m → Fin n) :
    Integrable (fun x => (∏ i, Phi sc N gd (σ (q i)) x) ^ 2) μ ∧
      ∫ x, (∏ i, Phi sc N gd (σ (q i)) x) ^ 2 ∂μ ≤ 2 ^ n * expBound sc N0 gd σ fun _ => 2 * m := by
  obtain ⟨h1, h2⟩ := (expBounded_fieldVec h sc hN gd σ).sq_prod_bound q
  have hm := (measurable_fieldVec sc N gd σ).aemeasurable (μ := μ)
  have hc : Continuous fun x : EuclideanSpace ℝ (Fin n) => (∏ i, x (q i)) ^ 2 :=
    (continuous_prod_coord q).pow 2
  refine ⟨(integrable_map_measure hc.aestronglyMeasurable hm).mp h1, ?_⟩
  rw [integral_map hm hc.aestronglyMeasurable] at h2
  exact h2

/-- [GG-OS] Theorem 9.4 (iv), at the level of the limit points: the correlation functions of the
limit points converge to the moments of the limit law. -/
theorem tendsto_lattice_prod (hω : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N))
    (hS : IsLimitFunctional sc N0 gd ω Nm S) {μ : ℕ → Measure (Cfg ℤ)}
    (hμ : ∀ N, N0 ≤ N → Represents (c N) (ω N) (μ N)) {n m : ℕ} (σ : Fin n → T)
    (q : Fin m → Fin n) :
    ∃ ν : Measure (EuclideanSpace ℝ (Fin n)), IsLaw sc N0 gd S σ ν ∧
      Tendsto (fun l => ∫ x, ∏ i, Phi sc (Nm l) gd (σ (q i)) x ∂(μ (Nm l))) atTop
        (𝓝 (∫ x, ∏ i, x (q i) ∂ν)) := by
  obtain ⟨ν, hν, hconv⟩ := exists_law hω hS hμ σ
  refine ⟨ν, hν, ?_⟩
  have hp (l : ℕ) : IsProbabilityMeasure (μ (Nm l)) := (hμ _ (hS.le l)).prob
  exact tendsto_integral_of_sq (fun l => μ (Nm l)) (fun l => fieldVec sc (Nm l) gd σ)
    (fun l => measurable_fieldVec sc (Nm l) gd σ) (ν : Measure (EuclideanSpace ℝ (Fin n))) hconv
    (continuous_prod_coord q)
    (fun l => lattice_sq_bound (hμ _ (hS.le l)) sc (hS.le l) gd σ q)
    (hν.expBounded.sq_prod_bound q)

/-- The correlation functions of the limit points converge to the Schwinger functions. -/
theorem tendsto_schwinger (hω : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N))
    (hS : IsLimitFunctional sc N0 gd ω Nm S) {μ : ℕ → Measure (Cfg ℤ)}
    (hμ : ∀ N, N0 ≤ N → Represents (c N) (ω N) (μ N)) {n : ℕ} (σ : Fin n → T) :
    Tendsto (fun l => ((∫ x, ∏ i, Phi sc (Nm l) gd (σ i) x ∂(μ (Nm l)) : ℝ) : ℂ)) atTop
      (𝓝 (schwinger S σ)) := by
  obtain ⟨ν, hν, hlim⟩ := tendsto_lattice_prod hω hS hμ σ id
  rw [schwinger_eq hν]
  exact (Complex.continuous_ofReal.tendsto _).comp hlim

end GGOS.OS

end

end

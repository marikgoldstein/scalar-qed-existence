module

public import GGOS.Frozen.LimitFunctional
public import GGOS.OS.Axioms
public import GGOS.OS.Work.Charge
public import GGOS.OS.Work.Entire
public import GGOS.OS.Work.Growth
public import GGOS.OS.Work.Invariance
public import GGOS.OS.Work.Polynomial
public import GGOS.OS.Work.Tempered
public import GGOS.OS.Work.TwoPoint

/-!
# The axioms for every limit functional
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace GGOS.OS

variable {sc : Scale} {N0 : ℕ} {gd : DensityFn} {S : Alg →ₗ[ℂ] ℂ}
  {c : ℕ → Coeffs} {ω : ℕ → (Cfg ℤ → ℂ) → ℂ} {Nm : ℕ → ℕ}

theorem os3 (hω : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N))
    (hS : IsLimitFunctional sc N0 gd ω Nm S) : OS3 S := by
  obtain ⟨h1, h2, h3, h4⟩ := os3_moments hω hS
  exact ⟨h1, h2, h3, h4, basis_charge hω hS, fun n hn σ hσ => schwinger_odd hω hS hn σ hσ⟩

theorem os0 (hω : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N))
    (hS : IsLimitFunctional sc N0 gd ω Nm S) :
    OS0 sc N0 gd (Real.exp 1 * normConst sc gd) S := by
  obtain ⟨μ, hμ⟩ := exists_representing hω
  have hgrowth (n : ℕ) (σ : Fin n → T) :
      ‖schwinger S σ‖ ≤ Real.exp n * Real.sqrt n.factorial * ∏ i, pairNorm sc N0 gd (σ i) := by
    obtain ⟨ν, hν, _⟩ := exists_law hω hS hμ σ
    exact schwinger_growth hν
  refine ⟨basis_zero hω hS, basis_lipschitz hω hS, fun k σ => ?_, hgrowth, fun n σ => ?_,
    fun σ hσ => ?_⟩
  · obtain ⟨ν, hν, _⟩ := exists_law hω hS hμ σ
    exact ⟨entireGen ν, differentiable_entireGen hν.expBounded, entireGen_imag hν,
      fun z => (norm_entireGen_le hν.expBounded z).1, fun z => (norm_entireGen_le hν.expBounded z).2⟩
  · have hprod : ∏ i, pairNorm sc N0 gd (σ i) ≤ normConst sc gd ^ n * ∏ i, weightNorm (σ i) := by
      calc ∏ i, pairNorm sc N0 gd (σ i) ≤ ∏ i, normConst sc gd * weightNorm (σ i) :=
            Finset.prod_le_prod (fun i _ => pairNorm_nonneg _)
              fun i _ => pairNorm_le_weightNorm sc N0 gd (σ i)
        _ = normConst sc gd ^ n * ∏ i, weightNorm (σ i) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc ‖schwinger S σ‖
        ≤ Real.exp n * Real.sqrt n.factorial * ∏ i, pairNorm sc N0 gd (σ i) := hgrowth n σ
      _ ≤ Real.exp n * Real.sqrt n.factorial * (normConst sc gd ^ n * ∏ i, weightNorm (σ i)) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = (Real.exp 1 * normConst sc gd) ^ n * Real.sqrt n.factorial * ∏ i, weightNorm (σ i) := by
          rw [mul_pow, ← Real.exp_nat_mul, mul_one]
          ring
  · obtain ⟨ν, hν, _⟩ := exists_law hω hS hμ ![σ, σ]
    exact two_point hσ hν

/-- The axioms for every limit functional of limit points of the torus states. -/
theorem osterwalder_schrader :
    ∀ (sc : Scale) (gd : DensityFn), ∃ C : ℝ,
      ∀ (N0 : ℕ) (c : ℕ → Coeffs) (ω : ℕ → (Cfg ℤ → ℂ) → ℂ)
        (_ : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N)),
      (∃ (Nm : ℕ → ℕ) (S : Alg →ₗ[ℂ] ℂ), IsLimitFunctional sc N0 gd ω Nm S) ∧
        ∀ (Nm : ℕ → ℕ) (S : Alg →ₗ[ℂ] ℂ), IsLimitFunctional sc N0 gd ω Nm S →
          OS0 sc N0 gd C S ∧ OS1Cubic S ∧ OS2 S ∧ OS3 S ∧
          ∀ (μ : ℕ → Measure (Cfg ℤ)),
            (∀ N, N0 ≤ N → IsProbabilityMeasure (μ N) ∧ ∀ F, IsBBL F → ω N F = ∫ x, F x ∂(μ N)) →
            ∀ (n : ℕ) (σ : Fin n → T),
              (∀ m, Integrable (fun x => ∏ i, Phi sc (Nm m) gd (σ i) x) (μ (Nm m))) ∧
              Tendsto (fun m => ((∫ x, ∏ i, Phi sc (Nm m) gd (σ i) x ∂(μ (Nm m)) : ℝ) : ℂ)) atTop
                (𝓝 (schwinger S σ)) := by
  intro sc gd
  refine ⟨Real.exp 1 * normConst sc gd, fun N0 c ω hω => ⟨?_, fun Nm S hS =>
    ⟨os0 hω hS, os1Cubic hω hS, os2 hω hS, os3 hω hS, fun μ hμ n σ => ?_⟩⟩⟩
  · obtain ⟨Nm, S, h1, h2, h3, -⟩ := GGOS.limit_functional sc N0 gd c ω hω
    exact ⟨Nm, S, h1, h2, h3⟩
  · have hr (N : ℕ) (hN : N0 ≤ N) : Represents (c N) (ω N) (μ N) :=
      represents (hω N hN) (hμ N hN).1 (hμ N hN).2
    exact ⟨fun m => integrable_lattice_prod (hr _ (hS.le m)) sc (hS.le m) gd σ id,
      tendsto_schwinger hω hS hr σ⟩

end GGOS.OS

end

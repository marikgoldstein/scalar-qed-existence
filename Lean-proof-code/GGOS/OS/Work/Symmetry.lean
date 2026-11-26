module

public import GGOS.OS.Axioms
public import GGOS.OS.Work.SchwingerLaw

/-!
# OS3 ([GG-OS] Proposition 9.12 (a))
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace GGOS.OS

variable {sc : Scale} {N0 : ℕ} {gd : DensityFn} {S : Alg →ₗ[ℂ] ℂ}
  {c : ℕ → Coeffs} {ω : ℕ → (Cfg ℤ → ℂ) → ℂ} {Nm : ℕ → ℕ}

open Classical in
theorem exists_representing (hω : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N)) :
    ∃ μ : ℕ → Measure (Cfg ℤ), ∀ N, N0 ≤ N → Represents (c N) (ω N) (μ N) := by
  choose μ hμ using fun (N : ℕ) (hN : N0 ≤ N) => exists_represents (hω N hN)
  refine ⟨fun N => if hN : N0 ≤ N then μ N hN else 0, fun N hN => ?_⟩
  simp only [hN, dite_true]
  exact hμ N hN

theorem prod_update (sc : Scale) (N : ℕ) (gd : DensityFn) {n : ℕ} (σ : Fin n → T) (i : Fin n)
    (τ : T) (x : Cfg ℤ) : ∏ j, Phi sc N gd (Function.update σ i τ j) x =
      Phi sc N gd τ x * ∏ j ∈ Finset.univ \ {i}, Phi sc N gd (σ j) x := by
  have h : (fun j => Phi sc N gd (Function.update σ i τ j) x) =
      Function.update (fun j => Phi sc N gd (σ j) x) i (Phi sc N gd τ x) := by
    funext j
    exact Function.apply_update (fun _ τ => Phi sc N gd τ x) σ i τ j
  rw [h, Finset.prod_update_of_mem (Finset.mem_univ i)]

/-- [GG-OS] Proposition 9.12 (a): symmetry, additivity, homogeneity, reality. -/
theorem os3_moments (hω : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N))
    (hS : IsLimitFunctional sc N0 gd ω Nm S) :
    (∀ (n : ℕ) (π : Equiv.Perm (Fin n)) (σ : Fin n → T),
      schwinger S (fun i => σ (π i)) = schwinger S σ) ∧
    (∀ (n : ℕ) (σ : Fin n → T) (i : Fin n) (τ τ' : T),
      schwinger S (Function.update σ i (τ + τ')) =
        schwinger S (Function.update σ i τ) + schwinger S (Function.update σ i τ')) ∧
    (∀ (n : ℕ) (σ : Fin n → T) (i : Fin n) (r : ℝ) (τ : T),
      schwinger S (Function.update σ i (r • τ)) = (r : ℂ) * schwinger S (Function.update σ i τ)) ∧
    ∀ (n : ℕ) (σ : Fin n → T), (schwinger S σ).im = 0 := by
  obtain ⟨μ, hμ⟩ := exists_representing hω
  have hint {n : ℕ} (σ : Fin n → T) (l : ℕ) :
      Integrable (fun x => ∏ i, Phi sc (Nm l) gd (σ i) x) (μ (Nm l)) :=
    integrable_lattice_prod (hμ _ (hS.le l)) sc (hS.le l) gd σ id
  refine ⟨fun n π σ => ?_, fun n σ i τ τ' => ?_, fun n σ i r τ => ?_, fun n σ => ?_⟩
  · refine tendsto_nhds_unique (tendsto_schwinger hω hS hμ _) ?_
    refine (tendsto_schwinger hω hS hμ σ).congr fun l => ?_
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact (Equiv.prod_comp π fun i => Phi sc (Nm l) gd (σ i) x).symm
  · refine tendsto_nhds_unique (tendsto_schwinger hω hS hμ _) ?_
    refine ((tendsto_schwinger hω hS hμ (Function.update σ i τ)).add
      (tendsto_schwinger hω hS hμ (Function.update σ i τ'))).congr fun l => ?_
    rw [← Complex.ofReal_add, ← integral_add (hint _ l) (hint _ l)]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [prod_update, phi_add, add_mul]
  · refine tendsto_nhds_unique (tendsto_schwinger hω hS hμ _) ?_
    refine ((tendsto_schwinger hω hS hμ (Function.update σ i τ)).const_mul (r : ℂ)).congr fun l => ?_
    rw [← Complex.ofReal_mul, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [prod_update, phi_smul, mul_assoc]
  · obtain ⟨ν, hν, _⟩ := tendsto_lattice_prod hω hS hμ σ id
    rw [schwinger_eq hν, Complex.ofReal_im]

end GGOS.OS

end

end

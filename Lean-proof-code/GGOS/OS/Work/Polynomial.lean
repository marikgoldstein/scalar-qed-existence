module

public import GGOS.OS.Work.FunctionalRP
public import GGOS.OS.Work.Symmetry

/-!
# OS2 for polynomials of the field ([GG-OS] Proposition 9.11)
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ComplexOrder ENNReal

namespace GGOS.OS

theorem exists_dependsUp_const (z : ℂ) : ∃ P X, DependsUp P X fun _ => z :=
  ⟨∅, ∅, by simp, by simp, fun _ _ _ _ => rfl⟩

theorem exists_dependsUp_prod {ι : Type*} (s : Finset ι) (f : ι → Cfg ℤ → ℂ)
    (h : ∀ i ∈ s, ∃ P X, DependsUp P X (f i)) : ∃ P X, DependsUp P X fun x => ∏ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact exists_dependsUp_const 1
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact exists_dependsUp_op (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj)) (· * ·)

theorem exists_dependsUp_sum {ι : Type*} (s : Finset ι) (f : ι → Cfg ℤ → ℂ)
    (h : ∀ i ∈ s, ∃ P X, DependsUp P X (f i)) : ∃ P X, DependsUp P X fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact exists_dependsUp_const 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact exists_dependsUp_op (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj)) (· + ·)

/-- The polynomial of the lattice fields. -/
def latPoly (sc : Scale) (N : ℕ) (gd : DensityFn) {m : ℕ} {d : Fin m → ℕ}
    (σ : (α : Fin m) → Fin (d α) → T) (w : Fin m → ℂ) (x : Cfg ℤ) : ℂ :=
  ∑ α, w α * ∏ i, ((Phi sc N gd (σ α i) x : ℝ) : ℂ)

theorem measurable_latPoly (sc : Scale) (N : ℕ) (gd : DensityFn) {m : ℕ} {d : Fin m → ℕ}
    (σ : (α : Fin m) → Fin (d α) → T) (w : Fin m → ℂ) : Measurable (latPoly sc N gd σ w) := by
  unfold latPoly
  refine Finset.measurable_sum _ fun α _ => Measurable.const_mul ?_ _
  exact Finset.measurable_prod _ fun i _ =>
    Complex.measurable_ofReal.comp (measurable_phi sc N gd (σ α i))

theorem memLp_latPoly {cN : Coeffs} {ωN : (Cfg ℤ → ℂ) → ℂ} {μ : Measure (Cfg ℤ)}
    (h : Represents cN ωN μ) (sc : Scale) {N0 N : ℕ} (hN : N0 ≤ N) (gd : DensityFn) {m : ℕ}
    {d : Fin m → ℕ} (σ : (α : Fin m) → Fin (d α) → T) (w : Fin m → ℂ) :
    MemLp (latPoly sc N gd σ w) 2 μ := by
  have := h.prob
  unfold latPoly
  refine memLp_finsetSum _ fun α _ => MemLp.const_mul ?_ _
  have hr : MemLp (fun x => ∏ i, Phi sc N gd (σ α i) x) 2 μ := by
    refine (memLp_two_iff_integrable_sq ?_).mpr
      (lattice_sq_bound h sc hN gd (σ α) id).1
    exact (Finset.measurable_prod _ fun i _ =>
      measurable_phi sc N gd (σ α i)).aestronglyMeasurable
  have hc := hr.ofReal (K := ℂ)
  refine hc.congr_norm ?_ (Eventually.of_forall fun x => ?_)
  · exact (Finset.measurable_prod _ fun i _ =>
      Complex.measurable_ofReal.comp (measurable_phi sc N gd (σ α i))).aestronglyMeasurable
  · rw [← Complex.ofReal_prod]
    rfl

theorem exists_dependsUp_latPoly (sc : Scale) (N : ℕ) (gd : DensityFn) {m : ℕ} {d : Fin m → ℕ}
    {σ : (α : Fin m) → Fin (d α) → T} (hσ : ∀ α i, SupportedAbove 2 0 (σ α i)) (w : Fin m → ℂ) :
    ∃ P X, DependsUp P X (latPoly sc N gd σ w) := by
  unfold latPoly
  refine exists_dependsUp_sum _ _ fun α _ => ?_
  refine exists_dependsUp_op (exists_dependsUp_const (w α)) (exists_dependsUp_prod _ _ fun i _ =>
    exists_dependsUp_phi sc N gd (hσ α i) fun r => (r : ℂ)) (· * ·)

theorem conj_latPoly (sc : Scale) (N : ℕ) (gd : DensityFn) {m : ℕ} {d : Fin m → ℕ}
    (σ : (α : Fin m) → Fin (d α) → T) (w : Fin m → ℂ) (x : Cfg ℤ) :
    starRingEnd ℂ (latPoly sc N gd σ w (pull (timeRefl ℤ) x)) * latPoly sc N gd σ w x =
      ∑ α, ∑ β, starRingEnd ℂ (w α) * w β * ((∏ k, Phi sc N gd
        (Fin.append (fun i => pushT (reflPlane 2 0) (σ α i)) (σ β) k) x : ℝ) : ℂ) := by
  unfold latPoly
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right, map_mul, map_prod, Complex.conj_ofReal, phi_refl]
  push_cast
  ring

variable {sc : Scale} {N0 : ℕ} {gd : DensityFn} {S : Alg →ₗ[ℂ] ℂ}
  {c : ℕ → Coeffs} {ω : ℕ → (Cfg ℤ → ℂ) → ℂ} {Nm : ℕ → ℕ}

theorem polynomial_refl (hω : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N))
    (hS : IsLimitFunctional sc N0 gd ω Nm S) (m : ℕ) (d : Fin m → ℕ)
    (σ : (α : Fin m) → Fin (d α) → T) (hσ : ∀ α i, SupportedAbove 2 0 (σ α i)) (w : Fin m → ℂ) :
    0 ≤ ∑ α, ∑ β, starRingEnd ℂ (w α) * w β *
      schwinger S (Fin.append (fun i => pushT (reflPlane 2 0) (σ α i)) (σ β)) := by
  obtain ⟨μ, hμ⟩ := exists_representing hω
  have hlim : Tendsto (fun l => ∑ α, ∑ β, starRingEnd ℂ (w α) * w β *
      ((∫ x, ∏ k, Phi sc (Nm l) gd
        (Fin.append (fun i => pushT (reflPlane 2 0) (σ α i)) (σ β) k) x ∂(μ (Nm l)) : ℝ) : ℂ))
      atTop (𝓝 (∑ α, ∑ β, starRingEnd ℂ (w α) * w β *
        schwinger S (Fin.append (fun i => pushT (reflPlane 2 0) (σ α i)) (σ β)))) :=
    tendsto_finsetSum _ fun α _ => tendsto_finsetSum _ fun β _ =>
      (tendsto_schwinger hω hS hμ _).const_mul _
  refine ge_of_tendsto' hlim fun l => ?_
  have hr := hμ _ (hS.le l)
  obtain ⟨P, X, hup⟩ := exists_dependsUp_latPoly sc (Nm l) gd hσ w
  have h := rp_state (hω _ (hS.le l)) hr (measurable_latPoly sc (Nm l) gd σ w)
    (memLp_latPoly hr sc (hS.le l) gd σ w) hup
  have hint (α β : Fin m) : Integrable (fun x => ((∏ k, Phi sc (Nm l) gd
      (Fin.append (fun i => pushT (reflPlane 2 0) (σ α i)) (σ β) k) x : ℝ) : ℂ)) (μ (Nm l)) :=
    (integrable_lattice_prod hr sc (hS.le l) gd _ id).ofReal
  simp only [conj_latPoly] at h
  rw [integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
    (hint α β).const_mul _] at h
  refine h.trans_eq (Finset.sum_congr rfl fun α _ => ?_)
  rw [integral_finsetSum _ fun β _ => (hint α β).const_mul _]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [integral_const_mul]
  congr 1
  exact integral_complex_ofReal

/-- [GG-OS] Proposition 9.11. -/
theorem polynomial_plane (hω : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N))
    (hS : IsLimitFunctional sc N0 gd ω Nm S) (j : Fin 3) (r : ℝ) (m : ℕ) (d : Fin m → ℕ)
    (σ : (α : Fin m) → Fin (d α) → T) (hσ : ∀ α i, SupportedAbove j r (σ α i)) (w : Fin m → ℂ) :
    0 ≤ ∑ α, ∑ β, starRingEnd ℂ (w α) * w β *
      schwinger S (Fin.append (fun i => pushT (reflPlane j r) (σ α i)) (σ β)) := by
  let τ (α : Fin m) (i : Fin (d α)) : T := pushT (fromPlane j r) (σ α i)
  have h := polynomial_refl hω hS m d τ (fun α i => supportedAbove_from (hσ α i)) w
  refine h.trans_eq (Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_)
  congr 1
  rw [← (os1Cubic hω hS).schwinger_invariant (toPlane j r)]
  congr 1
  funext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · simp only [Fin.append_left, τ]
    rw [← refl_to, to_from]
  · simp only [Fin.append_right, τ]
    rw [to_from]

/-- OS2 ([GG-OS] Propositions 9.9 and 9.11). -/
theorem os2 (hω : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N))
    (hS : IsLimitFunctional sc N0 gd ω Nm S) : OS2 S where
  conj := conj_plane hω hS
  hermitian := hermitian_plane hω hS
  nonneg j r _ ha := nonneg_plane hω hS j r ha
  polynomial := polynomial_plane hω hS

end GGOS.OS

end

end

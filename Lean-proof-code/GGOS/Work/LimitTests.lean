module

public import GGOS.Frozen.Defs.Admissible
public import GGOS.Frozen.Defs.Transl

/-! Fixed-support smooth approximation and continuity of translated tests. -/

public section

open Filter Topology Set Function
open scoped ContDiff Pointwise

namespace GGOS.Work.Limit

private abbrev Component := Option (Fin 3 × Fin 3)

private def component (σ : T) : Component → E3 → ℝ
  | none => σ.1.2
  | some (i, j) => σ.1.1 i j

private theorem smooth_component (σ : T) (i : Component) : ContDiff ℝ smoothTop (component σ i) := by
  cases i with
  | none => exact σ.isTestPair.smooth_h
  | some q => exact σ.isTestPair.smooth_f _ _

private theorem compact_component (σ : T) (i : Component) : HasCompactSupport (component σ i) := by
  cases i with
  | none => exact σ.isTestPair.compact_h
  | some q => exact σ.isTestPair.compact_f _ _

private theorem component_supports (σ : T) :
    ∃ K : Set E3, IsCompact K ∧ ∀ i, tsupport (component σ i) ⊆ K :=
  ⟨_, isCompact_iUnion (compact_component σ), fun i => subset_iUnion (fun j => tsupport (component σ j)) i⟩

private theorem convTest_of_components {u : ℕ → T} {σ : T} {K : Set E3} (hK : IsCompact K)
    (hs : ∀ n i, tsupport (component (u n) i) ⊆ K)
    (hd : ∀ k i, TendstoUniformly (fun n => iteratedFDeriv ℝ k (component (u n) i))
      (iteratedFDeriv ℝ k (component σ i)) atTop) : ConvTest u σ :=
  ⟨⟨K, hK, fun n => ⟨fun i j => hs n (some (i, j)), hs n none⟩⟩,
   fun k => ⟨fun i j => hd k (some (i, j)), hd k none⟩⟩

private abbrev Deriv (k : ℕ) := E3 [×k]→L[ℝ] ℝ

private theorem continuous_deriv (σ : T) (k : ℕ) (i : Component) :
    Continuous (iteratedFDeriv ℝ k (component σ i)) :=
  (smooth_component σ i).continuous_iteratedFDeriv (by simp [smoothTop])

private noncomputable def jets (σ : T) (k : ℕ) (i : Component) : C(E3, Deriv k) :=
  ⟨_, continuous_deriv σ k i⟩

private theorem uniform_deriv_of_fixed_support {u : ℕ → T} {σ : T} {K : Set E3}
    (hK : IsCompact K) (hs : ∀ n i, tsupport (component (u n) i) ⊆ K)
    (hσ : ∀ i, tsupport (component σ i) ⊆ K) (k : ℕ) (i : Component)
    (hj : Tendsto (fun n => jets (u n) k i) atTop (𝓝 (jets σ k i))) :
    TendstoUniformly (fun n => iteratedFDeriv ℝ k (component (u n) i))
      (iteratedFDeriv ℝ k (component σ i)) atTop := by
  have h := ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hj K hK
  refine Metric.tendstoUniformly_iff.mpr fun ε hε => ?_
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h ε hε] with n hn x
  by_cases hx : x ∈ K
  · exact hn x hx
  · have hzero (s : T) (hh : tsupport (component s i) ⊆ K) :
        iteratedFDeriv ℝ k (component s i) x = 0 := by
      by_contra hne
      exact hx (hh (support_iteratedFDeriv_subset (𝕜 := ℝ) k hne))
    simpa only [hzero σ (hσ i), hzero (u n) (hs n i), dist_self] using hε

private theorem dense_fixed_support (K : Set E3) (hK : IsCompact K) :
    ∃ d : Set T, d.Countable ∧ ∀ σ : T, (∀ i, tsupport (component σ i) ⊆ K) →
      ∃ u : ℕ → T, (∀ n, u n ∈ d) ∧ ConvTest u σ := by
  let A := {σ : T // ∀ i, tsupport (component σ i) ⊆ K}
  let J (s : A) := jets s.val
  let (k : ℕ) : FiniteDimensional ℝ (Deriv k) :=
    FiniteDimensional.of_injective ContinuousMultilinearMap.toMultilinearMapLinear
      ContinuousMultilinearMap.toMultilinearMap_injective
  let : TopologicalSpace A := TopologicalSpace.induced J inferInstance
  have hind : IsInducing J := ⟨rfl⟩
  let : SecondCountableTopology A := hind.secondCountableTopology
  obtain ⟨s, hs, hds⟩ := TopologicalSpace.exists_countable_dense A
  refine ⟨Subtype.val '' s, hs.image _, fun σ hσ => ?_⟩
  let a : A := ⟨σ, hσ⟩
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp (hds a)
  have hJ : Tendsto (J ∘ u) atTop (𝓝 (J a)) := (hind.continuous.tendsto a).comp hlim
  refine ⟨fun n => (u n).val, fun n => mem_image_of_mem _ (hu n),
    convTest_of_components hK (fun n => (u n).property) (fun k i => ?_)⟩
  exact uniform_deriv_of_fixed_support hK (fun n => (u n).property) hσ k i
    (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hJ k) i)

/-- A single countable set approximates every test in the smooth convergence relation `ConvTest`. -/
theorem exists_countable_convTest :
    ∃ D : Set T, D.Countable ∧ ∀ σ : T, ∃ u : ℕ → T, (∀ n, u n ∈ D) ∧ ConvTest u σ := by
  let K := CompactExhaustion.choice E3
  choose d hd happrox using fun n => dense_fixed_support (K n) (K.isCompact n)
  refine ⟨⋃ n, d n, countable_iUnion hd, fun σ => ?_⟩
  obtain ⟨L, hL, hs⟩ := component_supports σ
  obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hL
  obtain ⟨u, hu, hconv⟩ := happrox n σ (fun i => (hs i).trans hn)
  exact ⟨u, fun m => mem_iUnion.mpr ⟨n, hu m⟩, hconv⟩

private theorem component_transl (v : E3) (σ : T) (i : Component) :
    component (transl v σ) i = fun x => component σ i (x - v) := by
  cases i <;> rfl

/-- The supports of converging shifts stay in one compact set, and each derivative
converges uniformly on all of space. -/
theorem convTest_transl {u : ℕ → E3} {v : E3} (hu : Tendsto u atTop (𝓝 v)) (σ : T) :
    ConvTest (fun n => transl (u n) σ) (transl v σ) := by
  obtain ⟨K, hK, hs⟩ := component_supports σ
  refine convTest_of_components (hK.add hu.isCompact_insert_range) ?_ ?_
  · intro n i x hx
    rw [component_transl] at hx
    have hx' : x - u n ∈ tsupport (component σ i) :=
      tsupport_comp_subset_preimage (f := fun y : E3 => y - u n) (component σ i)
        (continuous_id.sub continuous_const) hx
    exact ⟨x - u n, hs i hx', u n, mem_insert_of_mem _ (mem_range_self n), sub_add_cancel _ _⟩
  · intro k i
    simp only [component_transl, iteratedFDeriv_comp_sub']
    have huc := ((compact_component σ i).iteratedFDeriv (𝕜 := ℝ) k).uniformContinuous_of_continuous
      (continuous_deriv σ k i)
    refine Metric.tendstoUniformly_iff.mpr fun ε hε => ?_
    obtain ⟨δ, hδ, hb⟩ := Metric.uniformContinuous_iff.mp huc ε hε
    filter_upwards [(Metric.tendsto_nhds.mp hu) δ hδ] with n hn x
    apply hb
    simpa only [dist_eq_norm, sub_sub_sub_cancel_left] using hn

end GGOS.Work.Limit

module

public import GGOS.Frozen.Defs.PairNorm
public import GGOS.Work.PairNormLattice

/-!
# Finiteness and uniform compact-support estimates for the two level sums
-/

public section

noncomputable section

namespace GGOS.Work.PairNorm

abbrev plaqSample (ε : ℝ) (σ : T) (p : Plaq ℤ) : ℝ :=
  σ.1.1 p.2.1.1 p.2.1.2 (plaqCentre ε p)

abbrev siteSample (ε : ℝ) (σ : T) (z : Site ℤ) : ℝ := σ.1.2 (sitePos ε z)

abbrev rLevel (sc : Scale) (N : ℕ) (σ : T) : ℝ :=
  Real.sqrt (eps sc N ^ 3 * ∑' p, plaqSample (eps sc N) σ p ^ 2)

abbrev eLevel (sc : Scale) (N : ℕ) (σ : T) : ℝ :=
  eps sc N ^ 3 * ∑' z, |siteSample (eps sc N) σ z|

abbrev SupportedIn (σ : T) (K : Set E3) : Prop :=
  (∀ μ ν, tsupport (σ.1.1 μ ν) ⊆ K) ∧ tsupport σ.1.2 ⊆ K

abbrev BoundedBy (σ : T) (M : ℝ) : Prop :=
  (∀ μ ν x, |σ.1.1 μ ν x| ≤ M) ∧ ∀ x, |σ.1.2 x| ≤ M

theorem exists_compact_support (σ : T) : ∃ K, IsCompact K ∧ SupportedIn σ K := by
  let F := ⋃ μ, ⋃ ν, tsupport (σ.1.1 μ ν)
  have hc : IsCompact F :=
    isCompact_iUnion fun μ => isCompact_iUnion fun ν => σ.isTestPair.compact_f μ ν
  refine ⟨F ∪ tsupport σ.1.2, hc.union σ.isTestPair.compact_h, ?_, Set.subset_union_right⟩
  intro μ ν x hx
  exact Or.inl (Set.mem_iUnion.mpr ⟨μ, Set.mem_iUnion.mpr ⟨ν, hx⟩⟩)

private theorem exists_component_bound (σ : T) : ∃ M, 0 ≤ M ∧ BoundedBy σ M := by
  choose C hC using fun μ ν =>
    (σ.isTestPair.smooth_f μ ν).continuous.bounded_above_of_compact_support
      (σ.isTestPair.compact_f μ ν)
  obtain ⟨F, hF⟩ := Finite.bddAbove_range fun q : Fin 3 × Fin 3 => C q.1 q.2
  obtain ⟨H, hH⟩ := σ.isTestPair.smooth_h.continuous.bounded_above_of_compact_support
    σ.isTestPair.compact_h
  refine ⟨max F H, (norm_nonneg _).trans ((hH 0).trans (le_max_right F H)), ?_, ?_⟩
  · intro μ ν x
    exact (hC μ ν x).trans ((hF ⟨(μ, ν), rfl⟩).trans (le_max_left F H))
  · exact fun x => (hH x).trans (le_max_right F H)

private theorem sample_support_subset {ε : ℝ} {S : Finset (Site ℤ)} {P : Finset (Plaq ℤ)}
    {σ : T} {K : Set E3} (hσ : SupportedIn σ K)
    (hS : ∀ z, sitePos ε z ∈ K → z ∈ S) (hP : ∀ p, plaqCentre ε p ∈ K → p ∈ P) :
    Function.support (siteSample ε σ) ⊆ ↑S ∧ Function.support (plaqSample ε σ) ⊆ ↑P :=
  ⟨fun z hz => hS z (hσ.2 (subset_tsupport _ hz)),
   fun p hp => hP p (hσ.1 _ _ (subset_tsupport _ hp))⟩

theorem finite_sample_supports (sc : Scale) (N : ℕ) (σ : T) :
    (Function.support (siteSample (eps sc N) σ)).Finite ∧
    (Function.support (plaqSample (eps sc N) σ)).Finite := by
  obtain ⟨K, hK, hσ⟩ := exists_compact_support σ
  obtain ⟨_, _, hbox⟩ := exists_sample_boxes sc hK
  obtain ⟨S, P, hS, hP, _⟩ := hbox N
  obtain ⟨hs, hp⟩ := sample_support_subset hσ hS hP
  exact ⟨S.finite_toSet.subset hs, P.finite_toSet.subset hp⟩

private theorem weighted_tsum_le {ι : Type*} {f : ι → ℝ} {S : Finset ι} {w V A : ℝ}
    (hw : 0 ≤ w) (hc : w * (S.card : ℝ) ≤ V) (hz : ∀ i ∉ S, f i = 0)
    (hf : ∀ i, f i ≤ A) (hA : 0 ≤ A) : w * ∑' i, f i ≤ V * A := by
  have hsum : HasSum f (∑ i ∈ S, f i) := hasSum_sum_of_ne_finset_zero hz
  rw [hsum.tsum_eq]
  calc
    w * ∑ i ∈ S, f i ≤ w * ∑ _i ∈ S, A :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hf i) hw
    _ = (w * (S.card : ℝ)) * A := by rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
    _ ≤ V * A := mul_le_mul_of_nonneg_right hc hA

/-- On a fixed compact support, both level sums are bounded by a fixed multiple of
a pointwise bound for the components. -/
theorem exists_level_bounds (sc : Scale) {K : Set E3} (hK : IsCompact K) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ (σ : T) (M : ℝ), SupportedIn σ K → 0 ≤ M → BoundedBy σ M →
      ∀ N, rLevel sc N σ ≤ Real.sqrt (3 * V) * M ∧ eLevel sc N σ ≤ V * M := by
  obtain ⟨V, hV, hbox⟩ := exists_sample_boxes sc hK
  refine ⟨V, hV, fun σ M hσ hM hbound N => ?_⟩
  obtain ⟨S, P, hS, hP, hcS, hcP⟩ := hbox N
  obtain ⟨hs, hp⟩ := sample_support_subset hσ hS hP
  have hw := pow_nonneg (eps_pos sc N).le 3
  constructor
  · have hz (p) (h : p ∉ P) : plaqSample (eps sc N) σ p ^ 2 = 0 := by
      rw [Function.notMem_support.mp (fun hmem => h (hp hmem)), zero_pow (by decide : 2 ≠ 0)]
    have hf (p : Plaq ℤ) : plaqSample (eps sc N) σ p ^ 2 ≤ M ^ 2 := by
      have h := abs_le.mp (hbound.1 p.2.1.1 p.2.1.2 (plaqCentre (eps sc N) p))
      exact sq_le_sq' h.1 h.2
    calc
      rLevel sc N σ ≤ Real.sqrt ((3 * V) * M ^ 2) :=
        Real.sqrt_le_sqrt (weighted_tsum_le hw hcP hz hf (sq_nonneg M))
      _ = Real.sqrt (3 * V) * M := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hM]
  · have hz (z) (h : z ∉ S) : |siteSample (eps sc N) σ z| = 0 := by
      rw [Function.notMem_support.mp (fun hmem => h (hs hmem)), abs_zero]
    exact weighted_tsum_le hw hcS hz (fun z => hbound.2 (sitePos (eps sc N) z)) hM

theorem level_ranges_bddAbove (sc : Scale) (N0 : ℕ) (σ : T) :
    BddAbove (Set.range fun N : {N : ℕ // N0 ≤ N} => rLevel sc N σ) ∧
    BddAbove (Set.range fun N : {N : ℕ // N0 ≤ N} => eLevel sc N σ) := by
  obtain ⟨K, hK, hσ⟩ := exists_compact_support σ
  obtain ⟨M, hM, hbound⟩ := exists_component_bound σ
  obtain ⟨V, _, hlevels⟩ := exists_level_bounds sc hK
  have h := hlevels σ M hσ hM hbound
  exact ⟨⟨Real.sqrt (3 * V) * M, Set.forall_mem_range.mpr fun N => (h N).1⟩,
    ⟨V * M, Set.forall_mem_range.mpr fun N => (h N).2⟩⟩

end GGOS.Work.PairNorm

end

end

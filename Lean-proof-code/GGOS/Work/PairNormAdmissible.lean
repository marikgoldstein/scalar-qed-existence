module

public import GGOS.Frozen.Defs.Admissible
public import GGOS.Work.PairNormSeminorm

/-!
# Continuity for convergent sequences of test pairs
-/

public section

open Filter Topology

namespace GGOS.Work.PairNorm

private theorem eventually_abs_sub_le {u : ℕ → E3 → ℝ} {f : E3 → ℝ}
    (h : TendstoUniformly (fun n => iteratedFDeriv ℝ 0 (u n)) (iteratedFDeriv ℝ 0 f) atTop)
    {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ n in atTop, ∀ x, |u n x - f x| ≤ δ := by
  filter_upwards [Metric.tendstoUniformly_iff.mp h δ hδ] with n hn x
  have hx := (hn x).le
  rw [dist_comm] at hx
  simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, LinearIsometryEquiv.dist_map,
    Real.dist_eq] using hx

/-- Uniform convergence at derivative order zero controls every sampled difference on the
union of the sequence's common compact support and the limit's compact support. -/
theorem admissible_pairNorm (sc : Scale) (N0 : ℕ) (gd : DensityFn) :
    Admissible (pairNorm sc N0 gd) := by
  rintro σs σ ⟨⟨K, hK, hseq⟩, hderiv⟩
  obtain ⟨L, hL, hlim⟩ := exists_compact_support σ
  have hs (n) : SupportedIn (σs n - σ) (K ∪ L) :=
    ⟨fun μ ν => (tsupport_sub ((σs n).1.1 μ ν) (σ.1.1 μ ν)).trans
      (Set.union_subset_union ((hseq n).1 μ ν) (hlim.1 μ ν)),
     (tsupport_sub (σs n).1.2 σ.1.2).trans (Set.union_subset_union (hseq n).2 hlim.2)⟩
  obtain ⟨V, _, hbound⟩ := exists_level_bounds sc (hK.union hL)
  obtain ⟨hf, hh⟩ := hderiv 0
  have : Nonempty {N : ℕ // N0 ≤ N} := ⟨⟨N0, le_rfl⟩⟩
  apply Metric.tendsto_nhds.mpr
  intro η hη
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_mul_lt hη (Real.sqrt (3 * V) + supNorm gd * V)
  have hf' : ∀ᶠ n in atTop, ∀ μ ν x, |(σs n).1.1 μ ν x - σ.1.1 μ ν x| ≤ δ :=
    eventually_all.mpr fun μ => eventually_all.mpr fun ν => eventually_abs_sub_le (hf μ ν) hδ
  filter_upwards [hf', eventually_abs_sub_le hh hδ] with n hn hn'
  have h := hbound (σs n - σ) δ (hs n) hδ.le ⟨hn, hn'⟩
  have hR : Rnorm sc N0 (σs n - σ) ≤ Real.sqrt (3 * V) * δ :=
    ciSup_le fun N : {N : ℕ // N0 ≤ N} => (h N).1
  have hE : Enorm sc N0 (σs n - σ) ≤ V * δ :=
    ciSup_le fun N : {N : ℕ // N0 ≤ N} => (h N).2
  rw [Real.dist_0_eq_abs, abs_of_nonneg ((isSeminorm_pairNorm sc N0 gd).nonneg _)]
  calc
    pairNorm sc N0 gd (σs n - σ) ≤ Real.sqrt (3 * V) * δ + supNorm gd * (V * δ) :=
      add_le_add hR (mul_le_mul_of_nonneg_left hE (supNorm_nonneg gd))
    _ = (Real.sqrt (3 * V) + supNorm gd * V) * δ := by rw [add_mul, mul_assoc]
    _ < η := hsmall

end GGOS.Work.PairNorm

end

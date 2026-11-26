module

public import GGOS.Work.LimitTests

/-! Simultaneous subsequence extraction for the characteristic functionals. -/

public section

open Filter Topology Set

namespace GGOS.Work.Limit

/-- Compactness on countably many disk coordinates and the three-term Cauchy estimate. -/
theorem exists_basis_limit (F : ℕ → T → ℂ) (N₀ : ℕ) {p : T → ℝ} (hp : Admissible p)
    (hb : ∀ N, N₀ ≤ N → ∀ σ, ‖F N σ‖ ≤ 1)
    (hmod : ∀ N, N₀ ≤ N → ∀ σ τ, ‖F N σ - F N τ‖ ≤ p (σ - τ)) :
    ∃ (Nm : ℕ → ℕ) (Z : T → ℂ), StrictMono Nm ∧ (∀ m, N₀ ≤ Nm m) ∧
      ∀ σ, Tendsto (fun m => F (Nm m) σ) atTop (𝓝 (Z σ)) := by
  obtain ⟨D, hD, happrox⟩ := exists_countable_convTest
  let Disc := Metric.closedBall (0 : ℂ) 1
  let : Countable D := hD.to_subtype
  let : CompactSpace Disc := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let U (n : ℕ) (s : D) : Disc :=
    ⟨F (N₀+n) s, by
      simpa only [Disc, Metric.mem_closedBall, dist_zero_right] using hb (N₀+n) (Nat.le_add_right _ _) s.val⟩
  obtain ⟨w, φ, hφ, hw⟩ := CompactSpace.tendsto_subseq U
  let Nm m := N₀ + φ m
  have hNm m : N₀ ≤ Nm m := Nat.le_add_right _ _
  have hDlim (s : D) : Tendsto (fun m => F (Nm m) s) atTop (𝓝 (w s).val) :=
    (continuous_subtype_val.tendsto _).comp (tendsto_pi_nhds.mp hw s)
  have hlim (σ : T) : ∃ z, Tendsto (fun m => F (Nm m) σ) atTop (𝓝 z) := by
    apply cauchySeq_tendsto_of_complete
    refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
    obtain ⟨u, hu, hconv⟩ := happrox σ
    have hthird : 0 < ε / 3 := by positivity
    obtain ⟨j, hj⟩ := ((hp u σ hconv).eventually_lt_const hthird).exists
    let s : D := ⟨u j, hu j⟩
    obtain ⟨M, hM⟩ := Metric.cauchySeq_iff.mp (hDlim s).cauchySeq (ε / 3) hthird
    refine ⟨M, fun m hm n hn => ?_⟩
    have hnear (l : ℕ) : dist (F (Nm l) s) (F (Nm l) σ) < ε / 3 :=
      by simpa only [dist_eq_norm] using (hmod (Nm l) (hNm l) s σ).trans_lt hj
    refine (dist_triangle4 (F (Nm m) σ) (F (Nm m) s) (F (Nm n) s) (F (Nm n) σ)).trans_lt ?_
    rw [dist_comm (F (Nm m) σ)]
    linarith only [hnear m, hM m hm n hn, hnear n]
  choose Z hZ using hlim
  exact ⟨Nm, Z, fun _ _ hij => Nat.add_lt_add_left (hφ hij) N₀, hNm, hZ⟩

end GGOS.Work.Limit

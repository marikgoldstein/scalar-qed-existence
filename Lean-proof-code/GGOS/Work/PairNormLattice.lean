module

public import GGOS.Frozen.Defs.Eps
public import GGOS.Frozen.Defs.PlaqCentre
public import GGOS.Frozen.Defs.SitePos

/-!
# Counting the lattice samples on a compact set
-/

public section

namespace GGOS.Work.PairNorm

theorem eps_pos (sc : Scale) (N : ℕ) : 0 < eps sc N :=
  div_pos sc.a0_pos (by positivity)

private theorem eps_le_a0 (sc : Scale) (N : ℕ) : eps sc N ≤ sc.a0 :=
  div_le_self sc.a0_pos.le (one_le_pow₀ (by norm_num))

/-- The extra lattice unit covers the offset from a plaquette corner to its centre. -/
private noncomputable def siteBox (ε R : ℝ) : Finset (Site ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-⌊R / ε + 1⌋) ⌊R / ε + 1⌋

private theorem mem_siteBox {ε R : ℝ} (hε : 0 < ε) (z : Site ℤ) (d : E3)
    (hd : ∀ i, |d i| ≤ 1) (hx : ‖fun i => ε * ((z i : ℝ) + d i)‖ ≤ R) :
    z ∈ siteBox ε R := by
  apply Fintype.mem_piFinset.mpr
  intro i
  have hi := (norm_le_pi_norm (fun j => ε * ((z j : ℝ) + d j)) i).trans hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hε] at hi
  have hcoord := abs_le.mp ((le_div_iff₀ hε).mpr ((mul_comm _ _).le.trans hi))
  have hoff := abs_le.mp (hd i)
  have upper : z i ≤ ⌊R / ε + 1⌋ := Int.le_floor.mpr (by linarith only [hcoord.2, hoff.1])
  have lower : -z i ≤ ⌊R / ε + 1⌋ := Int.le_floor.mpr (by
    rw [Int.cast_neg]
    linarith only [hcoord.1, hoff.2])
  exact Finset.mem_Icc.mpr ⟨by omega, upper⟩

private theorem siteBox_card_bound {ε R a : ℝ} (hε : 0 < ε) (ha : ε ≤ a) (hR : 0 ≤ R) :
    ε ^ 3 * ((siteBox ε R).card : ℝ) ≤ (2 * R + 3 * a) ^ 3 := by
  let m := ⌊R / ε + 1⌋
  have hm : 0 ≤ m := Int.floor_nonneg.mpr (by positivity)
  have hcard : ((Finset.Icc (-m) m).card : ℝ) = (m : ℝ) + 1 - (-m : ℝ) := by
    exact_mod_cast Int.card_Icc_of_le (a := -m) (b := m) (by omega)
  have hfloor : (m : ℝ) ≤ R / ε + 1 := Int.floor_le _
  have hside : ε * ((m : ℝ) + 1 - (-m : ℝ)) ≤ 2 * R + 3 * a := by
    have hmε := mul_le_mul_of_nonneg_right (sub_le_iff_le_add.mpr hfloor) hε.le
    rw [div_mul_cancel₀ _ hε.ne'] at hmε
    linarith only [hmε, ha]
  rw [siteBox, Fintype.card_piFinset_const, Nat.cast_pow, ← mul_pow]
  change (ε * ((Finset.Icc (-m) m).card : ℝ)) ^ 3 ≤ _
  apply pow_le_pow_left₀ (by positivity)
  rwa [hcard]

/-- A single compact set has site and plaquette sampling boxes whose weighted cardinalities
are bounded at every level. The three plaquette orientations share the same box of corners. -/
theorem exists_sample_boxes (sc : Scale) {K : Set E3} (hK : IsCompact K) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ N : ℕ, ∃ S : Finset (Site ℤ), ∃ P : Finset (Plaq ℤ),
      (∀ z, sitePos (eps sc N) z ∈ K → z ∈ S) ∧
      (∀ p, plaqCentre (eps sc N) p ∈ K → p ∈ P) ∧
      eps sc N ^ 3 * (S.card : ℝ) ≤ V ∧ eps sc N ^ 3 * (P.card : ℝ) ≤ 3 * V := by
  obtain ⟨R, hR, hsub⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : E3)
  have hnorm {x : E3} (hx : x ∈ K) : ‖x‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hsub hx
  have ha := sc.a0_pos
  refine ⟨(2 * R + 3 * sc.a0) ^ 3, by positivity, fun N => ?_⟩
  let ε := eps sc N
  let S := siteBox ε R
  have hε := eps_pos sc N
  have hc := siteBox_card_bound hε (eps_le_a0 sc N) hR.le
  refine ⟨S, S ×ˢ Finset.univ, ?_, ?_, hc, ?_⟩
  · intro z hz
    apply mem_siteBox hε z (fun _ => 0) (by simp)
    simp only [add_zero]
    exact hnorm hz
  · intro p hp
    apply Finset.mem_product.mpr
    refine ⟨mem_siteBox hε p.1
      (fun i => if i = p.2.1.1 ∨ i = p.2.1.2 then 1 / 2 else 0) ?_ (hnorm hp),
      Finset.mem_univ _⟩
    intro i
    split <;> norm_num
  · have hdir : Fintype.card Dir2 = 3 := by decide
    rw [Finset.card_product, Finset.card_univ, hdir, Nat.cast_mul, Nat.cast_ofNat, ← mul_assoc,
      mul_comm (_ * _) 3]
    exact mul_le_mul_of_nonneg_left hc (by norm_num)

end GGOS.Work.PairNorm

end

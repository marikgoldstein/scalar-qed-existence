module

public import GGOS.Frozen.Defs.LatticeInvariant
public import GGOS.Frozen.Defs.Transl
public import GGOS.Work.LimitObservables

/-! Translation of a sampled phase and approximation by the level meshes. -/

public section

open Filter Topology

namespace GGOS.Work.Limit

private def shift (j : Site ℤ) : LatSym ℤ := ⟨Equiv.refl _, fun _ => 1, j⟩

private theorem shift_act (j y : Site ℤ) : (shift j).act y = y + j := by
  funext i
  simp [LatSym.act, shift]

private theorem pull_face (j : Site ℤ) (x : Cfg ℤ) (q : Plaq ℤ) :
    (pull (shift j) x).1 q = x.1 (q.1 + j, q.2) := by
  rcases q with ⟨y, ⟨⟨i, l⟩, hil⟩⟩
  simp only [pull, shift_act]
  simp [shift, LatSym.corner, evalAnti, hil]

private theorem pull_site (j : Site ℤ) (x : Cfg ℤ) (y : Site ℤ) :
    (pull (shift j) x).2 y = x.2 (y + j) := by
  simp only [pull, shift_act]

private theorem centre_shift (ε : ℝ) (j : Site ℤ) (q : Plaq ℤ) :
    plaqCentre ε (q.1 + j, q.2) - sitePos ε j = plaqCentre ε q := by
  funext i
  simp only [Pi.sub_apply, plaqCentre, sitePos, Pi.add_apply, Int.cast_add]
  ring

private theorem site_shift (ε : ℝ) (j z : Site ℤ) :
    sitePos ε (z + j) - sitePos ε j = sitePos ε z := by
  funext i
  simp only [Pi.sub_apply, sitePos, Pi.add_apply, Int.cast_add]
  ring

/-- Reindex both sums in the phase by the same lattice shift. -/
private theorem phase_shift (sc : Scale) (N : ℕ) (gd : DensityFn) (σ : T)
    (j : Site ℤ) (x : Cfg ℤ) :
    Phi sc N gd (transl (sitePos (eps sc N) j) σ) x = Phi sc N gd σ (pull (shift j) x) := by
  let ε := eps sc N
  let e : Equiv.Perm (Plaq ℤ) := (Equiv.addRight j).prodCongr (Equiv.refl Dir2)
  let A (q : Plaq ℤ) := σ.1.1 q.2.1.1 q.2.1.2 (plaqCentre ε q - sitePos ε j) * x.1 q
  let B (z : Site ℤ) := σ.1.2 (sitePos ε z - sitePos ε j) * gd.toFun (x.2 z)
  change ε ^ (3/2 : ℝ) * (∑' q, A q) + ε ^ 3 * (∑' z, B z) = _
  unfold Phi
  rw [← e.tsum_eq A, ← (Equiv.addRight j).tsum_eq B]
  congr 1
  · congr 1
    apply tsum_congr
    intro q
    change σ.1.1 q.2.1.1 q.2.1.2 (plaqCentre ε (q.1+j, q.2) - sitePos ε j) * x.1 (q.1+j, q.2) = _
    rw [centre_shift, pull_face]
  · congr 1
    apply tsum_congr
    intro z
    change σ.1.2 (sitePos ε (z+j) - sitePos ε j) * gd.toFun (x.2 (z+j)) = _
    rw [site_shift, pull_site]

theorem state_exp_mesh_eq (sc : Scale) (N : ℕ) (gd : DensityFn) {ω : (Cfg ℤ → ℂ) → ℂ}
    (hi : LatticeInvariant ω) (σ : T) (j : Site ℤ) :
    ω (expPhi sc N gd (transl (sitePos (eps sc N) j) σ)) = ω (expPhi sc N gd σ) := by
  have he : expPhi sc N gd (transl (sitePos (eps sc N) j) σ) =
      expPhi sc N gd σ ∘ pull (shift j) := by
    funext x
    simp only [expPhi, Function.comp_apply, phase_shift]
  rw [he, hi _ _ (bbl_exp sc N gd σ)]

/-- Coordinatewise flooring approximates a displacement along the full sequence of meshes. -/
theorem exists_mesh_approx (sc : Scale) (v : E3) :
    ∃ j : ℕ → Site ℤ, Tendsto (fun N => sitePos (eps sc N) (j N)) atTop (𝓝 v) := by
  let j (N : ℕ) (i : Fin 3) := ⌊v i / eps sc N⌋
  refine ⟨j, tendsto_pi_nhds.mpr (fun i => ?_)⟩
  have hε : Tendsto (eps sc) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 5))
  have hlo (N : ℕ) : sitePos (eps sc N) (j N) i ≤ v i := by
    rw [sitePos, mul_comm]
    exact (le_div_iff₀ (spacing_pos sc N)).mp (Int.floor_le _)
  have hhi (N : ℕ) : v i - eps sc N ≤ sitePos (eps sc N) (j N) i := by
    have h := (div_lt_iff₀ (spacing_pos sc N)).mp (Int.lt_floor_add_one (v i / eps sc N))
    change v i - eps sc N ≤ eps sc N * (⌊v i / eps sc N⌋ : ℝ)
    linarith only [h]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le _ tendsto_const_nhds hhi hlo
  simpa only [sub_zero] using (tendsto_const_nhds (x := v i)).sub hε

end GGOS.Work.Limit

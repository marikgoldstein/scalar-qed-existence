module

public import GGOS.Frozen.Defs.ExpPhi
public import GGOS.Work.LimitState

/-! Finite lattice sampling and the truncated two-test estimate of Proposition 6.1. -/

public section

open MeasureTheory Topology Function Set

namespace GGOS.Work.Limit

theorem spacing_pos (sc : Scale) (N : ℕ) : 0 < eps sc N :=
  div_pos sc.a0_pos (pow_pos (by norm_num) _)

private theorem finite_samples {ε : ℝ} (hε : ε ≠ 0) (v : E3) {f : E3 → ℝ}
    (hf : HasCompactSupport f) :
    HasFiniteSupport (fun z : Site ℤ => f (fun i => ε * ((z i : ℝ) + v i))) := by
  let j (i : Fin 3) (m : ℤ) := ε * ((m : ℝ) + v i)
  have hj : IsClosedEmbedding (Pi.map j) := IsClosedEmbedding.piMap fun i =>
    (Homeomorph.mulLeft₀ ε hε).isClosedEmbedding.comp
      ((Homeomorph.addRight (v i)).isClosedEmbedding.comp Int.isClosedEmbedding_coe_real)
  exact (isCompact_iff_finite.mp (hj.isCompact_preimage hf)).subset
    (fun z hz => subset_tsupport f hz)

private noncomputable abbrev faceValue (ε : ℝ) (σ : T) (q : Plaq ℤ) :=
  σ.1.1 q.2.1.1 q.2.1.2 (plaqCentre ε q)

private abbrev siteValue (ε : ℝ) (σ : T) (z : Site ℤ) := σ.1.2 (sitePos ε z)

private theorem finite_sites {ε : ℝ} (hε : ε ≠ 0) (σ : T) : HasFiniteSupport (siteValue ε σ) := by
  change HasFiniteSupport (fun z : Site ℤ => σ.1.2 (fun i => ε * (z i : ℝ)))
  simpa only [Pi.zero_apply, add_zero] using
    finite_samples hε 0 σ.isTestPair.compact_h

private theorem finite_faces {ε : ℝ} (hε : ε ≠ 0) (σ : T) : HasFiniteSupport (faceValue ε σ) := by
  let A (d : Dir2) := support fun z : Site ℤ => faceValue ε σ (z, d)
  have hA (d : Dir2) : (A d).Finite := by
    change HasFiniteSupport (fun z : Site ℤ => σ.1.1 d.1.1 d.1.2 (plaqCentre ε (z, d)))
    exact finite_samples hε (fun i => if i = d.1.1 ∨ i = d.1.2 then 1 / 2 else 0)
      (σ.isTestPair.compact_f d.1.1 d.1.2)
  refine (finite_iUnion (fun d : Dir2 => (hA d).image (fun z => (z, d)))).subset ?_
  rintro ⟨z,d⟩ hz
  exact mem_iUnion.mpr ⟨d, z, hz, rfl⟩

variable (sc : Scale) (N : ℕ) (gd : DensityFn)

private theorem measurable_phase (σ : T) : Measurable (Phi sc N gd σ) := by
  unfold Phi
  refine (measurable_const.mul (.tsum fun q => measurable_const.mul
    ((measurable_pi_apply q).comp measurable_fst))).add (measurable_const.mul (.tsum fun z =>
      measurable_const.mul (gd.measurable.comp ((measurable_pi_apply z).comp measurable_snd))))

private theorem local_phase_comp (σ : T) (g : ℝ → ℂ) : IsLocal (g ∘ Phi sc N gd σ) := by
  classical
  let hP := finite_faces (spacing_pos sc N).ne' σ
  let hX := finite_sites (spacing_pos sc N).ne' σ
  refine ⟨hP.toFinset, hX.toFinset, ?_⟩
  intro x y hxy hy
  apply congrArg g
  unfold Phi
  congr 1
  · congr 1
    apply tsum_congr
    intro q
    by_cases h : faceValue (eps sc N) σ q = 0
    · simp only [show σ.1.1 _ _ (plaqCentre _ q) = 0 from h, zero_mul]
    · rw [hxy q (hP.mem_toFinset.mpr h)]
  · congr 1
    apply tsum_congr
    intro z
    by_cases h : siteValue (eps sc N) σ z = 0
    · simp only [show σ.1.2 (sitePos _ z) = 0 from h, zero_mul]
    · rw [hy z (hX.mem_toFinset.mpr h)]

theorem bbl_exp (σ : T) : IsBBL (expPhi sc N gd σ) :=
  ⟨Complex.continuous_exp.measurable.comp (measurable_const.mul
    (Complex.continuous_ofReal.measurable.comp (measurable_phase sc N gd σ))),
   ⟨1, fun x => (Complex.norm_exp_I_mul_ofReal (Phi sc N gd σ x)).le⟩,
   local_phase_comp sc N gd σ (fun r => Complex.exp (Complex.I * (r : ℂ)))⟩

private theorem bbl_trunc (σ : T) :
    IsBBL (fun x => ((min |Phi sc N gd σ x| 2 : ℝ) : ℂ)) := by
  refine ⟨Complex.continuous_ofReal.measurable.comp
    (((measurable_phase sc N gd σ).abs).min measurable_const), ⟨2, fun x => ?_⟩,
    local_phase_comp sc N gd σ (fun r => ((min |r| 2 : ℝ) : ℂ))⟩
  rw [Complex.norm_real, Real.norm_of_nonneg (le_min (abs_nonneg _) (by norm_num))]
  exact min_le_right _ _

private theorem phase_sub (σ τ : T) (x : Cfg ℤ) :
    Phi sc N gd (σ - τ) x = Phi sc N gd σ x - Phi sc N gd τ x := by
  let ε := eps sc N
  have hF (s : T) : Summable (fun q => faceValue ε s q * x.1 q) :=
    summable_of_hasFiniteSupport ((finite_faces (spacing_pos sc N).ne' s).mul_left x.1)
  have hX (s : T) : Summable (fun z => siteValue ε s z * gd.toFun (x.2 z)) :=
    summable_of_hasFiniteSupport ((finite_sites (spacing_pos sc N).ne' s).mul_left _)
  change ε ^ (3/2 : ℝ) * (∑' q, (faceValue ε σ q - faceValue ε τ q) * x.1 q) +
    ε ^ 3 * (∑' z, (siteValue ε σ z - siteValue ε τ z) * gd.toFun (x.2 z)) = _
  simp_rw [sub_mul]
  rw [(hF σ).tsum_sub (hF τ), (hX σ).tsum_sub (hX τ)]
  unfold Phi
  dsimp only [faceValue, siteValue, ε]
  ring

private theorem exp_sub_bound (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤ min |a-b| 2 := by
  apply le_min
  · have h : Complex.exp (Complex.I * (a : ℂ)) =
        Complex.exp (Complex.I * ((a-b : ℝ) : ℂ)) * Complex.exp (Complex.I * (b : ℂ)) := by
      rw [← Complex.exp_add, Complex.ofReal_sub]
      congr 1
      ring
    rw [h, ← sub_one_mul, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
    exact Real.norm_exp_I_mul_ofReal_sub_one_le
  · simpa only [Complex.norm_exp_I_mul_ofReal, one_add_one_eq_two] using
      norm_sub_le (Complex.exp (Complex.I * (a : ℂ))) (Complex.exp (Complex.I * (b : ℂ)))

variable {ω : (Cfg ℤ → ℂ) → ℂ} {ρ : ℝ}

theorem norm_state_exp_le (hs : IsState ρ ω) (σ : T) : ‖ω (expPhi sc N gd σ)‖ ≤ 1 := by
  have h := state_norm_le hs (bbl_exp sc N gd σ) (fun _ => 1) (bbl_const 1)
    (fun x _ => (Complex.norm_exp_I_mul_ofReal _).le)
  simpa only [Complex.ofReal_one, state_const hs, Complex.one_re] using h

theorem norm_state_exp_sub_le (hs : IsState ρ ω) {p : T → ℝ}
    (hest : ∀ σ : T, (ω fun x => ((min |Phi sc N gd σ x| 2 : ℝ) : ℂ)).re ≤ p σ)
    (σ τ : T) : ‖ω (expPhi sc N gd σ) - ω (expPhi sc N gd τ)‖ ≤ p (σ - τ) := by
  rw [← state_sub hs (bbl_exp sc N gd σ) (bbl_exp sc N gd τ)]
  refine (state_norm_le hs (bbl_sub (bbl_exp sc N gd σ) (bbl_exp sc N gd τ))
    _ (bbl_trunc sc N gd (σ - τ)) ?_).trans (hest _)
  intro x _
  rw [phase_sub]
  exact exp_sub_bound _ _

end GGOS.Work.Limit

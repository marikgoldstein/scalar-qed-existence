module

public import GGOS.Infra.IsState

/-! Positivity and domination on the bounded Borel local observables. -/

public section

open MeasureTheory

namespace GGOS.Work.Limit

variable {F G : Cfg ℤ → ℂ} {ρ : ℝ} {ω : (Cfg ℤ → ℂ) → ℂ}

theorem bbl_const (z : ℂ) : IsBBL (fun _ => z) :=
  ⟨measurable_const, ⟨‖z‖, fun _ => le_rfl⟩, ⟨∅, ∅, fun _ _ _ _ => rfl⟩⟩

private theorem local_comp {f : ℂ → ℂ} (hF : IsLocal F) : IsLocal (f ∘ F) := by
  obtain ⟨P, X, h⟩ := hF
  exact ⟨P, X, fun x y hP hX => congrArg f (h x y hP hX)⟩

theorem bbl_add (hF : IsBBL F) (hG : IsBBL G) : IsBBL (F + G) := by
  classical
  obtain ⟨a, ha⟩ := hF.bounded
  obtain ⟨b, hb⟩ := hG.bounded
  obtain ⟨P, X, hf⟩ := hF.isLocal
  obtain ⟨Q, Y, hg⟩ := hG.isLocal
  refine ⟨hF.measurable.add hG.measurable, ⟨a+b, fun x =>
    (norm_add_le _ _).trans (add_le_add (ha x) (hb x))⟩, P ∪ Q, X ∪ Y, ?_⟩
  intro x y hp hx
  exact congrArg₂ (· + ·)
    (hf x y (fun p h => hp p (Finset.mem_union_left _ h)) (fun q h => hx q (Finset.mem_union_left _ h)))
    (hg x y (fun p h => hp p (Finset.mem_union_right _ h)) (fun q h => hx q (Finset.mem_union_right _ h)))

theorem bbl_smul (z : ℂ) (hF : IsBBL F) : IsBBL (z • F) := by
  obtain ⟨C, hC⟩ := hF.bounded
  refine ⟨measurable_const.mul hF.measurable, ⟨‖z‖ * C, fun x => ?_⟩,
    local_comp (f := fun w => z * w) hF.isLocal⟩
  change ‖z * F x‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)

theorem bbl_sub (hF : IsBBL F) (hG : IsBBL G) : IsBBL (F - G) := by
  simpa only [neg_one_smul, sub_eq_add_neg] using bbl_add hF (bbl_smul (-1) hG)

theorem state_const (hs : IsState ρ ω) (z : ℂ) : ω (fun _ => z) = z := by
  simpa only [Pi.smul_def, smul_eq_mul, mul_one, hs.map_one] using
    hs.map_smul z (fun _ => 1) (bbl_const 1)

theorem state_sub (hs : IsState ρ ω) (hF : IsBBL F) (hG : IsBBL G) :
    ω (F - G) = ω F - ω G := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ G, hs.map_add _ _ hF (bbl_smul _ hG), hs.map_smul _ _ hG]
  simp only [neg_one_mul, sub_eq_add_neg]

private theorem bbl_re (hF : IsBBL F) : IsBBL (fun x => ((F x).re : ℂ)) := by
  obtain ⟨C, hC⟩ := hF.bounded
  exact ⟨Complex.continuous_ofReal.measurable.comp (Complex.continuous_re.measurable.comp hF.measurable),
    ⟨C, fun x => (Complex.norm_real _).le.trans ((Complex.abs_re_le_norm _).trans (hC x))⟩,
    local_comp (f := fun w => (w.re : ℂ)) hF.isLocal⟩

private theorem bbl_im (hF : IsBBL F) : IsBBL (fun x => ((F x).im : ℂ)) := by
  obtain ⟨C, hC⟩ := hF.bounded
  exact ⟨Complex.continuous_ofReal.measurable.comp (Complex.continuous_im.measurable.comp hF.measurable),
    ⟨C, fun x => (Complex.norm_real _).le.trans ((Complex.abs_im_le_norm _).trans (hC x))⟩,
    local_comp (f := fun w => (w.im : ℂ)) hF.isLocal⟩

private theorem state_real_im (hs : IsState ρ ω) (f : Cfg ℤ → ℝ)
    (hf : IsBBL (fun x => (f x : ℂ))) : (ω (fun x => (f x : ℂ))).im = 0 := by
  obtain ⟨C, hC⟩ := hf.bounded
  let F := fun x => (f x : ℂ)
  let G := fun _ : Cfg ℤ => (C : ℂ)
  obtain ⟨r, _, hr⟩ := hs.nonneg (F + G) (bbl_add hf (bbl_const C)) (by
    intro x _
    have hx : |f x| ≤ C := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hC x
    exact ⟨f x + C, by linarith only [(abs_le.mp hx).1], by simp [F, G]⟩)
  rw [hs.map_add _ _ hf (bbl_const C), state_const hs C] at hr
  simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using congrArg Complex.im hr

private theorem state_re (hs : IsState ρ ω) (hF : IsBBL F) :
    (ω (fun x => ((F x).re : ℂ))).re = (ω F).re := by
  let R := fun x => ((F x).re : ℂ)
  let J := fun x => ((F x).im : ℂ)
  have hj : (ω J).im = 0 := state_real_im hs _ (bbl_im hF)
  have hsplit : R + Complex.I • J = F := by
    funext x
    change ((F x).re : ℂ) + Complex.I * ((F x).im : ℂ) = F x
    rw [mul_comm Complex.I, Complex.re_add_im]
  nth_rw 2 [← hsplit]
  rw [hs.map_add _ _ (bbl_re hF) (bbl_smul _ (bbl_im hF)), hs.map_smul _ _ (bbl_im hF)]
  dsimp only [J] at hj
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, hj,
    sub_zero, add_zero]

/-- A positive state is dominated by the state value of a pointwise real majorant. -/
theorem state_norm_le (hs : IsState ρ ω) (hF : IsBBL F) (g : Cfg ℤ → ℝ)
    (hg : IsBBL (fun x => (g x : ℂ))) (hle : ∀ x ∈ OmegaN ρ, ‖F x‖ ≤ g x) :
    ‖ω F‖ ≤ (ω (fun x => (g x : ℂ))).re := by
  obtain ⟨z, hz, heq⟩ := Complex.exists_norm_eq_mul_self (ω F)
  let H := z • F
  let R := fun x => ((H x).re : ℂ)
  let G := fun x => (g x : ℂ)
  have hH : IsBBL H := bbl_smul z hF
  obtain ⟨r, hr, he⟩ := hs.nonneg (G - R) (bbl_sub hg (bbl_re hH)) (by
    intro x hx
    refine ⟨g x - (H x).re, sub_nonneg.mpr ((Complex.re_le_norm _).trans ?_), by simp [G, R]⟩
    change ‖z * F x‖ ≤ g x
    rw [norm_mul, hz, one_mul]
    exact hle x hx)
  rw [state_sub hs hg (bbl_re hH)] at he
  have hreal : (ω G).re - (ω R).re = r := congrArg Complex.re he
  have hR : (ω R).re = ‖ω F‖ := by
    rw [state_re hs hH, show ω H = z * ω F from hs.map_smul z F hF, ← heq, Complex.ofReal_re]
  change ‖ω F‖ ≤ (ω G).re
  linarith only [hr, hreal, hR]

end GGOS.Work.Limit

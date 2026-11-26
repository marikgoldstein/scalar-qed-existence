module

public import GGOS.Frozen.Defs.Pull
public import GGOS.OS.Work.TorusProduct
public import GGOS.Work.TorusSymmetryWeight

/-!
# Reflection positivity of the torus state at the site planes ([GG-OS] Theorem 9.7, `c = 0`)
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexOrder

namespace GGOS.OS

/-! ### The reflection of the sites -/

section Flip

variable {n : ℕ}

/-- The flip of the time coordinate, `t ↦ -t - δ` (`δ = 1` for the cells with a time edge). -/
def flip (δ : ZMod n) (x : Site (ZMod n)) : Site (ZMod n) := Function.update x 2 (-x 2 - δ)

theorem flip_two (δ : ZMod n) (x : Site (ZMod n)) : flip δ x 2 = -x 2 - δ := by simp [flip]

theorem flip_flip (δ : ZMod n) (x : Site (ZMod n)) : flip δ (flip δ x) = x := by
  funext i
  by_cases hi : i = 2
  · subst hi; simp [flip]
  · simp [flip, Function.update_of_ne hi]

theorem flip_add_unit {μ : Fin 3} (hμ : μ ≠ 2) (δ : ZMod n) (x : Site (ZMod n)) :
    flip δ (x + unitVec (ZMod n) μ) = flip δ x + unitVec (ZMod n) μ := by
  funext i
  by_cases hi : i = 2
  · subst hi
    simp [flip, unitVec, Pi.single_eq_of_ne hμ.symm]
  · simp [flip, Function.update_of_ne hi]

theorem flip_zero_add_unit_two (x : Site (ZMod n)) :
    flip 0 (x + unitVec (ZMod n) 2) = flip 1 x := by
  funext i
  by_cases hi : i = 2
  · subst hi
    simp [flip, unitVec]
    ring
  · simp [flip, unitVec, Function.update_of_ne hi, Pi.single_eq_of_ne hi]

theorem flip_one_add_unit_two (x : Site (ZMod n)) :
    flip 1 x + unitVec (ZMod n) 2 = flip 0 x := by
  funext i
  by_cases hi : i = 2
  · subst hi
    simp [flip, unitVec]
  · simp [flip, unitVec, Function.update_of_ne hi, Pi.single_eq_of_ne hi]

theorem dir2_cases (d : Dir2) : d = d01 ∨ d = d02 ∨ d = d12 := by
  revert d
  decide

/-- The time shift of a bond. -/
def bShift (μ : Fin 3) : ZMod n := if μ = 2 then 1 else 0

/-- The time shift of a plaquette. -/
def pShift (d : Dir2) : ZMod n := if d.1.2 = 2 then 1 else 0

/-- The sign of a bond. -/
def bSign (μ : Fin 3) : ℝ := if μ = 2 then -1 else 1

/-- The sign of a plaquette. -/
def pSign (d : Dir2) : ℝ := if d.1.2 = 2 then -1 else 1

/-- The reflected bond. -/
def rBond (b : Bond (ZMod n)) : Bond (ZMod n) := (flip (bShift b.2) b.1, b.2)

/-- The reflected plaquette. -/
def rPlaq (p : Plaq (ZMod n)) : Plaq (ZMod n) := (flip (pShift p.2) p.1, p.2)

theorem rBond_rBond (b : Bond (ZMod n)) : rBond (rBond b) = b := by
  simp [rBond, flip_flip]

theorem rPlaq_rPlaq (p : Plaq (ZMod n)) : rPlaq (rPlaq p) = p := by
  simp [rPlaq, flip_flip]

/-- The boundary of the reflected bond variables. -/
theorem dBond_refl (B : Bond (ZMod n) → ℝ) (p : Plaq (ZMod n)) :
    dBond (fun b => bSign b.2 * B (rBond b)) p = pSign p.2 * dBond B (rPlaq p) := by
  obtain ⟨x, d⟩ := p
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  rcases dir2_cases d with rfl | rfl | rfl
  · simp [dBond, d01, rBond, rPlaq, bSign, pSign, bShift, pShift, flip_add_unit h02,
      flip_add_unit h12]
  · simp [dBond, d02, rBond, rPlaq, bSign, pSign, bShift, pShift,
      flip_add_unit h02, flip_zero_add_unit_two, flip_one_add_unit_two]
    ring
  · simp [dBond, d12, rBond, rPlaq, bSign, pSign, bShift, pShift,
      flip_add_unit h12, flip_zero_add_unit_two, flip_one_add_unit_two]
    ring

/-- The coboundary of the reflected plaquette variables. -/
theorem dPlaqR_refl (m : Plaq (ZMod n) → ℝ) (x : Site (ZMod n)) :
    dPlaqR (fun p => pSign p.2 * m (rPlaq p)) x = -dPlaqR m (flip 1 x) := by
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have e01 : d01.1.2 ≠ 2 := by decide
  have e02 : d02.1.2 = 2 := by decide
  have e12 : d12.1.2 = 2 := by decide
  simp only [dPlaqR, rPlaq, pSign, pShift, ite_eq_right e01, ite_eq_left e02, ite_eq_left e12,
    flip_add_unit h02, flip_add_unit h12, flip_zero_add_unit_two, flip_one_add_unit_two]
  ring

/-- The reflected configuration of the gauge-invariant variables. -/
def reflCfg (ω : Cfg (ZMod n)) : Cfg (ZMod n) :=
  (fun p => pSign p.2 * ω.1 (rPlaq p), fun x => ω.2 (flip 0 x))

/-- The time reflection as a symmetry of the lattice. -/
def timeRefl (R : Type*) [CommRing R] : LatSym R :=
  ⟨Equiv.refl _, ![1, 1, -1], 0⟩

theorem timeRefl_act (x : Site (ZMod n)) : (timeRefl (ZMod n)).act x = flip 0 x := by
  funext i
  fin_cases i <;> simp [timeRefl, LatSym.act, flip]

theorem pull_timeRefl (ω : Cfg (ZMod n)) : pull (timeRefl (ZMod n)) ω = reflCfg ω := by
  have hc (μ : Fin 3) (hμ : μ ≠ 2) : (timeRefl (ZMod n)).corner μ = 0 := by
    fin_cases μ <;> simp_all [timeRefl, LatSym.corner]
  have hc2 : (timeRefl (ZMod n)).corner 2 = -unitVec (ZMod n) 2 := by
    simp [timeRefl, LatSym.corner]
  have hf (x : Site (ZMod n)) : flip 0 x + -unitVec (ZMod n) 2 = flip 1 x := by
    rw [← flip_one_add_unit_two]
    abel
  refine Prod.ext (funext fun p => ?_) (funext fun x => ?_)
  · obtain ⟨x, d⟩ := p
    rcases dir2_cases d with rfl | rfl | rfl
    · simp [pull, reflCfg, timeRefl_act, hc, d01, evalAnti, pSign, rPlaq, pShift]
      simp [timeRefl]
    · simp [pull, reflCfg, timeRefl_act, hc, hc2, d02, evalAnti, pSign, rPlaq, pShift, hf]
      simp [timeRefl]
    · simp [pull, reflCfg, timeRefl_act, hc, hc2, d12, evalAnti, pSign, rPlaq, pShift, hf]
      simp [timeRefl]
  · simp [pull, reflCfg, timeRefl_act]

end Flip

end GGOS.OS

end

end

module

public import GGOS.Work.TorusSymmetryCells
public import GGOS.Frozen.Defs.Curv

/-!
# Forward differences and the oriented plaquette boundary
-/

@[expose] public section

noncomputable section

namespace GGOS.TorusSymmetry

variable {R : Type*} [CommRing R]
variable {A : Type*} [AddCommGroup A]

def delta (f : Site R → A) (i : Fin 3) (x : Site R) : A :=
  f (x + unitVec R i) - f x

theorem delta_sign (u : ℤˣ) (f : Site R → A) (i : Fin 3) (x : Site R) :
    delta (fun y => sign u (f y)) i x = sign u (delta f i x) :=
  (map_sub ..).symm

/-- A reversed step contributes a minus sign and starts one unit further back. -/
theorem delta_affine (g : LatSym R) (f : Site R → A) (t : Site R) (i : Fin 3) (x : Site R) :
    delta (fun y => f (g.act y + t)) i x =
      sign (g.sgn i) (delta f (g.perm i) (g.act x + t + g.corner i)) := by
  by_cases h : g.sgn i = 1
  · simp [delta, act_add_unitVec, LatSym.corner, sign, h, add_right_comm]
  · simp [delta, act_add_unitVec, LatSym.corner, sign, h, neg_sub, add_right_comm]

private theorem dBond_eq_delta (B : Bond R → ℝ) (p : Plaq R) :
    dBond B p = delta (fun x => B (x, p.2.1.2)) p.2.1.1 p.1 -
      delta (fun x => B (x, p.2.1.1)) p.2.1.2 p.1 := by
  unfold dBond delta
  abel

private theorem alt_dBond (B : Bond R → ℝ) (x : Site R) (i j : Fin 3) :
    alt (dBond B) x i j =
      delta (fun y => B (y,j)) i x - delta (fun y => B (y,i)) j x := by
  rcases lt_trichotomy i j with h | rfl | h
  · simp [alt, h, dBond_eq_delta]
  · simp [alt]
  · simp [alt, h, h.not_gt, dBond_eq_delta]

private theorem delta_bondField (g : LatSym R) (B : Bond R → ℝ) (i j : Fin 3) (x : Site R) :
    delta (fun y => bondField g B (y,j)) i x = sign (g.sgn i) (sign (g.sgn j)
      (delta (fun y => B (y, g.perm j)) (g.perm i) (g.act x + g.corner i + g.corner j))) := by
  change delta (fun y => sign (g.sgn j) (B (g.act y + g.corner j, g.perm j))) i x = _
  rw [delta_sign, delta_affine g (fun y => B (y, g.perm j)), sign_comm (g.sgn j),
    add_right_comm (g.act x) (g.corner j)]

theorem dBond_bondField (g : LatSym R) (B : Bond R → ℝ) (p : Plaq R) :
    dBond (bondField g B) p = faceField g (dBond B) p := by
  rw [dBond_eq_delta]
  simp only [delta_bondField, faceField, faceValue, alt_dBond, map_sub]
  rw [sign_comm (g.sgn p.2.1.2) (g.sgn p.2.1.1),
    add_right_comm (g.act p.1) (g.corner p.2.1.2) (g.corner p.2.1.1)]

theorem curv_bondField (c : Coeffs) (g : LatSym R) (B : Bond R → ℝ) (m : Plaq R → ℤ)
    (p : Plaq R) :
    curv c (bondField g B) (faceField g m) p = faceField g (curv c B m) p := by
  rw [curv, dBond_bondField]
  simp only [faceField_apply, curv, map_add]
  by_cases ho : g.perm p.2.1.1 < g.perm p.2.1.2 <;>
    by_cases hi : g.sgn p.2.1.1 = 1 <;> by_cases hj : g.sgn p.2.1.2 = 1 <;>
    simp [faceSign, sign, ho, hi, hj]

theorem pull_eq_faceField (g : LatSym R) (ω : Cfg R) :
    pull g ω = (faceField g ω.1, fun x => ω.2 (g.act x)) := by
  refine Prod.ext ?_ rfl
  funext p
  have he (y : Site R) (i j : Fin 3) : evalAnti ω.1 y i j = alt ω.1 y i j := rfl
  rcases Int.units_eq_one_or (g.sgn p.2.1.1) with hi | hi <;>
    rcases Int.units_eq_one_or (g.sgn p.2.1.2) with hj | hj <;>
    simp [pull, faceField, faceValue, sign, hi, hj, he]

end GGOS.TorusSymmetry

end

end

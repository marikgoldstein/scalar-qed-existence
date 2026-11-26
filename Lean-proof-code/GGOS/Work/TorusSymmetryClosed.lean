module

public import GGOS.Work.TorusSymmetryBoundary
public import GGOS.Frozen.Defs.IsClosedForm

/-!
# The signed boundary of a transformed cube
-/

@[expose] public section

noncomputable section

namespace GGOS.TorusSymmetry

variable {R : Type*} [CommRing R]

/-- The three pairs of opposite faces, read in the ordered frame `i, j, k`. -/
private def cube (m : Plaq R → ℤ) (x : Site R) (i j k : Fin 3) : ℤ :=
  delta (fun y => alt m y j k) i x - delta (fun y => alt m y i k) j x +
    delta (fun y => alt m y i j) k x

private theorem cube_eq_zero_iff (m : Plaq R → ℤ) (x : Site R) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    cube m x i j k = 0 ↔ dPlaq m x = 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all +decide [cube, delta, alt, dPlaq, d01, d02, d12] <;> omega

private theorem delta_faceValue (g : LatSym R) (m : Plaq R → ℤ) (i j k : Fin 3) (x : Site R) :
    delta (faceValue g m j k) i x = sign (g.sgn i) (sign (g.sgn j) (sign (g.sgn k)
      (delta (fun y => alt m y (g.perm j) (g.perm k)) (g.perm i)
        (g.act x + (g.corner j + g.corner k) + g.corner i)))) := by
  unfold faceValue
  simp_rw [add_assoc (g.act _) (g.corner j) (g.corner k)]
  rw [delta_sign, delta_sign, delta_affine g (fun y => alt m y (g.perm j) (g.perm k)),
    sign_comm (g.sgn k) (g.sgn i),
    sign_comm (g.sgn j) (g.sgn i)]

private theorem dPlaq_faceField (g : LatSym R) (m : Plaq R → ℤ) (x : Site R) :
    dPlaq (faceField g m) x = sign (g.sgn 0) (sign (g.sgn 1) (sign (g.sgn 2)
      (cube m (g.act x + (g.corner 0 + g.corner 1 + g.corner 2))
        (g.perm 0) (g.perm 1) (g.perm 2)))) := by
  change delta (faceValue g m 1 2) 0 x - delta (faceValue g m 0 2) 1 x +
    delta (faceValue g m 0 1) 2 x = _
  simp only [delta_faceValue, cube, map_add, map_sub, sign_comm, add_comm,
    add_left_comm]

theorem isClosedForm_faceField_iff (g : LatSym R) (m : Plaq R → ℤ) :
    IsClosedForm (faceField g m) ↔ IsClosedForm m := by
  let t := g.corner 0 + g.corner 1 + g.corner 2
  have hpoint (x : Site R) : dPlaq (faceField g m) x = 0 ↔ dPlaq m (g.act x + t) = 0 := by
    rw [dPlaq_faceField]
    simpa only [AddEquiv.map_eq_zero_iff] using
      cube_eq_zero_iff m (g.act x + t) (g.perm 0) (g.perm 1) (g.perm 2)
        (g.perm.injective.ne (by decide)) (g.perm.injective.ne (by decide))
        (g.perm.injective.ne (by decide))
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := ((siteEquiv g).trans (Equiv.addRight t)).surjective y
    change g.act x + t = y at hx
    exact hx ▸ (hpoint x).mp (h x)
  · intro h x
    exact (hpoint x).mpr (h _)

/-- The permutation used to reindex the sum over closed Villain variables. -/
def closedEquiv (g : LatSym R) :
    {m : Plaq R → ℤ // IsClosedForm m} ≃ {m : Plaq R → ℤ // IsClosedForm m} :=
  (faceFieldEquiv g).subtypeEquiv fun m => by
    rw [faceFieldEquiv_apply]
    exact (isClosedForm_faceField_iff g m).symm

theorem closedEquiv_apply (g : LatSym R) (m : {m : Plaq R → ℤ // IsClosedForm m}) :
    (closedEquiv g m).1 = faceField g m.1 :=
  faceFieldEquiv_apply g m.1

end GGOS.TorusSymmetry

end

end

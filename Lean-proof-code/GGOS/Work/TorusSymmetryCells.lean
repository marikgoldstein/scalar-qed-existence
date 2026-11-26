module

public import GGOS.Frozen.Defs.Pull

/-!
# Signed permutations of lattice cells
-/

@[expose] public section

noncomputable section

namespace GGOS.TorusSymmetry

variable {R : Type*} [CommRing R]
variable {A : Type*} [AddCommGroup A]

/-- Change the orientation of a coefficient according to an integer unit. -/
def sign (u : ℤˣ) : A ≃+ A :=
  if u = 1 then AddEquiv.refl A else AddEquiv.neg A

theorem sign_comm (u v : ℤˣ) (a : A) : sign u (sign v a) = sign v (sign u a) := by
  by_cases h : u = 1 <;> simp [sign, h]

/-- The inverse first subtracts the translation, then undoes each signed coordinate. -/
def siteEquiv (g : LatSym R) : Site R ≃ Site R where
  toFun := g.act
  invFun y i := (((g.sgn i : ℤˣ) : ℤ) : R) * (y (g.perm i) - g.shift (g.perm i))
  left_inv x := by
    funext i
    rcases Int.units_eq_one_or (g.sgn i) with h | h <;> simp [LatSym.act, h]
  right_inv y := by
    funext j
    obtain ⟨i, rfl⟩ := g.perm.surjective j
    rcases Int.units_eq_one_or (g.sgn i) with h | h <;> simp [LatSym.act, h]

theorem act_add_unitVec (g : LatSym R) (x : Site R) (i : Fin 3) :
    g.act (x + unitVec R i) = g.act x + sign (g.sgn i) (unitVec R (g.perm i)) := by
  funext j
  obtain ⟨k, rfl⟩ := g.perm.surjective j
  by_cases hk : k = i
  · subst k
    rcases Int.units_eq_one_or (g.sgn i) with h | h <;>
      simp [sign, LatSym.act, unitVec, h] <;> abel
  · have hne := g.perm.injective.ne hk
    rcases Int.units_eq_one_or (g.sgn i) with h | h <;>
      simp [sign, LatSym.act, unitVec, h, Pi.single_eq_of_ne, hk, hne]

/-- Sort the image of a pair of distinct directions into the stored order. -/
def dirImage (e : Equiv.Perm (Fin 3)) (d : Dir2) : Dir2 :=
  if h : e d.1.1 < e d.1.2 then ⟨(e d.1.1, e d.1.2), h⟩
  else ⟨(e d.1.2, e d.1.1), lt_of_le_of_ne (le_of_not_gt h) (e.injective.ne d.2.ne.symm)⟩

theorem dirImage_left_inv (e : Equiv.Perm (Fin 3)) (d : Dir2) :
    dirImage e.symm (dirImage e d) = d := by
  obtain ⟨⟨i, j⟩, hij⟩ := d
  by_cases h : e i < e j <;> simp [dirImage, h, hij, hij.not_gt]

def dirEquiv (e : Equiv.Perm (Fin 3)) : Dir2 ≃ Dir2 where
  toFun := dirImage e
  invFun := dirImage e.symm
  left_inv := dirImage_left_inv e
  right_inv := dirImage_left_inv e.symm

/-- Each direction has its own displacement of the base site. -/
def cellEquiv {D : Type*} (g : LatSym R) (e : D ≃ D) (t : D → Site R) :
    Site R × D ≃ Site R × D :=
  (Equiv.prodCongrLeft fun d => (siteEquiv g).trans (Equiv.addRight (t d))).trans
    ((Equiv.refl _).prodCongr e)

def bondEquiv (g : LatSym R) : Bond R ≃ Bond R :=
  cellEquiv g g.perm g.corner

def plaqEquiv (g : LatSym R) : Plaq R ≃ Plaq R :=
  cellEquiv g (dirEquiv g.perm) fun d => g.corner d.1.1 + g.corner d.1.2

def bondField (g : LatSym R) (B : Bond R → A) (b : Bond R) : A :=
  sign (g.sgn b.2) (B (bondEquiv g b))

/-- Antisymmetric evaluation for both real and integer coefficients. -/
def alt (m : Plaq R → A) (y : Site R) (i j : Fin 3) : A :=
  if h : i < j then m (y, ⟨(i,j), h⟩)
  else if h' : j < i then -m (y, ⟨(j,i), h'⟩) else 0

def faceValue (g : LatSym R) (m : Plaq R → A) (i j : Fin 3) (x : Site R) : A :=
  sign (g.sgn i) (sign (g.sgn j)
    (alt m (g.act x + g.corner i + g.corner j) (g.perm i) (g.perm j)))

def faceField (g : LatSym R) (m : Plaq R → A) (p : Plaq R) : A :=
  faceValue g m p.2.1.1 p.2.1.2 p.1

/-- The sign of a plaquette includes the permutation that sorts its image directions. -/
def faceSign (g : LatSym R) (d : Dir2) : A ≃+ A :=
  (if g.perm d.1.1 < g.perm d.1.2 then AddEquiv.refl A else AddEquiv.neg A).trans
    ((sign (g.sgn d.1.2)).trans (sign (g.sgn d.1.1)))

theorem faceField_apply (g : LatSym R) (m : Plaq R → A) (p : Plaq R) :
    faceField g m p = faceSign g p.2 (m (plaqEquiv g p)) := by
  obtain ⟨x, ⟨⟨i,j⟩, hij⟩⟩ := p
  change _ = faceSign g ⟨(i,j), hij⟩
    (m (g.act x + (g.corner i + g.corner j), dirImage g.perm ⟨(i,j), hij⟩))
  rcases lt_or_gt_of_ne (g.perm.injective.ne hij.ne) with h | h <;>
    simp [faceField, faceValue, faceSign, alt, dirImage, h, h.not_gt, add_assoc]

/-- Pulling back plaquette coefficients is a bijection, before imposing closedness. -/
def faceFieldEquiv (g : LatSym R) : (Plaq R → A) ≃ (Plaq R → A) :=
  ((plaqEquiv g).symm.arrowCongr (Equiv.refl A)).trans
    (Equiv.piCongrRight fun p => (faceSign g p.2).toEquiv)

theorem faceFieldEquiv_apply (g : LatSym R) (m : Plaq R → A) :
    faceFieldEquiv g m = faceField g m := by
  funext p
  exact (faceField_apply g m p).symm

end GGOS.TorusSymmetry

end

end

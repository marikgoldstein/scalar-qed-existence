module

public import GGOS.Frozen.Defs.IsClosedForm
public import GGOS.Frozen.Defs.DBond

/-!
# The incidence pairings in the closed-flux projector
-/

@[expose] public section

namespace GGOS.Work.GD

variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]

/-- The oriented boundary of a cube, evaluated on plaquette data in any additive group. -/
def cubeSum {K : Type*} [AddCommGroup K] (m : Plaq R → K) (x : Site R) : K :=
  (m (x + unitVec R 0, d12) - m (x, d12)) - (m (x + unitVec R 1, d02) - m (x, d02))
    + (m (x + unitVec R 2, d01) - m (x, d01))

def delta {ι : Type*} [DecidableEq ι] (i j : ι) : ℤ := if j = i then 1 else 0

private theorem sum_delta {ι K : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]
    (f : ι → K) (i : ι) : (∑ j, (delta i j : K) * f j) = f i := by
  simp [delta, apply_ite ((↑) : ℤ → K), ite_mul]

/-- Incidence number of a plaquette in a cube. -/
noncomputable def cubeInc (x : Site R) (p : Plaq R) : ℤ := cubeSum (fun q => delta q p) x

/-- Incidence number of a bond in a plaquette. -/
noncomputable def bondInc (p : Plaq R) (b : Bond R) : ℤ :=
  delta (p.1, p.2.1.1) b + delta (p.1 + unitVec R p.2.1.1, p.2.1.2) b
    - delta (p.1 + unitVec R p.2.1.2, p.2.1.1) b - delta (p.1, p.2.1.2) b

/-- The real shift of the dual plaquette frequencies from the cube characters. -/
noncomputable def cubeAdj (t : Site R → ℝ) (p : Plaq R) : ℝ := ∑ x, t x * cubeInc x p

/-- The integer frequency of the character on a bond. -/
noncomputable def bondFreq (m : Plaq R → ℤ) (b : Bond R) : ℤ := ∑ p, m p * bondInc p b

private theorem sum_cubeInc {K : Type*} [CommRing K] (f : Plaq R → K) (x : Site R) :
    (∑ p, (cubeInc x p : K) * f p) = cubeSum f x := by
  simp only [cubeInc, cubeSum, Int.cast_add, Int.cast_sub, sub_mul, add_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_delta]

private theorem sum_bondInc (B : Bond R → ℝ) (p : Plaq R) :
    (∑ b, (bondInc p b : ℝ) * B b) = dBond B p := by
  simp only [bondInc, dBond, Int.cast_add, Int.cast_sub, sub_mul, add_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_delta]

private theorem transpose_pair {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → κ → ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    (∑ j, (∑ i, x i * A i j) * y j) = ∑ i, x i * ∑ j, A i j * y j := by
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

theorem pair_cubeAdj (t : Site R → ℝ) (m : Plaq R → ℤ) :
    (∑ p, cubeAdj t p * (m p : ℝ)) = ∑ x, t x * dPlaq m x := by
  unfold cubeAdj
  rw [transpose_pair]
  simp_rw [sum_cubeInc]
  simp [cubeSum, dPlaq]

theorem pair_bondFreq (m : Plaq R → ℤ) (B : Bond R → ℝ) :
    (∑ b, (bondFreq m b : ℝ) * B b) = ∑ p, (m p : ℝ) * dBond B p := by
  unfold bondFreq
  push_cast
  rw [transpose_pair]
  simp_rw [sum_bondInc]

omit [Fintype R] [DecidableEq R] in
/-- The two oriented incidences compose to zero, including across the periodic boundary. -/
theorem cubeSum_dBond (B : Bond R → ℝ) (x : Site R) : cubeSum (dBond B) x = 0 := by
  unfold cubeSum dBond d01 d02 d12
  simp only [add_assoc, add_comm (unitVec R 1) (unitVec R 0),
    add_comm (unitVec R 2) (unitVec R 0), add_comm (unitVec R 2) (unitVec R 1)]
  abel

theorem pair_cubeAdj_dBond (t : Site R → ℝ) (B : Bond R → ℝ) :
    (∑ p, cubeAdj t p * dBond B p) = 0 := by
  unfold cubeAdj
  rw [transpose_pair]
  simp only [sum_cubeInc, cubeSum_dBond, mul_zero, Finset.sum_const_zero]

end GGOS.Work.GD

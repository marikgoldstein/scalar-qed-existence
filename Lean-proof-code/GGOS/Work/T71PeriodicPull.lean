module

public import GGOS.Frozen.Defs.Per
public import GGOS.Frozen.Defs.IsLocal
public import GGOS.Work.TorusSymmetryBoundary

/-!
# Periodic extension and lattice symmetries
-/

@[expose] public section

namespace GGOS.Work

/-- Reduction of an affine lattice symmetry modulo the torus side. -/
def torusLatSym (n : ℕ) (g : LatSym ℤ) : LatSym (ZMod n) :=
  ⟨g.perm, g.sgn, castSite n g.shift⟩

/-- Periodic extension intertwines the torus and lattice actions, including on reversed faces. -/
theorem per_pull (n : ℕ) (g : LatSym ℤ) (w : Cfg (ZMod n)) :
    per n (pull (torusLatSym n g) w) = pull g (per n w) := by
  have act (x : Site ℤ) :
      (torusLatSym n g).act (castSite n x) = castSite n (g.act x) := by
    funext i
    simp [torusLatSym, LatSym.act, castSite]
  have corner (i : Fin 3) :
      (torusLatSym n g).corner i = castSite n (g.corner i) := by
    funext j
    by_cases hs : g.sgn i = 1
    · simp [torusLatSym, LatSym.corner, hs, castSite]
    · by_cases hj : j = g.perm i <;>
        simp [torusLatSym, LatSym.corner, hs, castSite, unitVec, hj, Pi.single_eq_of_ne]
  have cast_add (x y : Site ℤ) :
      castSite n (x + y) = castSite n x + castSite n y := by
    funext i
    exact Int.cast_add ..
  refine Prod.ext ?_ (funext fun x => congrArg w.2 (act x))
  funext ⟨x, ⟨⟨i, j⟩, _⟩⟩
  change _ * evalAnti w.1 ((torusLatSym n g).act (castSite n x) +
      (torusLatSym n g).corner i + (torusLatSym n g).corner j) (g.perm i) (g.perm j) =
    _ * evalAnti (per n w).1 (g.act x + g.corner i + g.corner j) (g.perm i) (g.perm j)
  rw [act, corner, corner, ← cast_add, ← cast_add]
  unfold evalAnti
  split_ifs <;> rfl

theorem continuous_pull {R : Type*} [CommRing R] (g : LatSym R) : Continuous (pull g) := by
  unfold pull
  apply Continuous.prodMk
  · refine continuous_pi fun p => ?_
    unfold evalAnti
    split_ifs <;> fun_prop
  · exact continuous_pi fun x => (continuous_apply (g.act x)).comp continuous_snd

theorem isLocal_comp_pull {F : Cfg ℤ → ℂ} (hF : IsLocal F) (g : LatSym ℤ) :
    IsLocal (F ∘ pull g) := by
  classical
  obtain ⟨P, X, h⟩ := hF
  refine ⟨P.image (TorusSymmetry.plaqEquiv g), X.image g.act, ?_⟩
  intro w w' hp hx
  apply h
  · intro p hP
    simp only [TorusSymmetry.pull_eq_faceField, TorusSymmetry.faceField_apply]
    rw [hp _ (Finset.mem_image_of_mem _ hP)]
  · exact fun x hX => hx _ (Finset.mem_image_of_mem _ hX)

end GGOS.Work

end

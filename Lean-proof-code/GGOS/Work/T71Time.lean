module

public import Mathlib
public import GGOS.Frozen.Defs.IsLimitPoint
public import GGOS.Frozen.Defs.LatticeInvariant
public import GGOS.Frozen.Defs.Iota
public import GGOS.Frozen.Defs.TauA
public import GGOS.Frozen.Defs.Phi
public import GGOS.Frozen.Defs.PairNorm
public import GGOS.Infra.IsState
public import GGOS.Work.LimitAlgebra
public import GGOS.Work.LimitLattice

public section

open MeasureTheory Filter Topology

/-!
# Discrete time invariance from lattice invariance
-/

namespace GGOS.Work

private theorem single_two_eq_sitePos (sc : Scale) (N : ℕ) (k : ℤ) :
    (Pi.single 2 (eps sc N * k) : E3) = sitePos (eps sc N) (Pi.single 2 k) := by
  funext i
  by_cases hi : i = 2
  · rw [hi]
    simp [sitePos]
  · simp [sitePos, Pi.single_eq_of_ne, hi]

/-- Lattice invariance of a state gives the discrete time invariance of the realised algebra:
`ω_N(ι_N(τ_{ε_N k} a)) = ω_N(ι_N(a))` ([GG-OS] Lemma 5.1, second sentence). -/
theorem time_of_latticeInvariant (sc : Scale) (N : ℕ) (gd : DensityFn) (ρ0 : ℝ)
    (ω : (Cfg ℤ → ℂ) → ℂ) (hs : IsState ρ0 ω) (hi : LatticeInvariant ω) (a : Alg) (k : ℤ) :
    ω (iota sc N gd (tauA (eps sc N * k) a)) = ω (iota sc N gd a) := by
  let Z : T → ℂ := fun s => ω (expPhi sc N gd s)
  have hc (b : Alg) : Tendsto (fun _ : ℕ => ω (iota sc N gd b)) atTop (𝓝 (ω (iota sc N gd b))) :=
    tendsto_const_nhds
  have htend (b : Alg) :
      Tendsto (fun _ : ℕ => ω (iota sc N gd b)) atTop (𝓝 (Limit.linearExtension Z b)) :=
    Limit.tendsto_iota sc gd (ρ := fun _ => ρ0) (ω := fun _ => ω) (Nm := fun _ => N)
      (fun _ => hs) (Z := Z) (fun _ => tendsto_const_nhds) b
  have hiota (b : Alg) : ω (iota sc N gd b) = Limit.linearExtension Z b :=
    tendsto_nhds_unique (hc b) (htend b)
  have hZ (s : T) : Z (transl (Pi.single 2 (eps sc N * k)) s) = Z s := by
    dsimp only [Z]
    rw [single_two_eq_sitePos sc N k]
    exact Limit.state_exp_mesh_eq sc N gd hi s (Pi.single 2 k)
  rw [tauA, hiota, hiota]
  exact Limit.extension_transl (Pi.single 2 (eps sc N * k)) hZ a

end GGOS.Work

end

module

public import Mathlib
public import GGOS.Frozen.Defs.Aplus
public import GGOS.Frozen.Defs.Iota
public import GGOS.Frozen.Defs.IsLimitPoint
public import GGOS.Frozen.Defs.LatSymAct
public import GGOS.Frozen.Defs.Mnorm
public import GGOS.Frozen.Defs.SitePos
public import GGOS.Frozen.Defs.TauA
public import GGOS.Frozen.Defs.ThetaA
public import GGOS.Frozen.Defs.TranslA
public import GGOS.Infra.Alg
public import GGOS.Infra.LatSym
public import GGOS.Infra.Motion

public import GGOS.Frozen.PassageToLimit
public import GGOS.Frozen.PairNorm
public import GGOS.Work.T71State
public import GGOS.Work.T71Invariance
public import GGOS.Work.T71Estimate
public import GGOS.Work.T71Time

/-!
# Provider for `GGOS.limit_functional`

The proof of the theorem in `GGOS/Frozen/LimitFunctional.lean`,
as `GGOS.Providers.limit_functional`,
stated with exactly the theorem's type; the theorem is `by exact` of it.
-/

public section

open MeasureTheory Filter Topology

namespace GGOS.Providers

/-- [GG-OS] Theorem 7.1: Proposition 6.1 (`GGOS.passage_to_limit`) with the seminorm of
Definition 4.1; its premises hold for limit points of the torus states. -/
theorem limit_functional :
    ∀ (sc : Scale) (N0 : ℕ) (gd : DensityFn) (c : ℕ → Coeffs) (ω : ℕ → (Cfg ℤ → ℂ) → ℂ)
      (hω : ∀ N, N0 ≤ N → IsLimitPoint (c N) (ω N)),
    ∃ (Nm : ℕ → ℕ) (S : Alg →ₗ[ℂ] ℂ),
      StrictMono Nm ∧ (∀ m, N0 ≤ Nm m) ∧
      (∀ a : Alg, Tendsto (fun m => ω (Nm m) (iota sc (Nm m) gd a)) atTop (𝓝 (S a))) ∧
      (∀ (t : ℝ) (a : Alg), S (tauA t a) = S a) ∧
      (∀ a ∈ Aplus, ∀ b ∈ Aplus,
        ContinuousOn (fun t : ℝ => S (ThetaA a * tauA t b)) (Set.Ici 0)) ∧
      (∀ v : E3, v 2 = 0 → ∀ a : Alg, S (translA v a) = S a) ∧
      (∀ (m : ℕ) (z : Site ℤ) (g : LatSym ℝ),
        g.act (sitePos (eps sc (Nm m)) z) = sitePos (eps sc (Nm m)) z →
          ∀ a : Alg, S (pushA g a) = S a) ∧
      ∀ a : Alg, ‖S a‖ ≤ Mnorm a := by
  intro sc N0 gd c ω hω
  have hpn := GGOS.pairNorm_finite_seminorm_admissible sc N0 gd
  have hinv : ∀ N, N0 ≤ N → LatticeInvariant (ω N) := fun N hN =>
    GGOS.Work.latticeInvariant_of_isLimitPoint (c N) (ω N) (hω N hN)
  have hstate : ∀ N, N0 ≤ N → IsState (c N).ρ0 (ω N) := fun N hN =>
    GGOS.Work.isState_of_isLimitPoint (c N) (ω N) (hω N hN)
  exact GGOS.passage_to_limit sc N0 gd (fun N => (c N).ρ0) ω (pairNorm sc N0 gd)
    (fun N _ => (c N).ρ0_pos) hstate hinv
    (fun N hN a k => GGOS.Work.time_of_latticeInvariant sc N gd _ (ω N) (hstate N hN) (hinv N hN) a k)
    hpn.2.2.1 hpn.2.2.2
    (fun N hN σ => GGOS.Work.trunc_le_pairNorm_of_isLimitPoint sc N0 gd (c N) (ω N) N hN (hω N hN) σ)

end GGOS.Providers

end

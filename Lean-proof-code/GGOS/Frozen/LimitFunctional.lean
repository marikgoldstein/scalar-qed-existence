module

public import Mathlib
public import GGOS.Frozen.Defs.Aplus
public import GGOS.Frozen.Defs.Eps
public import GGOS.Frozen.Defs.Iota
public import GGOS.Frozen.Defs.IsLimitPoint
public import GGOS.Frozen.Defs.LatSymAct
public import GGOS.Frozen.Defs.Mnorm
public import GGOS.Frozen.Defs.SitePos
public import GGOS.Frozen.Defs.TauA
public import GGOS.Frozen.Defs.ThetaA
public import GGOS.Frozen.Defs.TranslA
public import GGOS.Infra.Alg
public import GGOS.Infra.Ambient
public import GGOS.Infra.Cells
public import GGOS.Infra.Coeffs
public import GGOS.Infra.DensityFn
public import GGOS.Infra.LatSym
public import GGOS.Infra.Motion
public import GGOS.Infra.Scale
public import GGOS.Infra.Site
public import GGOS.Providers.LimitFunctional

/-!
# [GG-OS] Theorem 7.1
-/

public section

open MeasureTheory Filter Topology

namespace GGOS

/-- [GG-OS] Theorem 7.1 (the limit functional), for limit points of the torus states
(Definition 2.3). -/
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
      ∀ a : Alg, ‖S a‖ ≤ Mnorm a :=
  by exact GGOS.Providers.limit_functional

end GGOS

end

module

public import Mathlib
public import GGOS.Frozen.Defs.Admissible
public import GGOS.Frozen.Defs.Aplus
public import GGOS.Frozen.Defs.Eps
public import GGOS.Frozen.Defs.Iota
public import GGOS.Frozen.Defs.LatSymAct
public import GGOS.Frozen.Defs.LatticeInvariant
public import GGOS.Frozen.Defs.Mnorm
public import GGOS.Frozen.Defs.Phi
public import GGOS.Frozen.Defs.SitePos
public import GGOS.Frozen.Defs.TauA
public import GGOS.Frozen.Defs.ThetaA
public import GGOS.Frozen.Defs.TranslA
public import GGOS.Infra.Alg
public import GGOS.Infra.Ambient
public import GGOS.Infra.Cells
public import GGOS.Infra.DensityFn
public import GGOS.Infra.IsSeminorm
public import GGOS.Infra.IsState
public import GGOS.Infra.LatSym
public import GGOS.Infra.Motion
public import GGOS.Infra.Scale
public import GGOS.Infra.Site
public import GGOS.Infra.T
public import GGOS.Providers.PassageToLimit

/-!
# [GG-OS] Proposition 6.1
-/

public section

open MeasureTheory Filter Topology

namespace GGOS

/-- [GG-OS] Proposition 6.1 (the passage to the limit), with the estimate in the truncated form
of Remark 6.2 (i). The cubic group about a point is the group of the motions `g` of `GGOS.LatSym ℝ`
that fix it. -/
theorem passage_to_limit :
    ∀ (sc : Scale) (N0 : ℕ) (gd : DensityFn) (ρ0 : ℕ → ℝ) (ω : ℕ → (Cfg ℤ → ℂ) → ℂ) (p : T → ℝ)
      (hρ0 : ∀ N, N0 ≤ N → 0 < ρ0 N) (hstate : ∀ N, N0 ≤ N → IsState (ρ0 N) (ω N))
      (hinv : ∀ N, N0 ≤ N → LatticeInvariant (ω N)) (htime : ∀ N, N0 ≤ N → ∀ (a : Alg) (k : ℤ),
        ω N (iota sc N gd (tauA (eps sc N * k) a)) = ω N (iota sc N gd a))
      (hp : IsSeminorm p) (hp_adm : Admissible p) (hest : ∀ N, N0 ≤ N → ∀ σ : T,
        (ω N fun x => ((min |Phi sc N gd σ x| 2 : ℝ) : ℂ)).re ≤ p σ),
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
  by exact GGOS.Providers.passage_to_limit

end GGOS

end

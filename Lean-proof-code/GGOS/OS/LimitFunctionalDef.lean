module

public import Mathlib
public import GGOS.Frozen.Defs.Iota
public import GGOS.Infra.Alg
public import GGOS.Infra.Cells
public import GGOS.Infra.DensityFn
public import GGOS.Infra.Scale

/-!
# Limit functionals
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace GGOS

/-- `S` is the limit functional of the states `ω_N`, `N ≥ N_0`, along the levels `N_m`:
`S(a) = lim_m ω_{N_m}(ι_{N_m}(a))` for every `a ∈ 𝒜` ([GG-OS] Theorem 7.1 (a)). -/
structure IsLimitFunctional (sc : Scale) (N0 : ℕ) (gd : DensityFn) (ω : ℕ → (Cfg ℤ → ℂ) → ℂ)
    (Nm : ℕ → ℕ) (S : Alg →ₗ[ℂ] ℂ) : Prop where
  strictMono : StrictMono Nm
  le : ∀ m, N0 ≤ Nm m
  tendsto : ∀ a : Alg, Tendsto (fun m => ω (Nm m) (iota sc (Nm m) gd a)) atTop (𝓝 (S a))

end GGOS

end

end

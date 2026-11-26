module

public import GGOS.Frozen.Defs.IsLimitPoint
public import GGOS.Frozen.Defs.LatticeInvariant
public import GGOS.OS.Work.DenseRP
public import GGOS.OS.Work.TorusRP
public import GGOS.Work.T71Invariance
public import GGOS.Work.T71LocalMarginals
public import GGOS.Work.T71PeriodicPull

/-!
# Reflection positivity of the limit points ([GG-OS] Corollary 9.8, `c = 0`)
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ComplexOrder ENNReal

namespace GGOS.OS

/-- A function of finitely many variables of the closed half space `{x_3 ≥ 0}`. -/
def DependsUp (P : Finset (Plaq ℤ)) (X : Finset (Site ℤ)) (F : Cfg ℤ → ℂ) : Prop :=
  (∀ p ∈ P, 0 ≤ p.1 2) ∧ (∀ x ∈ X, 0 ≤ x 2) ∧
    ∀ ω ω' : Cfg ℤ, (∀ p ∈ P, ω.1 p = ω'.1 p) → (∀ x ∈ X, ω.2 x = ω'.2 x) → F ω = F ω'

theorem timeRefl_torus (n : ℕ) : Work.torusLatSym n (timeRefl ℤ) = timeRefl (ZMod n) := by
  have h : castSite n (0 : Site ℤ) = 0 := by
    funext i
    simp [castSite]
  change (⟨_, _, castSite n 0⟩ : LatSym (ZMod n)) = ⟨_, _, 0⟩
  rw [h]
  rfl

theorem castSite_up {n : ℕ} [NeZero n] {x : Site ℤ} (hx : 0 ≤ x 2) {δ M : ℕ} (hδ : δ ≤ 1)
    (hM : x 2 + 1 ≤ M) (hn : M ≤ n / 2) : up δ (castSite n x) := by
  unfold up castSite
  have h : ((((x 2 : ℤ) : ZMod n)).val : ℤ) = x 2 % n := ZMod.val_intCast _
  have hlt : x 2 < n := by omega
  rw [Int.emod_eq_of_lt hx hlt] at h
  omega

/-- The bound on the time coordinates of finitely many cells. -/
theorem exists_height (P : Finset (Plaq ℤ)) (X : Finset (Site ℤ)) :
    ∃ M : ℕ, (∀ p ∈ P, p.1 2 + 1 ≤ M) ∧ ∀ x ∈ X, x 2 + 1 ≤ M := by
  refine ⟨(∑ p ∈ P, (p.1 2).natAbs) + (∑ x ∈ X, (x 2).natAbs) + 1, fun p hp => ?_, fun x hx => ?_⟩
  · have h := Finset.single_le_sum (f := fun p : Plaq ℤ => (p.1 2).natAbs)
      (fun _ _ => Nat.zero_le _) hp
    omega
  · have h := Finset.single_le_sum (f := fun x : Site ℤ => (x 2).natAbs)
      (fun _ _ => Nat.zero_le _) hx
    omega

theorem measurable_per (n : ℕ) : Measurable (per n) := by
  unfold per
  fun_prop

/-- Reflection positivity on the large tori, for a fixed local function of the half space. -/
theorem torus_rp_local (c : Coeffs) {P : Finset (Plaq ℤ)} {X : Finset (Site ℤ)} {F : Cfg ℤ → ℂ}
    (hF : Measurable F) (hup : DependsUp P X F) :
    ∃ k : ℕ, ∀ s : Side, k ≤ s.n →
      0 ≤ ∫ ω, starRingEnd ℂ (F (pull (timeRefl ℤ) (per s.n ω))) * F (per s.n ω)
        ∂(torusState s c) := by
  obtain ⟨M, hP, hX⟩ := exists_height P X
  refine ⟨2 * M, fun s hs => ?_⟩
  have hn : M ≤ s.n / 2 := by omega
  have h := torus_rp s c (fun ω => F (per s.n ω)) (hF.comp (measurable_per s.n))
    (fun ω ω' h1 h2 => hup.2.2 _ _
      (fun p hp => h1 (castSite s.n p.1, p.2) (castSite_up (hup.1 p hp) (pExt_le p.2) (hP p hp) hn))
      fun x hx => h2 (castSite s.n x) (castSite_up (hup.2.1 x hx) (Nat.zero_le 1) (hX x hx) hn))
  simpa only [← timeRefl_torus, Work.per_pull] using h

/-- A probability measure that represents a limit point of the torus states is lattice invariant. -/
theorem map_pull_eq {ω : (Cfg ℤ → ℂ) → ℂ} (hi : LatticeInvariant ω) {μ : Measure (Cfg ℤ)}
    [IsProbabilityMeasure μ] (hμ : ∀ F, IsBBL F → ω F = ∫ x, F x ∂μ) (g : LatSym ℤ) :
    μ.map (pull g) = μ := by
  have hg := TorusSymmetry.measurable_pull g
  have : IsProbabilityMeasure (μ.map (pull g)) := Measure.isProbabilityMeasure_map hg.aemeasurable
  refine Work.measure_eq_of_integral_local_eq fun A hloc hc hb => ?_
  have hA : IsBBL A := ⟨hc.measurable, hb, hloc⟩
  obtain ⟨C, hC⟩ := hb
  have hA' : IsBBL (A ∘ pull g) :=
    ⟨hc.measurable.comp hg, ⟨C, fun x => hC _⟩, Work.isLocal_comp_pull hloc g⟩
  rw [integral_map hg.aemeasurable hc.aestronglyMeasurable, ← hμ A hA]
  exact (hμ _ hA').symm.trans (hi g A hA)

/-- The data of a limit point: the measure represents the state, and the torus expectations of
bounded continuous local functions converge to it along a sequence of sides. -/
structure Represents (c : Coeffs) (ω : (Cfg ℤ → ℂ) → ℂ) (μ : Measure (Cfg ℤ)) : Prop where
  prob : IsProbabilityMeasure μ
  eq : ∀ F : Cfg ℤ → ℂ, IsBBL F → ω F = ∫ x, F x ∂μ
  lim : ∃ L : ℕ → Side, Tendsto (fun n => (L n).n) atTop atTop ∧
    ∀ F : Cfg ℤ → ℂ, IsLocal F → Continuous F → (∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) →
      Tendsto (fun n => ∫ x, F (per (L n).n x) ∂(torusState (L n) c)) atTop (𝓝 (∫ x, F x ∂μ))

/-- Any probability measure that represents the state of a limit point carries its data. -/
theorem represents {c : Coeffs} {ω : (Cfg ℤ → ℂ) → ℂ} (h : IsLimitPoint c ω)
    {μ : Measure (Cfg ℤ)} (hp : IsProbabilityMeasure μ)
    (hμ : ∀ F, IsBBL F → ω F = ∫ x, F x ∂μ) : Represents c ω μ := by
  obtain ⟨L, ν, hL, hν, _, hlim, hω⟩ := h
  refine ⟨hp, hμ, L, hL, fun F hloc hc hb => ?_⟩
  rw [← hμ F ⟨hc.measurable, hb, hloc⟩, hω F ⟨hc.measurable, hb, hloc⟩]
  exact hlim F hloc hc hb

theorem exists_represents {c : Coeffs} {ω : (Cfg ℤ → ℂ) → ℂ} (h : IsLimitPoint c ω) :
    ∃ μ, Represents c ω μ := by
  obtain ⟨L, ν, hL, hν, _, hlim, hω⟩ := h
  exact ⟨ν, hν, hω, L, hL, hlim⟩

theorem isLocal_conj_mul {F : Cfg ℤ → ℂ} (hF : IsLocal F) (g : LatSym ℤ) :
    IsLocal fun x => starRingEnd ℂ (F (pull g x)) * F x := by
  classical
  obtain ⟨P, X, h⟩ := hF
  obtain ⟨P', X', h'⟩ := Work.isLocal_comp_pull (F := F) ⟨P, X, h⟩ g
  refine ⟨P ∪ P', X ∪ X', fun w w' hp hx => ?_⟩
  have h1 := h w w' (fun p hP => hp p (Finset.mem_union_left _ hP))
    fun x hX => hx x (Finset.mem_union_left _ hX)
  have h2 := h' w w' (fun p hP => hp p (Finset.mem_union_right _ hP))
    fun x hX => hx x (Finset.mem_union_right _ hX)
  simp only [Function.comp_apply] at h2
  simp only [h1, h2]

/-- Reflection positivity on the bounded continuous local functions of the half space. -/
theorem rp_continuous {c : Coeffs} {ω : (Cfg ℤ → ℂ) → ℂ} {μ : Measure (Cfg ℤ)}
    (h : Represents c ω μ) {P : Finset (Plaq ℤ)} {X : Finset (Site ℤ)} {F : Cfg ℤ → ℂ}
    (hc : Continuous F) (hb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) (hup : DependsUp P X F) :
    0 ≤ ∫ x, starRingEnd ℂ (F (pull (timeRefl ℤ) x)) * F x ∂μ := by
  obtain ⟨L, hL, hlim⟩ := h.lim
  obtain ⟨C, hC⟩ := hb
  obtain ⟨k, hk⟩ := torus_rp_local c hc.measurable hup
  have hlim' := hlim (fun x => starRingEnd ℂ (F (pull (timeRefl ℤ) x)) * F x)
    (isLocal_conj_mul ⟨P, X, hup.2.2⟩ _)
    ((Complex.continuous_conj.comp (hc.comp (Work.continuous_pull _))).mul hc)
    ⟨C * C, fun x => by
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul (hC _) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hC x))⟩
  refine ge_of_tendsto hlim' ?_
  filter_upwards [hL.eventually (eventually_ge_atTop k)] with n hn
  exact hk (L n) hn

/-- The marginal on finitely many variables. -/
def marg (P : Finset (Plaq ℤ)) (X : Finset (Site ℤ)) (x : Cfg ℤ) : (P → ℝ) × (X → ℝ) :=
  (fun p => x.1 p.1, fun z => x.2 z.1)

open Classical in
/-- The extension of finitely many variables by zero. -/
noncomputable def extCfg (P : Finset (Plaq ℤ)) (X : Finset (Site ℤ)) (y : (P → ℝ) × (X → ℝ)) :
    Cfg ℤ :=
  (fun p => if h : p ∈ P then y.1 ⟨p, h⟩ else 0, fun z => if h : z ∈ X then y.2 ⟨z, h⟩ else 0)

theorem continuous_marg (P : Finset (Plaq ℤ)) (X : Finset (Site ℤ)) : Continuous (marg P X) := by
  unfold marg
  fun_prop

theorem continuous_extCfg (P : Finset (Plaq ℤ)) (X : Finset (Site ℤ)) :
    Continuous (extCfg P X) := by
  refine Continuous.prodMk (continuous_pi fun p => ?_) (continuous_pi fun z => ?_)
  · by_cases h : p ∈ P
    · simp only [h, dite_true]
      fun_prop
    · simp only [h, dite_false]
      fun_prop
  · by_cases h : z ∈ X
    · simp only [h, dite_true]
      fun_prop
    · simp only [h, dite_false]
      fun_prop

theorem ext_marg {P : Finset (Plaq ℤ)} {X : Finset (Site ℤ)} {F : Cfg ℤ → ℂ}
    (hup : DependsUp P X F) (x : Cfg ℤ) : F (extCfg P X (marg P X x)) = F x := by
  refine hup.2.2 _ _ (fun p hp => ?_) fun z hz => ?_
  · simp [extCfg, marg, hp]
  · simp [extCfg, marg, hz]

/-- **Reflection positivity of a limit point** ([GG-OS] Corollary 9.8, `c = 0`, in the `L²` form of
Theorem 9.7). -/
theorem rp_state {c : Coeffs} {ω : (Cfg ℤ → ℂ) → ℂ} (hω : IsLimitPoint c ω) {μ : Measure (Cfg ℤ)}
    (h : Represents c ω μ) {P : Finset (Plaq ℤ)} {X : Finset (Site ℤ)} {F : Cfg ℤ → ℂ}
    (hF : Measurable F) (hF2 : MemLp F 2 μ) (hup : DependsUp P X F) :
    0 ≤ ∫ x, starRingEnd ℂ (F (pull (timeRefl ℤ) x)) * F x ∂μ := by
  have hprob := h.prob
  have hinv := map_pull_eq (Work.latticeInvariant_of_isLimitPoint c ω hω) h.eq (timeRefl ℤ)
  let π := marg P X
  have hπ : Continuous π := continuous_marg P X
  let R : Cfg ℤ → Cfg ℤ := pull (timeRefl ℤ)
  have hR : Measurable R := TorusSymmetry.measurable_pull _
  have hRc : Continuous R := Work.continuous_pull _
  let ν := μ.map π
  have hνp : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hπ.measurable.aemeasurable
  have hp : MeasurePreserving π μ ν := ⟨hπ.measurable, rfl⟩
  have hq : MeasurePreserving (π ∘ R) μ ν := by
    refine ⟨hπ.measurable.comp hR, ?_⟩
    rw [← Measure.map_map hπ.measurable hR]
    change Measure.map π (Measure.map (pull (timeRefl ℤ)) μ) = ν
    rw [hinv]
  let f : (P → ℝ) × (X → ℝ) → ℂ := fun y => F (extCfg P X y)
  have hfF (x : Cfg ℤ) : f (π x) = F x := ext_marg hup x
  have hf : Measurable f := hF.comp (continuous_extCfg P X).measurable
  have hf2 : MemLp f 2 ν := by
    refine (memLp_map_measure_iff hf.aestronglyMeasurable hπ.measurable.aemeasurable).mpr ?_
    exact hF2.congr_norm (hf.comp hπ.measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simp only [Function.comp_apply, hfF])
  have hmain := nonneg_of_continuous hp hq (fun g => ?_) hf2
  · simpa only [Function.comp_apply, hfF] using hmain
  · have hg := rp_continuous h (F := fun x => g (π x)) (g.continuous.comp hπ)
      ⟨‖g‖, fun x => g.norm_coe_le_norm _⟩ (P := P) (X := X)
      ⟨hup.1, hup.2.1, fun w w' h1 h2 => congrArg g (Prod.ext (funext fun p => h1 p.1 p.2)
        (funext fun z => h2 z.1 z.2))⟩
    exact hg

end GGOS.OS

end

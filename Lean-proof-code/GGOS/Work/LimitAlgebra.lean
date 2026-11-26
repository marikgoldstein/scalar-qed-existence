module

public import GGOS.Frozen.Defs.Iota
public import GGOS.Frozen.Defs.Mnorm
public import GGOS.Frozen.Defs.TranslA
public import GGOS.Infra.Motion
public import GGOS.Work.LimitObservables
public import GGOS.Work.LimitTests

/-! Linear extension of the basis limit and continuity of finite mixed products. -/

public section

open Filter Topology

namespace GGOS.Work.Limit

/-- Evaluation of the finite coefficient expansion against the basis limits. -/
noncomputable def linearExtension (Z : T → ℂ) : Alg →ₗ[ℂ] ℂ :=
  (Finsupp.linearCombination ℂ Z).comp (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

private theorem extension_single (Z : T → ℂ) (s : T) (c : ℂ) :
    linearExtension Z (AddMonoidAlgebra.single s c) = c * Z s :=
  Finsupp.linearCombination_single ℂ c s

private theorem state_sum {ρ : ℝ} {ω : (Cfg ℤ → ℂ) → ℂ} (hs : IsState ρ ω)
    {ι : Type*} (s : Finset ι) (f : ι → Cfg ℤ → ℂ) (hf : ∀ i, IsBBL (f i)) :
    IsBBL (∑ i ∈ s, f i) ∧ ω (∑ i ∈ s, f i) = ∑ i ∈ s, ω (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨bbl_const 0, state_const hs 0⟩
  | @insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hs.map_add _ _ (hf i) ih.1, ih.2]
    exact ⟨bbl_add (hf i) ih.1, rfl⟩

private theorem state_iota (sc : Scale) (N : ℕ) (gd : DensityFn)
    {ρ : ℝ} {ω : (Cfg ℤ → ℂ) → ℂ} (hs : IsState ρ ω) (a : Alg) :
    ω (iota sc N gd a) = ∑ s ∈ a.coeff.support, a.coeff s * ω (expPhi sc N gd s) := by
  let f (s : T) := a.coeff s • expPhi sc N gd s
  change ω (∑ s ∈ a.coeff.support, f s) = _
  rw [(state_sum hs _ f (fun s => bbl_smul _ (bbl_exp sc N gd s))).2]
  exact Finset.sum_congr rfl (fun s _ => hs.map_smul _ _ (bbl_exp sc N gd s))

theorem tendsto_iota (sc : Scale) (gd : DensityFn) {ρ : ℕ → ℝ} {ω : ℕ → (Cfg ℤ → ℂ) → ℂ}
    {Nm : ℕ → ℕ} (hs : ∀ m, IsState (ρ (Nm m)) (ω (Nm m))) {Z : T → ℂ}
    (hZ : ∀ s, Tendsto (fun m => ω (Nm m) (expPhi sc (Nm m) gd s)) atTop (𝓝 (Z s))) (a : Alg) :
    Tendsto (fun m => ω (Nm m) (iota sc (Nm m) gd a)) atTop (𝓝 (linearExtension Z a)) := by
  simp only [state_iota sc _ gd (hs _) a]
  exact tendsto_finsetSum a.coeff.support (fun s _ => tendsto_const_nhds.mul (hZ s))

theorem norm_extension_le {Z : T → ℂ} (hb : ∀ s, ‖Z s‖ ≤ 1) (a : Alg) :
    ‖linearExtension Z a‖ ≤ Mnorm a := by
  change ‖∑ s ∈ a.coeff.support, a.coeff s * Z s‖ ≤ ∑ s ∈ a.coeff.support, ‖a.coeff s‖
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun s _ => ?_))
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hb s)

private theorem transl_add (v : E3) (x y : Alg) : translA v (x + y) = translA v x + translA v y :=
  AddMonoidAlgebra.mapDomain_add _ _ _

private theorem transl_smul (v : E3) (r : ℂ) (x : Alg) : translA v (r • x) = r • translA v x :=
  (AddMonoidAlgebra.mapDomainLinearMap ℂ ℂ (transl v)).map_smul r x

theorem extension_transl {Z : T → ℂ} (v : E3) (hi : ∀ s, Z (transl v s) = Z s) (a : Alg) :
    linearExtension Z (translA v a) = linearExtension Z a := by
  induction a using AddMonoidAlgebra.induction_on with
  | of s =>
    change linearExtension Z (AddMonoidAlgebra.mapDomain (transl v) (.single s 1)) =
      linearExtension Z (.single s 1)
    rw [AddMonoidAlgebra.mapDomain_single, extension_single, extension_single, hi]
  | add x y hx hy =>
    rw [transl_add, map_add, map_add, hx, hy]
  | smul r x hx =>
    rw [transl_smul, map_smul, map_smul, hx]

private theorem push_add (g : LatSym ℝ) (x y : Alg) : pushA g (x + y) = pushA g x + pushA g y :=
  AddMonoidAlgebra.mapDomain_add _ _ _

private theorem push_smul (g : LatSym ℝ) (r : ℂ) (x : Alg) : pushA g (r • x) = r • pushA g x :=
  (AddMonoidAlgebra.mapDomainLinearMap ℂ ℂ (pushT g)).map_smul r x

theorem extension_push {Z : T → ℂ} (g : LatSym ℝ) (hi : ∀ s, Z (pushT g s) = Z s) (a : Alg) :
    linearExtension Z (pushA g a) = linearExtension Z a := by
  induction a using AddMonoidAlgebra.induction_on with
  | of s =>
    change linearExtension Z (AddMonoidAlgebra.mapDomain (pushT g) (.single s 1)) =
      linearExtension Z (.single s 1)
    rw [AddMonoidAlgebra.mapDomain_single, extension_single, extension_single, hi]
  | add x y hx hy =>
    rw [push_add, map_add, map_add, hx, hy]
  | smul r x hx =>
    rw [push_smul, map_smul, map_smul, hx]

private theorem continuous_basis_transl {Z : T → ℂ} {p : T → ℝ} (hp : Admissible p)
    (hmod : ∀ s t, ‖Z s - Z t‖ ≤ p (s - t)) (s t : T) :
    Continuous (fun v => Z (s + transl v t)) := by
  apply SeqContinuous.continuous
  intro u v hu
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun n => dist_nonneg) _ (hp _ _ (convTest_transl hu t))
  intro n
  simpa only [Function.comp_apply, dist_eq_norm, add_sub_add_left_eq_sub] using hmod (s + transl (u n) t) (s + transl v t)

/-- Continuity holds on the whole translation group with an arbitrary fixed left factor. -/
theorem continuous_mixed {Z : T → ℂ} {p : T → ℝ} (hp : Admissible p)
    (hmod : ∀ s t, ‖Z s - Z t‖ ≤ p (s - t)) (a b : Alg) :
    Continuous (fun v : E3 => linearExtension Z (a * translA v b)) := by
  induction a using AddMonoidAlgebra.induction_on with
  | of s =>
    induction b using AddMonoidAlgebra.induction_on with
    | of t =>
      change Continuous (fun v => linearExtension Z (.single s 1 *
        AddMonoidAlgebra.mapDomain (transl v) (.single t 1)))
      simpa only [AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.single_mul_single,
        extension_single, one_mul] using continuous_basis_transl hp hmod s t
    | add x y hx hy =>
      simpa only [transl_add, mul_add, map_add, Pi.add_def] using hx.add hy
    | smul r x hx =>
      simpa only [transl_smul, mul_smul_comm, map_smul, Pi.smul_def'] using
        (continuous_const (y := r)).smul hx
  | add x y hx hy =>
    simpa only [add_mul, map_add, Pi.add_def] using hx.add hy
  | smul r x hx =>
    simpa only [smul_mul_assoc, map_smul, Pi.smul_def'] using (continuous_const (y := r)).smul hx

end GGOS.Work.Limit

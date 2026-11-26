module

public import Mathlib

/-!
# Reflection positivity of a product measure

A finite product of measures on `ℝ`, indexed by a set with an involution that exchanges the two
halves, fixes the common part pointwise and acts on each coordinate by a sign.  A function of the
coordinates of one closed half pairs non-negatively with its reflection.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexOrder

namespace GGOS.OS

/-- A reflection of the index set of a product measure. -/
structure IndexRefl {K : Type*} (ν : K → Measure ℝ) where
  /-- the involution of the indices -/
  r : K → K
  invol : ∀ k, r (r k) = k
  /-- the sign attached to each coordinate -/
  sgn : K → ℝ
  sgn_mul : ∀ k, sgn k * sgn (r k) = 1
  mp : ∀ k, MeasurePreserving (fun x => sgn k * x) (ν (r k)) (ν k)
  /-- the closed upper half -/
  U : K → Prop
  cover : ∀ k, U k ∨ U (r k)
  plane : ∀ k, U k → U (r k) → r k = k ∧ sgn k = 1

namespace IndexRefl

variable {K : Type*} [Fintype K] {ν : K → Measure ℝ} (R : IndexRefl ν)

/-- The action on configurations. -/
def act (x : K → ℝ) : K → ℝ := fun k => R.sgn k * x (R.r k)

omit [Fintype K] in
theorem measurable_act : Measurable R.act := by
  refine measurable_pi_iff.mpr fun k => ?_
  unfold act
  fun_prop

/-- Indices of the plane. -/
abbrev K0 := {k : K // R.U k ∧ R.U (R.r k)}

/-- Indices of the open upper half. -/
abbrev K1 := {k : K // R.U k ∧ ¬ R.U (R.r k)}

/-- The indices as plane, upper half, and reflected upper half. -/
def idx : R.K0 ⊕ (R.K1 ⊕ R.K1) → K
  | .inl k => k.1
  | .inr (.inl k) => k.1
  | .inr (.inr k) => R.r k.1

omit [Fintype K] in
theorem idx_bijective : Function.Bijective R.idx := by
  constructor
  · rintro (⟨a, ha⟩ | ⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩ | ⟨b, hb⟩) h <;>
      simp only [idx] at h
  -- the nine cases
    · subst h; rfl
    · subst h; exact absurd ha.2 hb.2
    · exact absurd (h ▸ ha.1) hb.2
    · subst h; exact absurd hb.2 ha.2
    · subst h; rfl
    · exact absurd (h ▸ ha.1) hb.2
    · exact absurd (h ▸ hb.1) ha.2
    · exact absurd (h ▸ hb.1) ha.2
    · have : a = b := by rw [← R.invol a, h, R.invol]
      subst this; rfl
  · intro k
    by_cases h : R.U k
    · by_cases h' : R.U (R.r k)
      · exact ⟨.inl ⟨k, h, h'⟩, rfl⟩
      · exact ⟨.inr (.inl ⟨k, h, h'⟩), rfl⟩
    · have hr := (R.cover k).resolve_left h
      refine ⟨.inr (.inr ⟨R.r k, hr, by rwa [R.invol]⟩), R.invol k⟩

open Classical in
/-- The configuration with given values on the plane, on the upper half, and (reflected) on the
lower half. -/
def glue (z : (R.K0 → ℝ) × ((R.K1 → ℝ) × (R.K1 → ℝ))) : K → ℝ := fun k =>
  if h : R.U k then
    if h' : R.U (R.r k) then z.1 ⟨k, h, h'⟩ else z.2.1 ⟨k, h, h'⟩
  else R.sgn k * z.2.2 ⟨R.r k, (R.cover k).resolve_left h, by rwa [R.invol]⟩

omit [Fintype K] in
theorem glue_plane (z) (k : R.K0) : R.glue z k.1 = z.1 k := by
  simp only [glue, dite_eq_left k.2.1, dite_eq_left k.2.2]

omit [Fintype K] in
theorem glue_up (z) (k : R.K1) : R.glue z k.1 = z.2.1 k := by
  simp only [glue, dite_eq_left k.2.1, dite_eq_right k.2.2]

omit [Fintype K] in
theorem glue_down (z) (k : R.K1) : R.glue z (R.r k.1) = R.sgn (R.r k.1) * z.2.2 k := by
  have h : (⟨R.r (R.r k.1), by rw [R.invol]; exact k.2⟩ : R.K1) = k := Subtype.ext (R.invol k.1)
  simp only [glue, dite_eq_right k.2.2]
  rw [h]

omit [Fintype K] in
theorem measurable_glue : Measurable R.glue := by
  classical
  refine measurable_pi_iff.mpr fun k => ?_
  by_cases h : R.U k
  · by_cases h' : R.U (R.r k)
    · have : (fun z => R.glue z k) = fun z => z.1 ⟨k, h, h'⟩ :=
        funext fun z => R.glue_plane z ⟨k, h, h'⟩
      rw [this]
      fun_prop
    · have : (fun z => R.glue z k) = fun z => z.2.1 ⟨k, h, h'⟩ :=
        funext fun z => R.glue_up z ⟨k, h, h'⟩
      rw [this]
      fun_prop
  · have hr := (R.cover k).resolve_left h
    have : (fun z => R.glue z k) = fun z => R.sgn k * z.2.2 ⟨R.r k, hr, by rwa [R.invol]⟩ := by
      funext z
      simp only [glue, dite_eq_right h]
    rw [this]
    fun_prop

variable [∀ k, SigmaFinite (ν k)]

/-- The product measure in the three groups of coordinates. -/
abbrev split : Measure ((R.K0 → ℝ) × ((R.K1 → ℝ) × (R.K1 → ℝ))) :=
  open Classical in
  (Measure.pi fun k : R.K0 => ν k.1).prod
    ((Measure.pi fun k : R.K1 => ν k.1).prod (Measure.pi fun k : R.K1 => ν k.1))

theorem map_glue : Measure.map R.glue R.split = Measure.pi ν := by
  classical
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply R.measurable_glue (MeasurableSet.univ_pi hs)]
  have hpre : R.glue ⁻¹' (Set.univ.pi s) = (Set.univ.pi fun k : R.K0 => s k.1) ×ˢ
      ((Set.univ.pi fun k : R.K1 => s k.1) ×ˢ
        (Set.univ.pi fun k : R.K1 => (fun x => R.sgn (R.r k.1) * x) ⁻¹' s (R.r k.1))) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      exact ⟨fun k => R.glue_plane z k ▸ h k.1, fun k => R.glue_up z k ▸ h k.1,
        fun k => R.glue_down z k ▸ h (R.r k.1)⟩
    · rintro ⟨h0, h1, h2⟩ k
      obtain ⟨i, rfl⟩ := R.idx_bijective.2 k
      rcases i with k | k | k
      · simp only [idx]; rw [R.glue_plane]; exact h0 k
      · simp only [idx]; rw [R.glue_up]; exact h1 k
      · simp only [idx]; rw [R.glue_down]; exact h2 k
  have hmp (k : R.K1) : ν k.1 ((fun x => R.sgn (R.r k.1) * x) ⁻¹' s (R.r k.1)) =
      ν (R.r k.1) (s (R.r k.1)) := by
    have h := R.mp (R.r k.1)
    rw [R.invol] at h
    exact h.measure_preimage (hs _).nullMeasurableSet
  rw [hpre, Measure.prod_prod, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, Measure.pi_pi]
  simp only [hmp]
  rw [← (Equiv.ofBijective R.idx R.idx_bijective).prod_comp fun k => ν k (s k),
    Fintype.prod_sum_type, Fintype.prod_sum_type]
  rfl

/-- **Reflection positivity of a product measure.** -/
theorem integral_nonneg (G : (K → ℝ) → ℂ) (hG : Measurable G)
    (hdep : ∀ x y, (∀ k, R.U k → x k = y k) → G x = G y) :
    0 ≤ ∫ x, starRingEnd ℂ (G (R.act x)) * G x ∂(Measure.pi ν) := by
  classical
  let g (a : R.K0 → ℝ) (b : R.K1 → ℝ) : ℂ := G (R.glue (a, (b, 0)))
  have h1 (z) : G (R.glue z) = g z.1 z.2.1 := by
    refine hdep _ _ fun k hk => ?_
    by_cases h' : R.U (R.r k)
    · rw [R.glue_plane z ⟨k, hk, h'⟩, R.glue_plane _ ⟨k, hk, h'⟩]
    · rw [R.glue_up z ⟨k, hk, h'⟩, R.glue_up _ ⟨k, hk, h'⟩]
  have h2 (z) : G (R.act (R.glue z)) = g z.1 z.2.2 := by
    refine hdep _ _ fun k hk => ?_
    by_cases h' : R.U (R.r k)
    · obtain ⟨hrk, hs⟩ := R.plane k hk h'
      have e : R.act (R.glue z) k = R.glue z k := by
        unfold act
        rw [congrArg (R.glue z) hrk, hs, one_mul]
      rw [e, R.glue_plane z ⟨k, hk, h'⟩, R.glue_plane _ ⟨k, hk, h'⟩]
    · rw [R.glue_up _ ⟨k, hk, h'⟩, act, R.glue_down z ⟨k, hk, h'⟩, ← mul_assoc, R.sgn_mul, one_mul]
  have hmeas : AEStronglyMeasurable (fun x => starRingEnd ℂ (G (R.act x)) * G x)
      (Measure.map R.glue R.split) :=
    ((Complex.continuous_conj.measurable.comp (hG.comp R.measurable_act)).mul
      hG).aestronglyMeasurable
  rw [← R.map_glue, integral_map R.measurable_glue.aemeasurable hmeas]
  simp only [h1, h2]
  by_cases hint : Integrable (fun z : (R.K0 → ℝ) × ((R.K1 → ℝ) × (R.K1 → ℝ)) =>
      starRingEnd ℂ (g z.1 z.2.2) * g z.1 z.2.1) R.split
  · rw [integral_prod _ hint]
    have hinner (a : R.K0 → ℝ) :
        (∫ p : (R.K1 → ℝ) × (R.K1 → ℝ), starRingEnd ℂ (g a p.2) * g a p.1
          ∂((Measure.pi fun k : R.K1 => ν k.1).prod (Measure.pi fun k : R.K1 => ν k.1))) =
        ((‖∫ b, g a b ∂(Measure.pi fun k : R.K1 => ν k.1)‖ ^ 2 : ℝ) : ℂ) := by
      have hc : (fun p : (R.K1 → ℝ) × (R.K1 → ℝ) => starRingEnd ℂ (g a p.2) * g a p.1) =
          fun p => g a p.1 * starRingEnd ℂ (g a p.2) := funext fun p => mul_comm _ _
      rw [hc, integral_prod_mul (fun b => g a b) (fun b => starRingEnd ℂ (g a b)), integral_conj,
        Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [hinner]
    rw [integral_complex_ofReal]
    exact Complex.zero_le_real.mpr (MeasureTheory.integral_nonneg fun a => by positivity)
  · rw [integral_undef hint]

end IndexRefl

end GGOS.OS

end

end

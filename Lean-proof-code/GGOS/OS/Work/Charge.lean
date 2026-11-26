module

public import GGOS.OS.Axioms
public import GGOS.OS.Work.Invariance
public import GGOS.OS.Work.Symmetry

/-!
# Charge conjugation ([GG-OS] Proposition 9.12 (b))
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace GGOS.OS

/-- Charge conjugation of a configuration, `(𝔣, ρ̃) ↦ (-𝔣, ρ̃)`. -/
def chargeCfg {R : Type*} [CommRing R] (ω : Cfg R) : Cfg R := (fun p => -ω.1 p, ω.2)

theorem measurable_chargeCfg {R : Type*} [CommRing R] : Measurable (chargeCfg (R := R)) := by
  unfold chargeCfg
  fun_prop

theorem continuous_chargeCfg {R : Type*} [CommRing R] : Continuous (chargeCfg (R := R)) := by
  unfold chargeCfg
  fun_prop

/-- The signs of charge conjugation on the cells. -/
def cSign {n : ℕ} : Cell n → ℝ := Sum.elim (fun _ => 1) fun _ => -1

/-- Charge conjugation of the cell variables. -/
def chargeCell {n : ℕ} (x : Cell n → ℝ) : Cell n → ℝ := fun k => cSign k * x k

variable (s : Side) (c : Coeffs)

theorem measurePreserving_chargeCell :
    MeasurePreserving chargeCell (Measure.pi (cellMeasure c (n := s.n)))
      (Measure.pi (cellMeasure c (n := s.n))) := by
  refine measurePreserving_pi (cellMeasure c (n := s.n)) (cellMeasure c (n := s.n))
    (f := fun k r => cSign k * r) fun k => ?_
  rcases k with k | k | k
  · simp only [cSign, Sum.elim_inl, one_mul]
    exact MeasurePreserving.id _
  · exact measurePreserving_sign_Ioc (Real.pi / c.γ) (Or.inr rfl)
  · exact measurePreserving_sign_int (Or.inr rfl)

variable {s}

theorem hop_neg (r r' θ : ℝ) : hop c r r' (-θ) = hop c r r' θ := by
  have h : ‖Complex.exp (Complex.I * ((c.γ * -θ : ℝ) : ℂ)) * ((c.ρ0 + r' : ℝ) : ℂ)
      - ((c.ρ0 + r : ℝ) : ℂ)‖ = ‖Complex.exp (Complex.I * ((c.γ * θ : ℝ) : ℂ)) *
      ((c.ρ0 + r' : ℝ) : ℂ) - ((c.ρ0 + r : ℝ) : ℂ)‖ := by
    rw [← RCLike.norm_conj (Complex.exp (Complex.I * ((c.γ * θ : ℝ) : ℂ)) *
      ((c.ρ0 + r' : ℝ) : ℂ) - ((c.ρ0 + r : ℝ) : ℂ))]
    congr 1
    rw [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 3
    simp
  unfold hop
  rw [h]

theorem curvCell_charge {n : ℕ} (x : Cell n → ℝ) (p : Plaq (ZMod n)) :
    curvCell c (chargeCell x) p = -curvCell c x p := by
  have hb (b : Bond (ZMod n)) : bondPart (chargeCell x) b = -bondPart x b := neg_one_mul _
  have hp (p : Plaq (ZMod n)) : plaqPart (chargeCell x) p = -plaqPart x p := neg_one_mul _
  unfold curvCell dBond
  simp only [hb, hp]
  ring

theorem cfgOf_charge {n : ℕ} (x : Cell n → ℝ) :
    cfgOf c (chargeCell x) = chargeCfg (cfgOf c x) := by
  refine Prod.ext (funext fun p => curvCell_charge c x p) (funext fun z => ?_)
  exact one_mul _

theorem closedCell_charge {n : ℕ} (x : Cell n → ℝ) (z : Site (ZMod n)) :
    closedCell (chargeCell x) z = closedCell x z := by
  have hp (p : Plaq (ZMod n)) : plaqPart (chargeCell x) p = -plaqPart x p := neg_one_mul _
  have h : dPlaqR (plaqPart (chargeCell x)) z = -dPlaqR (plaqPart x) z := by
    unfold dPlaqR
    simp only [hp]
    ring
  unfold closedCell
  rw [h]
  simp only [neg_eq_zero]

theorem cellWeight_charge (x : Cell s.n → ℝ) : cellWeight c (chargeCell x) = cellWeight c x := by
  have hs (z : Site (ZMod s.n)) : chargeCell x (.inl z) = x (.inl z) := one_mul _
  have hb (b : Bond (ZMod s.n)) : hopCell c (chargeCell x) b = hopCell c x b := by
    unfold hopCell
    have h1 : bondPart (chargeCell x) b = -bondPart x b := neg_one_mul _
    rw [hs, hs, h1, hop_neg]
  unfold cellWeight
  simp only [hs, hb, curvCell_charge, closedCell_charge, neg_sq]

variable (s)

theorem torus_charge (f : Cfg (ZMod s.n) → ℂ) (hf : Measurable f) :
    ∫ ω, f (chargeCfg ω) ∂(torusState s c) = ∫ ω, f ω ∂(torusState s c) := by
  rw [integral_torusState s c (fun ω => f (chargeCfg ω)) (hf.comp measurable_chargeCfg),
    integral_torusState s c f hf]
  congr 1
  have hmp := measurePreserving_chargeCell s c
  have hmeas : Measurable fun x : Cell s.n → ℝ => (cellWeight c x : ℂ) * f (cfgOf c x) :=
    (Complex.measurable_ofReal.comp (measurable_cellWeight c)).mul (hf.comp (measurable_cfgOf c))
  calc ∫ x, (cellWeight c x : ℂ) * f (chargeCfg (cfgOf c x)) ∂(Measure.pi (cellMeasure c (n := s.n)))
      = ∫ x, (cellWeight c (chargeCell x) : ℂ) * f (cfgOf c (chargeCell x))
          ∂(Measure.pi (cellMeasure c (n := s.n))) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [cellWeight_charge, cfgOf_charge]
    _ = ∫ x, (cellWeight c x : ℂ) * f (cfgOf c x)
          ∂(Measure.map chargeCell (Measure.pi (cellMeasure c (n := s.n)))) :=
        (integral_map hmp.measurable.aemeasurable hmeas.aestronglyMeasurable).symm
    _ = _ := by rw [hmp.map_eq]

theorem isLocal_comp_charge {F : Cfg ℤ → ℂ} (hF : IsLocal F) : IsLocal (F ∘ chargeCfg) := by
  obtain ⟨P, X, h⟩ := hF
  exact ⟨P, X, fun w w' hp hx => h _ _ (fun p hP => congrArg Neg.neg (hp p hP)) fun x hX => hx x hX⟩

variable {c}

theorem map_charge_eq {ω : (Cfg ℤ → ℂ) → ℂ} {μ : Measure (Cfg ℤ)} (h : Represents c ω μ) :
    μ.map chargeCfg = μ := by
  have hprob := h.prob
  obtain ⟨L, -, hlim⟩ := h.lim
  have hm : Measurable (chargeCfg (R := ℤ)) := measurable_chargeCfg
  have : IsProbabilityMeasure (μ.map chargeCfg) := Measure.isProbabilityMeasure_map hm.aemeasurable
  refine Work.measure_eq_of_integral_local_eq fun A hloc hc hb => ?_
  obtain ⟨C, hC⟩ := hb
  rw [integral_map hm.aemeasurable hc.aestronglyMeasurable]
  have h1 := hlim (A ∘ chargeCfg) (isLocal_comp_charge hloc) (hc.comp continuous_chargeCfg)
    ⟨C, fun x => hC _⟩
  refine tendsto_nhds_unique (h1.congr fun n => ?_) (hlim A hloc hc ⟨C, hC⟩)
  exact torus_charge (L n) c (fun ω => A (per (L n).n ω)) (hc.measurable.comp (measurable_per _))

theorem phi_charge (sc : Scale) (N : ℕ) (gd : DensityFn) (σ : T) (x : Cfg ℤ) :
    Phi sc N gd (chargeT σ) x = Phi sc N gd σ (chargeCfg x) := by
  unfold Phi
  congr 1
  congr 1
  refine tsum_congr fun p => ?_
  change -σ.1.1 _ _ _ * x.1 p = σ.1.1 _ _ _ * -x.1 p
  ring

theorem state_charge {ω : (Cfg ℤ → ℂ) → ℂ} {μ : Measure (Cfg ℤ)} (h : Represents c ω μ)
    (sc : Scale) (N : ℕ) (gd : DensityFn) (σ : T) :
    ω (expPhi sc N gd (chargeT σ)) = ω (expPhi sc N gd σ) := by
  have hb := Work.Limit.bbl_exp sc N gd σ
  rw [h.eq _ (Work.Limit.bbl_exp sc N gd _), h.eq _ hb]
  have he : expPhi sc N gd (chargeT σ) = fun x => expPhi sc N gd σ (chargeCfg x) := by
    funext x
    simp only [expPhi, phi_charge]
  rw [he]
  have hm : Measurable (chargeCfg (R := ℤ)) := measurable_chargeCfg
  calc ∫ x, expPhi sc N gd σ (chargeCfg x) ∂μ = ∫ x, expPhi sc N gd σ x ∂(μ.map chargeCfg) :=
        (integral_map hm.aemeasurable hb.measurable.aestronglyMeasurable).symm
    _ = ∫ x, expPhi sc N gd σ x ∂μ := by rw [map_charge_eq h]

/-- Charge conjugation as a linear map. -/
def chargeL : T →ₗ[ℝ] T where
  toFun := chargeT
  map_add' _ _ := T_ext (fun _ _ _ => neg_add _ _) fun _ => rfl
  map_smul' r σ := T_ext (fun μ ν x => (mul_neg r (σ.1.1 μ ν x)).symm) fun _ => rfl

theorem charge_sum_smul {ι : Type*} (s : Finset ι) (t : ι → ℝ) (σ : ι → T) :
    chargeT (∑ j ∈ s, t j • σ j) = ∑ j ∈ s, t j • chargeT (σ j) := by
  change chargeL _ = _
  rw [map_sum]
  simp only [map_smul]
  rfl

theorem chargeT_of_curv {σ : T} (h : σ.1.2 = 0) : chargeT σ = -σ := by
  refine T_ext (fun _ _ _ => rfl) fun x => ?_
  change σ.1.2 x = -σ.1.2 x
  rw [h]
  simp

variable {sc : Scale} {N0 : ℕ} {gd : DensityFn} {S : Alg →ₗ[ℂ] ℂ}
  {cc : ℕ → Coeffs} {ω : ℕ → (Cfg ℤ → ℂ) → ℂ} {Nm : ℕ → ℕ}

theorem basis_charge (hω : ∀ N, N0 ≤ N → IsLimitPoint (cc N) (ω N))
    (hS : IsLimitFunctional sc N0 gd ω Nm S) (σ : T) :
    S (basisE (chargeT σ)) = S (basisE σ) := by
  obtain ⟨μ, hμ⟩ := exists_representing hω
  refine tendsto_nhds_unique (tendsto_basis hS _) ((tendsto_basis hS σ).congr fun m => ?_)
  exact (state_charge (hμ _ (hS.le m)) sc (Nm m) gd σ).symm

theorem schwinger_neg (hω : ∀ N, N0 ≤ N → IsLimitPoint (cc N) (ω N))
    (hS : IsLimitFunctional sc N0 gd ω Nm S) {n : ℕ} (σ : Fin n → T) :
    schwinger S (fun i => -σ i) = (-1) ^ n * schwinger S σ := by
  obtain ⟨μ, hμ⟩ := exists_representing hω
  refine tendsto_nhds_unique (tendsto_schwinger hω hS hμ _) ?_
  refine ((tendsto_schwinger hω hS hμ σ).const_mul ((-1) ^ n)).congr fun l => ?_
  have h1 (x : Cfg ℤ) : ∏ i, Phi sc (Nm l) gd (-σ i) x =
      (-1) ^ n * ∏ i, Phi sc (Nm l) gd (σ i) x := by
    simp only [phi_neg]
    rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin]
  simp only [h1, integral_const_mul]
  push_cast
  ring

theorem schwinger_odd (hω : ∀ N, N0 ≤ N → IsLimitPoint (cc N) (ω N))
    (hS : IsLimitFunctional sc N0 gd ω Nm S) {n : ℕ} (hn : Odd n) (σ : Fin n → T)
    (hσ : ∀ i, (σ i).1.2 = 0) : schwinger S σ = 0 := by
  have hg : genFun S (fun i => chargeT (σ i)) = genFun S σ := by
    funext t
    unfold genFun
    rw [← charge_sum_smul, basis_charge hω hS]
  have h1 : schwinger S (fun i => chargeT (σ i)) = schwinger S σ := by
    unfold schwinger
    rw [hg]
  have h2 : (fun i => chargeT (σ i)) = fun i => -σ i := funext fun i => chargeT_of_curv (hσ i)
  rw [h2, schwinger_neg hω hS, hn.neg_one_pow, neg_one_mul] at h1
  exact self_eq_neg.mp h1.symm

end GGOS.OS

end

end

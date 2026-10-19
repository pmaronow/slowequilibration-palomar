-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalHessianMarginEvents
public import SlowEquilibration.SourcePhysicalPairHessianMarginProbability
public import SlowEquilibration.SourcePureOriginalIntensityEnvelope
public import SlowEquilibration.SourcePureAboveStaticCertificate
public import SlowEquilibration.SphericalTAPPureMarkedValueWeight
public import SlowEquilibration.SphericalTAPCriticalLightBandMark
public import SlowEquilibration.DeterminantHolder

/-! The determinant-weighted bad-Hessian first moment in manuscript
`lem:pc-hessian`, on a fixed normalized window around the original pure
ground energy. The posterior margin estimate and normalized determinant
moments give a Hölder bound; the pure complexity tangent then controls the
Kac--Rice integral on this window of linear physical width. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.PureHighEnergyBadHessianCount

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalMarkedWindows SphericalGaussianJet SphericalForm SphereHessian
open PairConditionalDeterminantMoments ConditionedDeterminantMoments
open SphericalHessianMarginEvents SphericalTAPCertificate TwoAtomStationarity PureStationarity
open SphericalTAPCriticalLightBandMark SphericalTAPPureMarkedValueWeight
open SourcePureOriginalEdgeMargin SourcePureOriginalComplexityEnvelope
open SphericalPureCapSourceScalars SphericalPureCapCenteringIdentity
open scoped ENNReal Topology

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma center_one (μ : FiniteMixture) :
    centerCoefficients (mixtureCoefficients μ) 1 = mixtureCoefficients μ := by
  funext k
  simp [centerCoefficients]

/-- Hölder for the actual dependent determinant and bad-margin indicator,
under the value-and-zero-gradient posterior. -/
private lemma posterior_bad_margin_weight
    (p : ℕ) (hp : 2 ≤ p) {κ Z : ℝ} (hκ : 0 < κ) :
    let μ := FiniteMixture.pure p hp 1 (by positivity)
    let c := mixtureCoefficients μ
    let d := (κ / Real.sqrt (μ.xi2 1))^2 / (16 * Real.pi^2)
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+2)) (hu : ‖u‖^2 = (n+2 : ℕ)) (e : ℝ),
        2 * Real.sqrt (μ.xi2 1) + 2*κ ≤ (p : ℝ)*e → (p : ℝ)*e ≤ Z →
        (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) u).det| *
          hessianMarginFailureMark c κ J u ∂valueConditionedLaw c u hu e) ≤
        ENNReal.ofReal (C * Real.exp (-d*(n+1 : ℕ)/2)) *
          ENNReal.ofReal (GOEPhysicalPotential.physicalMean n (n+2) (μ.xi2 1)
            ((p : ℝ)*e)) := by
  classical
  intro μ c d
  obtain ⟨K,hK,hMom⟩ := pure_conditioned_determinant_moments p hp 1 (by positivity)
    (Q := 1) (by positivity) (g := 2*κ) (Z := Z) (r := 2)
    (by positivity) (by norm_num)
  refine ⟨K^(1/(2 : ℝ)), Real.rpow_pos_of_pos hK _, ?_⟩
  have hPost := source_pure_physical_posterior_hessian_margin p hp 1 (by positivity)
    (Q := 1) (g := 2*κ) (by positivity) (by positivity)
  simp only [one_pow, one_mul, center_one, show 2*κ/2 = κ by ring] at hPost hMom
  filter_upwards [hPost] with n hn
  intro u hu e he hZ
  let ν := valueConditionedLaw c u hu e
  let D := intrinsicDet μ 1 u
  let A := {J : Disorder (n+2) μ.maxDegree | ¬ sourceHessianMargin c κ J u}
  let φ := A.indicator (fun _ => (1 : ℝ))
  have hLaw : pureLaw p hp 1 (by positivity) 1 u hu e = ν := by
    change _ = valueConditionedLaw (mixtureCoefficients μ) u hu e
    rw [← center_one μ]
    unfold pureLaw valueConditionedLaw
    congr 1
  have hM := hMom n u hu e he hZ
  rw [hLaw] at hM
  have hD0 : ∀ J, 0 ≤ D J := fun _ => abs_nonneg _
  have hA : MeasurableSet A :=
    ((sourceHessianMargin_closed c κ).measurableSet.preimage
      (measurable_id.prodMk (measurable_const (a := u)))).compl
  have hφ : Measurable φ := measurable_const.indicator hA
  have hφ0 : ∀ J, 0 ≤ φ J ∧ φ J ≤ 1 := by
    intro J
    by_cases hJ : J ∈ A <;> simp [φ, hJ]
  have hφmean : (∫ J, φ J ∂ν) ≤ Real.exp (-d*(n+1 : ℕ)) := by
    have heq : (∫ J, φ J ∂ν) = ν.real A := by
      rw [show φ = A.indicator (fun _ => (1 : ℝ)) from rfl, integral_indicator hA]
      simp
    rw [heq]
    have h := hn u hu e he
    change ν.real A ≤ _ at h
    exact h.trans_eq (by
      congr 1
      dsimp [d]
      push_cast
      ring)
  let : IsProbabilityMeasure ν := by unfold ν valueConditionedLaw; infer_instance
  have hHolder := determinant_weighted_holder ν D φ hM.1
    (.of_forall hD0) hM.2.2.1 hφ.aestronglyMeasurable (.of_forall hφ0)
    (by norm_num : (1 : ℝ) < 2) hM.2.2.2.1 hM.2.2.2.2 hφmean
  have hRatio : (∫ J in A, D J ∂ν) / (∫ J, D J ∂ν) ≤
      K^(1/(2 : ℝ)) * Real.exp (-d*(n+1 : ℕ)/2) := by
    have heq : (∫ J, D J * φ J ∂ν) = ∫ J in A, D J ∂ν := by
      rw [← integral_indicator hA]
      congr 1
      funext J
      by_cases hJ : J ∈ A <;> simp [φ, hJ]
    rw [heq, show (1 : ℝ)-1/2 = 1/2 by norm_num, ← Real.exp_mul] at hHolder
    exact hHolder.trans_eq (by congr 2; ring)
  have hBound := palm_ratio_to_lintegral_bound ν D hM.1 hD0 A hA
    (by positivity) hM.2.2.1 hRatio
  have hmark : ∀ J : Disorder (n+2) μ.maxDegree,
      hessianMarginFailureMark c κ J u = if J ∈ A then 1 else 0 := by
    intro J
    by_cases hJ : sourceHessianMargin c κ J u <;> simp [hessianMarginFailureMark, A, hJ]
  have hmean : (∫⁻ J, ENNReal.ofReal (D J) ∂ν) =
      ENNReal.ofReal (GOEPhysicalPotential.physicalMean n (n+2) (μ.xi2 1)
        ((p : ℝ)*e)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hM.1 (.of_forall hD0), hM.2.1]
  rw [hmean] at hBound
  have hD_eq (J : Disorder (n+2) μ.maxDegree) :
      D J = |(intrinsicHessian (field c J) u).det| := by
    simp only [D, intrinsicDet, center_one]
    rfl
  calc
    _ = ∫⁻ J, ENNReal.ofReal (D J) *
        @ite ℝ≥0∞ (J ∈ A) (Classical.propDecidable _) 1 0 ∂ν := by
      apply lintegral_congr
      intro J
      rw [hD_eq J, hmark J]
      split_ifs <;> rfl
    _ ≤ _ := hBound

variable (p : ℕ) (hp : 4 ≤ p)

local notation "μp" => (FiniteMixture.pure p (by omega) 1 (by positivity))
local notation "ep" => (pureEnergyConstant p (by omega))
local notation "Δp" => (ep - 2*Real.sqrt (((p : ℝ)-1)/(p : ℝ)))
local notation "κp" => ((p : ℝ)*Δp/4)

/-- Manuscript `lem:pc-hessian`: the expected count of critical points
failing the fixed positive Hessian margin is exponentially small throughout
one fixed normalized window around the pure ground energy. -/
theorem pure_high_window_bad_margin_mean :
    0 < κp ∧
    ∃ τ a : ℝ, 0 < τ ∧ τ ≤ Δp/4 ∧ 0 < a ∧
      ∀ᶠ n : ℕ in atTop,
        (∫⁻ J,
          actualValueWindowCount (n+1) (mixtureCoefficients μp)
            (Icc (ep-τ) (ep+τ))
            (hessianMarginFailureMark (mixtureCoefficients μp) κp) J
          ∂disorderLaw (n+2) (μp).maxDegree) ≤
        ENNReal.ofReal (Real.exp (-a*(n+2 : ℕ))) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hp1 : 0 ≤ (p : ℝ)-1 := by
    have h : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
    linarith
  let β := Thresholds.staticThreshold (fun r : ℝ => r^p) + 1
  obtain ⟨x,Q,hcert⟩ := pure_certificate_above_static p hp
    (show Thresholds.staticThreshold (fun r : ℝ => r^p) < β by dsimp [β]; linarith)
  have hedge := source_pure_original_ground_energy_above_edge p hp hcert
  have hξ : (μp).xi2 1 = (p : ℝ)*((p : ℝ)-1) := by
    simp only [pure_xi2, one_pow, mul_one]
  have hsquare : ((p : ℝ)*Real.sqrt (((p : ℝ)-1)/(p : ℝ)))^2 =
      (p : ℝ)*((p : ℝ)-1) := by
    rw [mul_pow, Real.sq_sqrt (div_nonneg hp1 hpR.le)]
    field_simp
  have hroot : Real.sqrt ((p : ℝ)*((p : ℝ)-1)) =
      (p : ℝ)*Real.sqrt (((p : ℝ)-1)/(p : ℝ)) := by
    nlinarith [Real.sq_sqrt (mul_nonneg hpR.le hp1),
      Real.sqrt_nonneg ((p : ℝ)*((p : ℝ)-1)),
      mul_nonneg hpR.le (Real.sqrt_nonneg (((p : ℝ)-1)/(p : ℝ)))]
  have hgap : (p : ℝ)*Δp = (p : ℝ)*ep - 2*Real.sqrt ((μp).xi2 1) := by
    rw [hξ, hroot]
    ring
  have hΔ : 0 < Δp := by
    rw [hroot] at hedge
    nlinarith
  have hκ : 0 < κp := by positivity
  refine ⟨hκ, ?_⟩
  let d := (κp / Real.sqrt ((μp).xi2 1))^2 / (16 * Real.pi^2)
  have hd : 0 < d := by
    exact div_pos (sq_pos_of_pos (div_pos hκ
      (Real.sqrt_pos.mpr ((μp).xi2_pos (by norm_num))))) (by positivity)
  let c₀ := pureIntensityConstant p (by omega)
  have hc₀ : 0 < c₀ := pureIntensityConstant_pos p (by omega)
  let τ := min (Δp/4) (d/(16*c₀))
  have hτ : 0 < τ := lt_min (by positivity) (by positivity)
  have hτΔ : τ ≤ Δp/4 := min_le_left _ _
  have hτd : c₀*τ ≤ d/16 := by
    have h := (le_div_iff₀ (show 0 < 16*c₀ by positivity)).mp (min_le_right (Δp/4) (d/(16*c₀)))
    change τ*(16*c₀) ≤ d at h
    nlinarith
  let Z := (p : ℝ)*(ep+Δp/4)
  have hBox : ∀ e ∈ Icc (ep-τ) (ep+τ),
      2*Real.sqrt ((μp).xi2 1)+2*κp ≤ (p : ℝ)*e ∧ (p : ℝ)*e ≤ Z := by
    intro e he
    have hlo := mul_le_mul_of_nonneg_left he.1 hpR.le
    have hhi := mul_le_mul_of_nonneg_left he.2 hpR.le
    have hτp := mul_le_mul_of_nonneg_left hτΔ hpR.le
    dsimp [Z]
    constructor <;> nlinarith [hgap]
  obtain ⟨_,B,_,hB,hIntensity⟩ := actual_pure_intensity_prefactors p (by omega)
    1 (by positivity) (Q := 1) (by positivity) (g := 2*κp) (Z := Z) (by positivity)
  obtain ⟨C,hC,hPost⟩ := posterior_bad_margin_weight p (by omega) (Z := Z) hκ
  simp only [one_pow, one_mul] at hIntensity
  let A := 2*τ*B*C
  have hA : 0 < A := by positivity
  have hN : Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hAbsorb : ∀ᶠ n : ℕ in atTop,
      A*(n+2 : ℕ)*Real.exp (-(d/8)*(n+2 : ℕ)) ≤ 1 := by
    have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (hN.const_mul_atTop (show 0 < d/8 by positivity))
    have ht' : Tendsto (fun n : ℕ => A*(n+2 : ℕ)*Real.exp (-(d/8)*(n+2 : ℕ)))
        atTop (𝓝 (0 : ℝ)) := by
      convert ht.const_mul (A/(d/8)) using 1
      · funext n
        simp only [Function.comp_def, pow_one, neg_mul]
        field_simp
      · simp
    exact (ht'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun _ h => h.le)
  refine ⟨τ, d/16, hτ, hτΔ, by positivity, ?_⟩
  filter_upwards [hPost, hAbsorb] with n hn habs
  let w := ENNReal.ofReal (C * Real.exp (-d*(n+1 : ℕ)/2))
  have hKR :
      (∫⁻ J, actualValueWindowCount (n+1) (mixtureCoefficients μp)
        (Icc (ep-τ) (ep+τ))
        (hessianMarginFailureMark (mixtureCoefficients μp) κp) J
        ∂disorderLaw (n+2) (μp).maxDegree) ≤
      ∫⁻ e in Icc (ep-τ) (ep+τ), pureCriticalIntensity n p (by omega)
        1 (by positivity) 1 e * w := by
    have h := actual_pure_marked_count_le_value_weight n p (by omega) 1 (by positivity)
      (Q := 1) (by positivity) (Icc (ep-τ) (ep+τ)) measurableSet_Icc
      (hessianMarginFailureMark (mixtureCoefficients μp) κp)
      (hessianMarginFailureMark_measurable _ _) (fun _ => w) (by
        intro u hu e he
        simpa only [center_one, one_pow, one_mul] using
          hn u hu e (hBox e he).1 (hBox e he).2)
    simpa only [center_one] using h
  have hDensity : ∀ e ∈ Icc (ep-τ) (ep+τ),
      pureCriticalIntensity n p (by omega) 1 (by positivity) 1 e * w ≤
      ENNReal.ofReal (B*Real.sqrt (n+2 : ℕ)*C *
        Real.exp (c₀*τ*(n+2 : ℕ)-d*(n+1 : ℕ)/2)) := by
    intro e he
    have hI := (hIntensity n e (hBox e he)).2
    have hComp := pure_original_complexity_global_linear_loss p hp hcert e
    have hCompτ : pureMarkedComplexity p (by omega) 1 (by positivity) 1 e ≤ c₀*τ := by
      have hmul := mul_le_mul_of_nonneg_left he.1 hc₀.le
      dsimp [c₀] at *
      linarith
    have hExp : Real.exp ((n+2 : ℕ)*pureMarkedComplexity p (by omega)
        1 (by positivity) 1 e) ≤ Real.exp (c₀*τ*(n+2 : ℕ)) := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left hCompτ (show (0 : ℝ) ≤ (n+2 : ℕ) by positivity)
      nlinarith
    calc
      _ ≤ ENNReal.ofReal (B*Real.sqrt (n+2 : ℕ)*
          Real.exp ((n+2 : ℕ)*pureMarkedComplexity p (by omega)
            1 (by positivity) 1 e)) * w := mul_le_mul' hI (le_refl w)
      _ ≤ ENNReal.ofReal (B*Real.sqrt (n+2 : ℕ)*
          Real.exp (c₀*τ*(n+2 : ℕ))) * w := by
        gcongr
      _ = _ := by
        dsimp [w]
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        calc
          _ = (B*Real.sqrt (n+2 : ℕ)*C) *
              (Real.exp (c₀*τ*(n+2 : ℕ)) * Real.exp (-d*(n+1 : ℕ)/2)) := by ring
          _ = _ := by
            rw [← Real.exp_add]
            congr 2
            ring
  have hIntegral :
      (∫⁻ e in Icc (ep-τ) (ep+τ), pureCriticalIntensity n p (by omega)
        1 (by positivity) 1 e * w) ≤
      ENNReal.ofReal (A*Real.sqrt (n+2 : ℕ) *
        Real.exp (c₀*τ*(n+2 : ℕ)-d*(n+1 : ℕ)/2)) := by
    calc
      _ ≤ ∫⁻ _e in Icc (ep-τ) (ep+τ),
          ENNReal.ofReal (B*Real.sqrt (n+2 : ℕ)*C *
            Real.exp (c₀*τ*(n+2 : ℕ)-d*(n+1 : ℕ)/2)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with e he
        exact hDensity e he
      _ = _ := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        dsimp [A]
        ring
  have hNr : (2 : ℝ) ≤ (n+2 : ℕ) := by exact_mod_cast (show 2 ≤ n+2 by omega)
  have hsqrt : Real.sqrt (n+2 : ℕ) ≤ (n+2 : ℕ) := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (n+2 : ℕ) by positivity)
    nlinarith [Real.sqrt_nonneg (n+2 : ℕ)]
  have hRate : c₀*τ*(n+2 : ℕ)-d*(n+1 : ℕ)/2 ≤
      -(d/8)*(n+2 : ℕ) - (d/16)*(n+2 : ℕ) := by
    have h := mul_le_mul_of_nonneg_right hτd (show (0 : ℝ) ≤ (n+2 : ℕ) by positivity)
    push_cast at *
    nlinarith
  have hFinal : A*Real.sqrt (n+2 : ℕ)*
      Real.exp (c₀*τ*(n+2 : ℕ)-d*(n+1 : ℕ)/2) ≤
      Real.exp (-(d/16)*(n+2 : ℕ)) := by
    calc
      _ ≤ A*(n+2 : ℕ)*Real.exp (-(d/8)*(n+2 : ℕ) - (d/16)*(n+2 : ℕ)) := by
        gcongr
      _ = (A*(n+2 : ℕ)*Real.exp (-(d/8)*(n+2 : ℕ))) *
          Real.exp (-(d/16)*(n+2 : ℕ)) := by
        rw [mul_assoc (A*(n+2 : ℕ)), ← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right habs (Real.exp_pos _).le
  exact hKR.trans (hIntegral.trans (ENNReal.ofReal_le_ofReal hFinal))

end SlowEquilibration.PureHighEnergyBadHessianCount

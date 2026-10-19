-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceActualProductComparison
public import SlowEquilibration.ConditionedEntranceSourceFixedAxisProbabilityRate
public import SlowEquilibration.ConditionedEntranceSourceGradientCutoffRate
public import SlowEquilibration.ConditionedEntranceSourceCutoffHorizonMono
public import SlowEquilibration.SphericalPosteriorHorizonLawExtension
public import SlowEquilibration.SphericalEvenReplicaTypicality

/-! Unconditional manuscript-rate cap entrance bound for the actual mixed
Gaussian-regression posterior diffusion, every prescribed physical axis,
bounded energy/radial marks, and every sufficiently small cap radius. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalForm SphericalMarkedWindows
open SphericalPosteriorGradientIndependence SphericalOverlapExponential
open SphericalAging HardSphereDynamics
open scoped NNReal
set_option autoImplicit false
set_option maxHeartbeats 1300000

private theorem exponentialGridHorizon_mono
    (N : ℕ) {γ γ' : ℝ} (hγ : γ ≤ γ') :
    exponentialGridHorizon γ N ≤ exponentialGridHorizon γ' N := by
  apply NNReal.coe_le_coe.mp
  change Real.exp ((N : ℝ)*γ) ≤ Real.exp ((N : ℝ)*γ')
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hγ (Nat.cast_nonneg N))

theorem actual_mixedPosterior_fixed_axis_cap_hit_source_rate_all_small_scales
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree)
    {Q B β : ℝ} (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hnp : μ.minDegree < μ.maxDegree) (hB : 0 ≤ B) (hβ : 0 ≤ β) :
    ∃ aStar : ℝ, 0 < aStar ∧
      ∀ {a : ℝ} (_ha : 0 < a), a ≤ aStar →
        ∃ (T : ℝ≥0), 0 < T ∧
        ∃ (γ c C : ℝ), 0 < γ ∧ 0 < c ∧ 0 < C ∧
          ∀ᶠ n : ℕ in atTop,
            ∀ (e k : ℝ), |e| ≤ B → |k| ≤ B →
            ∀ (u : Vector (n+1)) (_hu : OnSphere u),
              let H := exponentialGridHorizon γ (n+1)
              (posteriorTrajectoryLaw n μ).real {q | ∃ t : ℝ≥0, t ≤ H ∧
                a ≤ |mixedPosteriorOverlapScore n μ Q u
                  (scorePairEquiv (e,k)) β (H+2*T) t q|} ≤
              C*(((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)+
                ((n+1 : ℕ) : ℝ)^(3-(μ.minDegree : ℝ)))+
                Real.exp (-c*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨aStar,hStar,hScales⟩ :=
    actual_mixedSource_fixed_axis_probability_rate_all_small_scales
      μ hd hQ hQ1 hnp hB hβ
  refine ⟨aStar,hStar,?_⟩
  intro a ha hab
  obtain ⟨γcut,ccut,Ccut,hγcut,hccut,hCcut,hCutEvent⟩ := hScales ha hab
  obtain ⟨T,hT,γgrad,cgrad,hγgrad,hcgrad,hGradEvent⟩ :=
    source_mixedPosterior_uniform_gradient_cutoff_rate
      μ hnp (α := 2*a) hQ hQ1 hB hβ (mul_pos (by norm_num) ha)
  let γ := min γcut γgrad
  let cmin := min ccut cgrad
  let c := cmin/2
  have hγ : 0 < γ := lt_min hγcut hγgrad
  have hcmin : 0 < cmin := lt_min hccut hcgrad
  have hc : 0 < c := half_pos hcmin
  refine ⟨T,hT,γ,c,Ccut,hγ,hc,hCcut,?_⟩
  filter_upwards [hCutEvent,hGradEvent,
    SphericalModel.weighted_exponential_eventually_le hcmin 2]
    with n hnCut hnGrad hnExp
  intro e k he hk u hu
  dsimp only
  let H := exponentialGridHorizon γ (n+1)
  let Hcut := exponentialGridHorizon γcut (n+1)
  let Hgrad := exponentialGridHorizon γgrad (n+1)
  let Sgrad := Hgrad+2*T
  have hHcut : H ≤ Hcut :=
    exponentialGridHorizon_mono (n+1) (min_le_left _ _)
  have hHgrad : H ≤ Hgrad :=
    exponentialGridHorizon_mono (n+1) (min_le_right _ _)
  have hHSgrad : H ≤ Sgrad := hHgrad.trans (le_add_right le_rfl)
  have hHSfinal : H ≤ H+2*T := le_add_right le_rfl
  have hExt := mixedPosterior_overlap_horizon_probability_extension
    n μ Q u (scorePairEquiv (e,k)) β H (H+2*T) Sgrad
    hHSfinal hHSgrad a
  have hComp := actual_mixedPosterior_joint_cap_hit_le_sourceCutoff_add_gradient
    n μ Q hQ hQ1 hnp u hu e k a ha β H Sgrad hHSgrad
  have hCutInt (U : ℝ≥0) : Integrable
      (fun J : Disorder (n+1) μ.maxDegree =>
        sourceCapHitProbability μ Q hQ hnp (2*a) sourceScalarCutoff
          sourceScalarCutoff_contDiff_two β U (J,(u,(e,k))))
      (disorderLaw (n+1) μ.maxDegree) := by
    apply Integrable.of_bound
      ((sourceCapHitProbability_measurable μ Q hQ hnp (2*a)
        sourceScalarCutoff sourceScalarCutoff_contDiff_two β U).comp
          (measurable_id.prodMk (measurable_const.prodMk
            (measurable_const.prodMk measurable_const)))).aestronglyMeasurable 1
    apply ae_of_all
    intro J
    change |sourceCapHitProbability μ Q hQ hnp (2*a) sourceScalarCutoff
      sourceScalarCutoff_contDiff_two β U (J,(u,(e,k)))| ≤ 1
    rw [abs_of_nonneg
      (sourceCapHitProbability_mem_unit μ Q hQ hnp (2*a)
        sourceScalarCutoff sourceScalarCutoff_contDiff_two β U _).1]
    exact (sourceCapHitProbability_mem_unit μ Q hQ hnp (2*a)
      sourceScalarCutoff sourceScalarCutoff_contDiff_two β U _).2
  have hCutSmall :
      (∫ J, sourceCapHitProbability μ Q hQ hnp (2*a) sourceScalarCutoff
        sourceScalarCutoff_contDiff_two β H (J,(u,(e,k)))
        ∂disorderLaw (n+1) μ.maxDegree) ≤
      Ccut*(((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)+
        ((n+1 : ℕ) : ℝ)^(3-(μ.minDegree : ℝ)))+
        Real.exp (-ccut*((n+1 : ℕ) : ℝ)) := by
    have hMono := integral_mono (hCutInt H) (hCutInt Hcut)
      (fun J => sourceCapHitProbability_mono_horizon
        (by omega : 1 ≤ n+1) μ hnp Q hQ hQ1 (2*a)
        (mul_pos (by norm_num) ha) sourceScalarCutoff
        sourceScalarCutoff_contDiff_two β H Hcut hHcut
        (J,(u,(e,k))) hu)
    exact hMono.trans (hnCut e k he hk u hu)
  have hGradLarge := hnGrad u ((onSphere_iff_norm_sq u).mp hu)
    e k he hk
  have hGradSmall :
      (posteriorTrajectoryLaw n μ).real {q | ∃ t : ℝ≥0, t ≤ H ∧
        2*a ≤ |mixedPosteriorOriginalGradientScore n μ Q u
          (scorePairEquiv (e,k)) β Sgrad t q|} ≤
      Real.exp (-cgrad*((n+1 : ℕ) : ℝ)) := by
    have hfinite : (posteriorTrajectoryLaw n μ)
        {q | ∃ t : ℝ≥0, t ≤ Hgrad ∧
          2*a ≤ |mixedPosteriorOriginalGradientScore n μ Q u
            (scorePairEquiv (e,k)) β Sgrad t q|} ≠ ⊤ := measure_ne_top _ _
    have hMono := measureReal_mono (μ:=posteriorTrajectoryLaw n μ)
      (show {q | ∃ t : ℝ≥0, t ≤ H ∧
          2*a ≤ |mixedPosteriorOriginalGradientScore n μ Q u
            (scorePairEquiv (e,k)) β Sgrad t q|} ⊆
        {q | ∃ t : ℝ≥0, t ≤ Hgrad ∧
          2*a ≤ |mixedPosteriorOriginalGradientScore n μ Q u
            (scorePairEquiv (e,k)) β Sgrad t q|} from by
        rintro q ⟨t,ht,ha⟩
        exact ⟨t,ht.trans hHgrad,ha⟩) hfinite
    exact hMono.trans hGradLarge
  have hExpCut : Real.exp (-ccut*((n+1 : ℕ) : ℝ)) ≤
      Real.exp (-cmin*((n+1 : ℕ) : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [min_le_left ccut cgrad, Nat.cast_nonneg (α := ℝ) (n+1)]
  have hExpGrad : Real.exp (-cgrad*((n+1 : ℕ) : ℝ)) ≤
      Real.exp (-cmin*((n+1 : ℕ) : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [min_le_right ccut cgrad, Nat.cast_nonneg (α := ℝ) (n+1)]
  rw [hExt]
  change (posteriorTrajectoryLaw n μ).real {q | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |mixedPosteriorOverlapScore n μ Q u
        (scorePairEquiv (e,k)) β Sgrad t q|} ≤ _
  have hBound := hComp.trans (add_le_add hCutSmall hGradSmall)
  dsimp only [γ,c,cmin] at *
  nlinarith [hBound,hExpCut,hExpGrad,hnExp]

end SlowEquilibration.ConditionedEntrance

-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPosteriorPathIndependence
public import SlowEquilibration.SphericalOriginalGradientTail

/-! Actual uniform-start posterior Brownian trajectories remain spherical and
have the source Gaussian tangent-gradient tail at every deterministic time. -/
@[expose] public section
namespace SlowEquilibration.SphericalPosteriorGradientIndependence
noncomputable section
open Function MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm SphericalGaussianJet SphericalPosteriorMaps SphericalDynamics
open SphericalRotationCovariance
open SphericalAging HardSphereDynamics
open scoped Topology ENNReal NNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000

theorem original_gradient_measurable (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1)) :
    Measurable (fun g : EuclideanDisorder (n+1) μ.maxDegree=>
      surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder g)) u) := by
  have he : (fun g : EuclideanDisorder (n+1) μ.maxDegree=>
      surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder g)) u)=
        surfaceGamma (centerCoefficients (mixtureCoefficients μ) Q) u := by
    funext g
    simp only [surfaceGamma,ContinuousLinearMap.comp_apply,IntrinsicGradientRegression.ambientGradientCLM_apply]
    rfl
  rw [he]
  exact (surfaceGamma _ u).continuous.measurable

theorem original_gradient_trajectory_marginal (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) :
    (posteriorTrajectoryLaw n μ).map
      (fun q=>surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder q.1)) u)=
    (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)).map
      (fun g=>surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder g)) u) := by
  unfold posteriorTrajectoryLaw
  change ((stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)).prod
    ((sphereLaw (n+1)).prod (VectorBrownian.law (n+1)))).map
    ((fun g=>surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder g)) u) ∘ Prod.fst)=_
  rw [←Measure.map_map (original_gradient_measurable n μ Q u) measurable_fst,
    Measure.map_fst_prod,measure_univ,one_smul]

theorem mixedPosteriorContinuousPath_state_spherical (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) (marks : EuclideanSpace ℝ (Fin 2)) (β : ℝ) (T : ℝ≥0)
    (t : PathTime T) :
    ∀ᵐ q ∂posteriorTrajectoryLaw n μ, ‖mixedPosteriorContinuousPath n μ Q u marks β T q t‖^2=(n+1:ℕ) := by
  have hm := (continuous_eval_const t).measurable.comp
    (mixedPosteriorContinuousPath_measurable n μ Q u marks β T)
  unfold posteriorTrajectoryLaw
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (hm.norm.pow_const 2) measurable_const)).mpr
  apply Filter.Eventually.of_forall
  intro z
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun ((hm.comp (measurable_const.prodMk measurable_id)).norm.pow_const 2) measurable_const)).mpr
  filter_upwards [sphereLaw_support (N:=n+1) (by omega)] with x hx
  filter_upwards [jointContinuousPath_ae_actual μ β T (unpackDisorder (mixedPosterior n μ Q u marks z),x),
    mixedProcess_onSphere (by omega : n+1≠0) μ (unpackDisorder (mixedPosterior n μ Q u marks z)) β x
      ((onSphere_iff_norm_sq x).mpr hx)] with ω he hs
  change ‖jointContinuousPath μ β T ((unpackDisorder (mixedPosterior n μ Q u marks z),x),ω) t‖^2=_
  rw [he t]
  exact (onSphere_iff_norm_sq _).mp (hs t.1)

theorem valuePosteriorContinuousPath_state_spherical (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) (mark : ℝ) (β : ℝ) (T : ℝ≥0)
    (t : PathTime T) :
    ∀ᵐ q ∂posteriorTrajectoryLaw n μ, ‖valuePosteriorContinuousPath n μ Q u mark β T q t‖^2=(n+1:ℕ) := by
  have hm := (continuous_eval_const t).measurable.comp
    (valuePosteriorContinuousPath_measurable n μ Q u mark β T)
  unfold posteriorTrajectoryLaw
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (hm.norm.pow_const 2) measurable_const)).mpr
  apply Filter.Eventually.of_forall
  intro z
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun ((hm.comp (measurable_const.prodMk measurable_id)).norm.pow_const 2) measurable_const)).mpr
  filter_upwards [sphereLaw_support (N:=n+1) (by omega)] with x hx
  filter_upwards [jointContinuousPath_ae_actual μ β T (unpackDisorder (valuePosterior n μ Q u mark z),x),
    mixedProcess_onSphere (by omega : n+1≠0) μ (unpackDisorder (valuePosterior n μ Q u mark z)) β x
      ((onSphere_iff_norm_sq x).mpr hx)] with ω he hs
  change ‖jointContinuousPath μ β T ((unpackDisorder (valuePosterior n μ Q u mark z),x),ω) t‖^2=_
  rw [he t]
  exact (onSphere_iff_norm_sq _).mp (hs t.1)

/-- A generic independence transport with the actual center-gradient marginal.
The Gaussian covariance and tail are derived, rather than supplied. -/
theorem independent_spherical_state_original_gradient_tail {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ))
    (Y G : Ω→Vector (n+1)) (hY : Measurable Y) (hG : Measurable G)
    (hI : IndepFun Y G ρ) (hS : ∀ᵐ ω ∂ρ, ‖Y ω‖^2=(n+1:ℕ))
    (hLaw : ρ.map G=(stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)).map
      (fun g=>surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder g)) u))
    {α : ℝ} (hα : 0≤α) :
    ρ.real {ω | α/2≤|inner ℝ (G ω) (Y ω)/(n+1:ℕ)|} ≤
      2*Real.exp (-((n+1:ℕ):ℝ)*α^2/(8*(Q*μ.xi1 Q))) := by
  let C := 2*Real.exp (-((n+1:ℕ):ℝ)*α^2/(8*(Q*μ.xi1 Q)))
  let S : Set (Vector (n+1)×Vector (n+1)) := {q | α/2≤|inner ℝ q.2 q.1/(n+1:ℕ)|}
  have hSm : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
  have hYm : ∀ᵐ y ∂ρ.map Y, ‖y‖^2=(n+1:ℕ) :=
    (ae_map_iff hY.aemeasurable (measurableSet_eq_fun (measurable_id.norm.pow_const 2) measurable_const)).mpr hS
  have hBound (y : Vector (n+1)) (hy : ‖y‖^2=(n+1:ℕ)) :
      (ρ.map G) (Prod.mk y ⁻¹' S) ≤ ENNReal.ofReal C := by
    rw [hLaw,Measure.map_apply (original_gradient_measurable n μ Q u)
      (hSm.preimage measurable_prodMk_left),←ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (original_tangent_projection_tail n μ hQ u hu y hy hα)
  have hP : (ρ.map Y).prod (ρ.map G) S ≤ ENNReal.ofReal C := by
    rw [Measure.prod_apply hSm]
    calc
      _ ≤ ∫⁻ _y, ENNReal.ofReal C ∂ρ.map Y := lintegral_mono_ae (hYm.mono fun y hy=>hBound y hy)
      _ = _ := by simp [Measure.map_apply_of_aemeasurable hY.aemeasurable MeasurableSet.univ]
  have he := Measure.map_apply (μ:=ρ) (hY.prodMk hG) hSm
  rw [hI.map_prod_eq_prod_map_map hY.aemeasurable hG.aemeasurable] at he
  have hp : ρ ((fun ω=>(Y ω,G ω)) ⁻¹' S) ≤ ENNReal.ofReal C := he ▸ hP
  exact (ENNReal.toReal_mono (by finiteness) hp).trans_eq (ENNReal.toReal_ofReal (by unfold C; positivity))

theorem mixedPosterior_fixedTime_original_gradient_tail (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ))
    (marks : EuclideanSpace ℝ (Fin 2)) (β : ℝ) (T : ℝ≥0) (t : PathTime T)
    {α : ℝ} (hα : 0≤α) :
    (posteriorTrajectoryLaw n μ).real {q | α/2≤
      |inner ℝ (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder q.1)) u)
        (mixedPosteriorContinuousPath n μ Q u marks β T q t)/(n+1:ℕ)|} ≤
      2*Real.exp (-((n+1:ℕ):ℝ)*α^2/(8*(Q*μ.xi1 Q))) := by
  have hm : Measurable (fun f : ContinuousPath (n+1) T=>f t) := (continuous_eval_const t).measurable
  have hI := (mixedPosteriorContinuousPath_independent_original_gradient n μ hQ u hu marks β T).comp hm measurable_id
  apply independent_spherical_state_original_gradient_tail (posteriorTrajectoryLaw n μ) n μ hQ u hu
    (fun q=>mixedPosteriorContinuousPath n μ Q u marks β T q t) _
    (hm.comp (mixedPosteriorContinuousPath_measurable n μ Q u marks β T))
    ((original_gradient_measurable n μ Q u).comp measurable_fst)
  · simpa only [Function.comp_def,id_eq] using hI
  · exact mixedPosteriorContinuousPath_state_spherical n μ Q u marks β T t
  · exact original_gradient_trajectory_marginal n μ Q u
  · exact hα

theorem valuePosterior_fixedTime_original_gradient_tail (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ))
    (mark : ℝ) (β : ℝ) (T : ℝ≥0) (t : PathTime T)
    {α : ℝ} (hα : 0≤α) :
    (posteriorTrajectoryLaw n μ).real {q | α/2≤
      |inner ℝ (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder q.1)) u)
        (valuePosteriorContinuousPath n μ Q u mark β T q t)/(n+1:ℕ)|} ≤
      2*Real.exp (-((n+1:ℕ):ℝ)*α^2/(8*(Q*μ.xi1 Q))) := by
  have hm : Measurable (fun f : ContinuousPath (n+1) T=>f t) := (continuous_eval_const t).measurable
  have hI := (valuePosteriorContinuousPath_independent_original_gradient n μ hQ u hu mark β T).comp hm measurable_id
  apply independent_spherical_state_original_gradient_tail (posteriorTrajectoryLaw n μ) n μ hQ u hu
    (fun q=>valuePosteriorContinuousPath n μ Q u mark β T q t) _
    (hm.comp (valuePosteriorContinuousPath_measurable n μ Q u mark β T))
    ((original_gradient_measurable n μ Q u).comp measurable_fst)
  · simpa only [Function.comp_def,id_eq] using hI
  · exact valuePosteriorContinuousPath_state_spherical n μ Q u mark β T t
  · exact original_gradient_trajectory_marginal n μ Q u
  · exact hα

end
end SlowEquilibration.SphericalPosteriorGradientIndependence

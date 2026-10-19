-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalOriginalPureSourceCorrection

/-! The full continuous-process law of the actual conditional original
field equals the literal source corrected field of the genuine original
Gaussian tensor disorder, including the proper pure branch. -/

@[expose] public section
namespace SlowEquilibration.SphericalCriticalLatitude
noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression SphericalTaylorRemainder
open SphericalMarkedWindows SphericalPosteriorMaps ConditionedEntrance SphericalForm
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- The literal source corrected original field, as a continuous function
on any compact spatial parameter set. -/
def originalMixedSourceContinuousField (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0<Q) (hnp : μ.minDegree<μ.maxDegree) (u : Vector (n+1)) (e k : ℝ)
    (z : K→Vector (n+1)) (hz : Continuous z) (J : Disorder (n+1) μ.maxDegree) : C(K,ℝ) :=
  ⟨fun v => fieldOfMixture μ J (z v)+sourceRegressionCorrection μ Q hQ hnp J u e k (z v),by
    have hc : Continuous (sourceRegressionCorrection μ Q hQ hnp J u e k) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      exact (regressionCorrection_hasGradientAt μ Q u
        (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u)
        (field (centerCoefficients (mixtureCoefficients μ) Q) J u)
        (jet (centerCoefficients (mixtureCoefficients μ) Q) 1 u (fun _ => u) J) e k x).differentiableAt.continuousAt
    exact ((field_contDiff (mixtureCoefficients μ) J).continuous.comp hz).add (hc.comp hz)⟩

/-- The literal proper pure corrected original field on the same compact
spatial parameter set; its correction is the homogeneous polynomial. -/
def originalPureSourceContinuousField (n p : ℕ) (hp : 2≤p) (c : ℝ) (hc : 0<c) (Q : ℝ)
    (u : Vector (n+1)) (e : ℝ) (z : K→Vector (n+1)) (hz : Continuous z)
    (J : Disorder (n+1) (FiniteMixture.pure p hp c hc).maxDegree) : C(K,ℝ) :=
  ⟨fun v => fieldOfMixture (FiniteMixture.pure p hp c hc) J (z v)+
    pureSourceRegressionCorrection p hp c hc Q J u e (z v),by
    have hpc : Continuous (pureSourceRegressionCorrection p hp c hc Q J u e) := by
      unfold pureSourceRegressionCorrection pureRegressionCorrection overlap
      fun_prop
    exact ((field_contDiff (mixtureCoefficients (FiniteMixture.pure p hp c hc)) J).continuous.comp hz).add
      (hpc.comp hz)⟩

omit [CompactSpace K] in
/-- Pointwise semantic equality of the whole continuous source field. -/
theorem actual_mixedPosterior_original_continuous_field (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (hnp : μ.minDegree<μ.maxDegree) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (e k : ℝ) (z : K→Vector (n+1)) (hz : Continuous z)
    (g : EuclideanDisorder (n+1) μ.maxDegree) :
    modelContinuousField (mixtureCoefficients μ) z hz
      (mixedPosterior n μ Q u (scorePairEquiv (e,k)) g)=
      originalMixedSourceContinuousField n μ hQ hnp u e k z hz (unpackDisorder g) := by
  ext v
  rw [modelContinuousField_apply]
  simpa only [valueObservation,flatJetCLM_apply,jet,iteratedFDeriv_zero_apply,
    originalMixedSourceContinuousField,ContinuousMap.coe_mk,fieldOfMixture] using
      actual_mixedPosterior_original_field n μ hQ hnp u hu e k g (z v)

omit [CompactSpace K] in
/-- Whole-field semantic equality for the proper pure posterior. -/
theorem actual_purePosterior_original_continuous_field (n p : ℕ) (hp : 2≤p) (c : ℝ) (hc : 0<c)
    {Q : ℝ} (hQ : 0<Q) (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (e : ℝ)
    (z : K→Vector (n+1)) (hz : Continuous z)
    (g : EuclideanDisorder (n+1) (FiniteMixture.pure p hp c hc).maxDegree) :
    modelContinuousField (mixtureCoefficients (FiniteMixture.pure p hp c hc)) z hz
      (valuePosterior n (FiniteMixture.pure p hp c hc) Q u e g)=
      originalPureSourceContinuousField n p hp c hc Q u e z hz (unpackDisorder g) := by
  ext v
  rw [modelContinuousField_apply]
  simpa only [valueObservation,flatJetCLM_apply,jet,iteratedFDeriv_zero_apply,
    originalPureSourceContinuousField,ContinuousMap.coe_mk,fieldOfMixture] using
      actual_purePosterior_original_field n p hp c hc hQ u hu e g (z v)

omit [CompactSpace K] in
/-- The actual mixed conditional original field has exactly the literal
source corrected-field law under the genuine original tensor disorder. -/
theorem actual_mixed_conditioned_original_source_continuous_law (n : ℕ) (μ : FiniteMixture)
    [SecondCountableTopology K] [T2Space K] [Nonempty K]
    {Q : ℝ} (hQ : 0<Q) (hnp : μ.minDegree<μ.maxDegree) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (e k : ℝ) (z : K→Vector (n+1)) (hz : Continuous z) :
    (mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu (scorePairEquiv (e,k))).map
      (fun J => modelContinuousField (mixtureCoefficients μ) z hz (euclideanDisorder J))=
      (disorderLaw (n+1) μ.maxDegree).map
        (originalMixedSourceContinuousField n μ hQ hnp u e k z hz) := by
  let F := modelContinuousField (mixtureCoefficients μ) z hz
  have hm : Measurable (fun J : Disorder (n+1) μ.maxDegree => F (euclideanDisorder J)) :=
    F.continuous.measurable.comp (SphericalTaylorRemainder.euclideanDisorder_measurable _ _)
  have hp : Continuous (fun g => mixedPosterior n μ Q u (scorePairEquiv (e,k)) g) := by
    unfold mixedPosterior
    exact ((gradientResidual n μ Q u).continuous.comp (scoreResidual n μ Q u).continuous).add continuous_const
  have hp' : Measurable (fun g : EuclideanDisorder (n+1) μ.maxDegree =>
      unpackCLM (n+1) μ.maxDegree (mixedPosterior n μ Q u (scorePairEquiv (e,k)) g)) :=
    (unpackCLM (n+1) μ.maxDegree).continuous.measurable.comp hp.measurable
  rw [mixedConditionedLaw_eq_map n μ hQ hnp u hu,Measure.map_map hm hp']
  have he : (fun g : EuclideanDisorder (n+1) μ.maxDegree =>
      F (euclideanDisorder (unpackCLM (n+1) μ.maxDegree
        (mixedPosterior n μ Q u (scorePairEquiv (e,k)) g))))=
      fun g => originalMixedSourceContinuousField n μ hQ hnp u e k z hz (unpackDisorder g) := by
    funext g
    exact actual_mixedPosterior_original_continuous_field n μ hQ hnp u hu e k z hz g
  simp only [Function.comp_def]
  rw [he]
  have hr : Measurable (fun g : EuclideanDisorder (n+1) μ.maxDegree =>
      originalMixedSourceContinuousField n μ hQ hnp u e k z hz (unpackDisorder g)) := by
    have he' := he
    exact he' ▸ F.continuous.measurable.comp hp.measurable
  have hf := congrArg (fun ν => ν.map (fun g : EuclideanDisorder (n+1) μ.maxDegree =>
    originalMixedSourceContinuousField n μ hQ hnp u e k z hz (unpackDisorder g)))
      (actual_flattened_gaussian (n+1) μ.maxDegree).map_eq
  rw [Measure.map_map hr (SphericalTaylorRemainder.euclideanDisorder_measurable _ _)] at hf
  simpa only [Function.comp_def,unpack_euclideanDisorder] using hf.symm

omit [CompactSpace K] in
/-- The actual proper pure conditional original field has the literal
homogeneous corrected-field law, with scalar value conditioning only. -/
theorem actual_pure_conditioned_original_source_continuous_law (n p : ℕ) (hp : 2≤p) (c : ℝ) (hc : 0<c)
    [SecondCountableTopology K] [T2Space K] [Nonempty K]
    {Q : ℝ} (hQ : 0<Q) (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (e : ℝ)
    (z : K→Vector (n+1)) (hz : Continuous z) :
    (valueConditionedLaw (centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp c hc)) Q) u hu e).map
      (fun J => modelContinuousField (mixtureCoefficients (FiniteMixture.pure p hp c hc)) z hz (euclideanDisorder J))=
      (disorderLaw (n+1) (FiniteMixture.pure p hp c hc).maxDegree).map
        (originalPureSourceContinuousField n p hp c hc Q u e z hz) := by
  let μ := FiniteMixture.pure p hp c hc
  let F := modelContinuousField (mixtureCoefficients μ) z hz
  have hm : Measurable (fun J : Disorder (n+1) μ.maxDegree => F (euclideanDisorder J)) :=
    F.continuous.measurable.comp (SphericalTaylorRemainder.euclideanDisorder_measurable _ _)
  have hv : Continuous (fun g => valuePosterior n μ Q u e g) := by
    unfold valuePosterior
    exact ((gradientResidual n μ Q u).continuous.comp (valueResidual n μ Q u).continuous).add continuous_const
  have hv' : Measurable (fun g : EuclideanDisorder (n+1) μ.maxDegree =>
      unpackCLM (n+1) μ.maxDegree (valuePosterior n μ Q u e g)) :=
    (unpackCLM (n+1) μ.maxDegree).continuous.measurable.comp hv.measurable
  rw [valueConditionedLaw_eq_map n μ hQ u hu,Measure.map_map hm hv']
  have he : (fun g : EuclideanDisorder (n+1) μ.maxDegree =>
      F (euclideanDisorder (unpackCLM (n+1) μ.maxDegree (valuePosterior n μ Q u e g))))=
      fun g => originalPureSourceContinuousField n p hp c hc Q u e z hz (unpackDisorder g) := by
    funext g
    exact actual_purePosterior_original_continuous_field n p hp c hc hQ u hu e z hz g
  simp only [Function.comp_def]
  rw [he]
  have hr : Measurable (fun g : EuclideanDisorder (n+1) μ.maxDegree =>
      originalPureSourceContinuousField n p hp c hc Q u e z hz (unpackDisorder g)) := by
    exact he ▸ F.continuous.measurable.comp hv.measurable
  have hf := congrArg (fun ν => ν.map (fun g : EuclideanDisorder (n+1) μ.maxDegree =>
    originalPureSourceContinuousField n p hp c hc Q u e z hz (unpackDisorder g)))
      (actual_flattened_gaussian (n+1) μ.maxDegree).map_eq
  rw [Measure.map_map hr (SphericalTaylorRemainder.euclideanDisorder_measurable _ _)] at hf
  simpa only [Function.comp_def,unpack_euclideanDisorder] using hf.symm

end
end SlowEquilibration.SphericalCriticalLatitude

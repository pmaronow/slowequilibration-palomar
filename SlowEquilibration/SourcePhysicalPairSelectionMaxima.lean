-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairSelectionEvent

/-! The literal selection Hessian margin implies actual intrinsic negative
Hessians. Its selected critical-point sums therefore equal the corresponding
selected maximum sums, with exact Borel marked Kac--Rice identities. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Set
open SphericalModel SphericalGaussianJet SphericalForm SphereHessian
open SphericalMarkedWindows NegativeDefiniteOperators SphericalPosteriorMaps
open scoped ENNReal Topology RealInnerProductSpace
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance] Classical.propDecidable

lemma sourceSphereHessianExtension_intrinsic_apply {N P:ℕ} (hN:N≠0) (c:Degree P→ℝ)
    (J:Disorder N P) (u:Vector N) (hu:‖u‖^2=(N:ℝ)) (v:tangentPlane u) :
    (intrinsicHessian (field c J) u v:Vector N)=sourceSphereHessianExtension c J u v:=by
  have hP:tangentProjection u (v:Vector N)=v:=by
    rw [tangentProjection_eq_starProjection hN u (by simpa only [SphericalAging.HardSphereDynamics.OnSphere,real_inner_self_eq_norm_sq] using hu)]
    exact (tangentPlane u).starProjection_eq_self_iff.mpr v.property
  simp only [intrinsicHessian,sourceSphereHessianExtension,ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply,Submodule.coe_orthogonalProjectionOnto_apply]
  rw [←tangentProjection_eq_starProjection hN u (by simpa only [SphericalAging.HardSphereDynamics.OnSphere,real_inner_self_eq_norm_sq] using hu),hP]

lemma sourceHessianMargin_negative {N P:ℕ} (hN:N≠0) (c:Degree P→ℝ) {κ:ℝ}
    (hκ:0<κ) (J:Disorder N P) (u:Vector N) (hu:‖u‖^2=(N:ℝ))
    (hMargin:sourceHessianMargin c κ J u) :
    NegativeDefinite (intrinsicHessian (field c J) u):=by
  intro v hv
  have hP:tangentProjection u (v:Vector N)=v:=by
    rw [tangentProjection_eq_starProjection hN u (by simpa only [SphericalAging.HardSphereDynamics.OnSphere,real_inner_self_eq_norm_sq] using hu)]
    exact (tangentPlane u).starProjection_eq_self_iff.mpr v.property
  have hh:=hMargin (v:Vector N)
  rw [hP] at hh
  change inner ℝ (v:Vector N) (intrinsicHessian (field c J) u v:Vector N)<0
  rw [sourceSphereHessianExtension_intrinsic_apply hN c J u hu v]
  exact hh.trans_lt (mul_neg_of_neg_of_pos (neg_neg_of_pos hκ) (sq_pos_of_pos (show 0<‖(v:Vector N)‖ by simpa only [Submodule.norm_coe] using (norm_pos_iff.mpr hv))))

lemma sourceSelectionEvent_negative {N P:ℕ} (hN:N≠0) (c:Degree P→ℝ) {κ:ℝ}
    (hκ:0<κ) (C ε η E G:ℝ) (J:Disorder N P) (u:Vector N) (hu:‖u‖^2=(N:ℝ))
    (hSel:sourceSelectionEvent c κ C ε η E G J u) :
    NegativeDefinite (intrinsicHessian (field c J) u):=
  sourceHessianMargin_negative hN c hκ J u hu hSel.1

lemma sourceSelectionMark_negative_factor {P:ℕ} (n:ℕ) (c:Degree P→ℝ) {κ:ℝ}
    (hκ:0<κ) (C ε η E G:ℝ) (J:Disorder (n+1) P) (u:Vector (n+1))
    (hu:‖u‖^2=(n+1:ℕ)) (hcrit:surfaceGradient (field c J) u=0) :
    negativeHessianMark n c J u*sourceSelectionMark c κ C ε η E G J u=
      sourceSelectionMark c κ C ε η E G J u:=by
  by_cases hSel:sourceSelectionEvent c κ C ε η E G J u
  · have hNeg:=sourceSelectionEvent_negative (by omega) c hκ C ε η E G J u hu hSel
    have hRep:criticalNegative n c J u:=(criticalNegative_iff n c J u hu hcrit).mpr hNeg
    simp only [sourceSelectionMark,negativeHessianMark,ite_eq_left hSel,ite_eq_left hRep,one_mul]
  · simp only [sourceSelectionMark,ite_eq_right hSel,mul_zero]

theorem sourceRetainedScoreWindowCount_eq_selected_maxima {P:ℕ} (n:ℕ) (c:Degree P→ℝ)
    (K:Set (EuclideanSpace ℝ (Fin 2))) {κ:ℝ} (hκ:0<κ) (C ε η E G:ℝ) (J:Disorder (n+1) P) :
    sourceRetainedScoreWindowCount n c K κ C ε η E G J=
      actualScoreWindowCount n c K (fun J u=>negativeHessianMark n c J u*
        sourceSelectionMark c κ C ε η E G J u) J:=by
  unfold sourceRetainedScoreWindowCount actualScoreWindowCount
  apply tsum_congr
  intro u
  exact (sourceSelectionMark_negative_factor n c hκ C ε η E G J u u.property.1 u.property.2.1).symm

theorem sourceRetainedValueWindowCount_eq_selected_maxima {P:ℕ} (n:ℕ) (c:Degree P→ℝ)
    (I:Set ℝ) {κ:ℝ} (hκ:0<κ) (C ε η E G:ℝ) (J:Disorder (n+1) P) :
    sourceRetainedValueWindowCount n c I κ C ε η E G J=
      actualValueWindowCount n c I (fun J u=>negativeHessianMark n c J u*
        sourceSelectionMark c κ C ε η E G J u) J:=by
  unfold sourceRetainedValueWindowCount actualValueWindowCount
  apply tsum_congr
  intro u
  exact (sourceSelectionMark_negative_factor n c hκ C ε η E G J u u.property.1 u.property.2.1).symm

theorem sourceRetainedScoreWindowCount_kacRice (n:ℕ) (hn:1 ≤ n) (μ:FiniteMixture)
    {Q:ℝ} (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree)
    (K:Set (EuclideanSpace ℝ (Fin 2))) (hK:MeasurableSet K) (κ C ε η E G:ℝ) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    AEMeasurable (sourceRetainedScoreWindowCount n c K κ C ε η E G) (disorderLaw (n+1) μ.maxDegree) ∧
      (∫⁻ J,sourceRetainedScoreWindowCount n c K κ C ε η E G J ∂disorderLaw (n+1) μ.maxDegree)=
        sphereKRPrefactor n μ Q*∫⁻ u,mixedWindowIntensity n μ Q K
          (sourceSelectionMark c κ C ε η E G) u ∂sphereLaw (n+1):=by
  dsimp only
  exact actual_mixed_score_window_kacRice n hn μ hQ hnp K hK _
    (sourceSelectionMark_measurable _ κ C ε η E G)

theorem sourceRetainedValueWindowCount_kacRice (n:ℕ) (hn:1 ≤ n) (μ:FiniteMixture)
    {Q:ℝ} (hQ:0<Q) (I:Set ℝ) (hI:MeasurableSet I) (κ C ε η E G:ℝ) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    AEMeasurable (sourceRetainedValueWindowCount n c I κ C ε η E G) (disorderLaw (n+1) μ.maxDegree) ∧
      (∫⁻ J,sourceRetainedValueWindowCount n c I κ C ε η E G J ∂disorderLaw (n+1) μ.maxDegree)=
        sphereKRPrefactor n μ Q*∫⁻ u,valueWindowIntensity n μ Q I
          (sourceSelectionMark c κ C ε η E G) u ∂sphereLaw (n+1):=by
  dsimp only
  exact actual_value_window_kacRice n hn μ hQ I hI _
    (sourceSelectionMark_measurable _ κ C ε η E G)

end
end SlowEquilibration.PairConditionalDeterminantMoments

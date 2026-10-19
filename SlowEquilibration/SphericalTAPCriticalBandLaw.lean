-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalRemainderLaw
public import SlowEquilibration.SphericalTaylorBandGeometry
public import SlowEquilibration.SphericalSequentialRegression

@[expose] public section
/-! The original physical critical TAP band has the full sample-function
law of its actual Taylor residual plus the literal conditioned energy.
Both mixed score conditioning and proper value-only conditioning are
retained; no Parisi/TAP formula or Gibbs limit is assumed. -/
namespace SlowEquilibration.SphericalTAPCriticalBand
noncomputable section
open MeasureTheory ProbabilityTheory Function
open SphericalModel SphericalGaussianJet WholeFieldRegression IntrinsicHessianLaw
open ConditionedIntrinsicHessian ValueTangentConditioning SphericalMarkedWindows
open SphericalTaylorRemainder SphericalSequentialRegression IntrinsicGradientRegression
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The value-only physical kernel fixes the actual energy and the whole
zero tangent gradient at every prescribed value mark. -/
theorem actual_value_critical_firstJet_ae (n:ℕ) (μ:FiniteMixture) {Q:ℝ} (hQ:0<Q)
    (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ)) (e₀:ℝ) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    ∀ᵐ J ∂valueConditionedLaw c u hu e₀,
      field c J u=(n+1:ℕ)*e₀ ∧ intrinsicGamma c u (euclideanDisorder J)=0:=by
  dsimp only
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have H:=coefficientKernel_observation_ae (valueTangentCLM c u (tangentFrame u hu))
    (center_valueTangent_surjective (by omega) μ hQ u hu _
      (tangentFrame_orthonormal u hu) (tangentFrame_tangent u hu))
    (jointValueTarget n ((n+1:ℕ)*e₀))
  filter_upwards [H] with J hJ
  constructor
  · have hi:=congrArg (fun v=>v (Sum.inl 0)) hJ
    simpa only [actualObservation,valueTangentCLM_apply_value,unpack_euclideanDisorder,
      jet,iteratedFDeriv_zero_apply,jointValueTarget,WithLp.toLp_ofLp,Sum.elim_inl] using hi
  · apply (tangentFrame_gradient_zero_iff c u hu (euclideanDisorder J)).mp
    apply PiLp.ext
    intro i
    have hi:=congrArg (fun v=>v (Sum.inr i)) hJ
    simpa only [actualObservation,valueTangentCLM_apply_gradient,gradientCLM_apply,
      jointValueTarget,WithLp.toLp_ofLp,Sum.elim_inr,PiLp.zero_apply] using hi

/-- The genuine mixed critical kernel also fixes every tangent component;
its radial mark may vary independently of the band mean. -/
theorem actual_mixed_critical_firstJet_ae (n:ℕ) (μ:FiniteMixture) {Q:ℝ} (hQ:0<Q)
    (hnp:μ.minDegree<μ.maxDegree) (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ))
    (b:EuclideanSpace ℝ (Fin 2)) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    ∀ᵐ J ∂mixedConditionedLaw c u hu b,
      field c J u=(n+1:ℕ)*b 0 ∧ intrinsicGamma c u (euclideanDisorder J)=0:=by
  dsimp only
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have H:=coefficientKernel_observation_ae (jointCLM c u (tangentFrame u hu))
    (center_joint_surjective (by omega) μ hQ hnp u hu _
      (tangentFrame_orthonormal u hu) (tangentFrame_tangent u hu))
    (jointScoreTarget n (((n+1:ℕ):ℝ) • b))
  filter_upwards [H] with J hJ
  constructor
  · have hi:=congrArg (fun v=>v (Sum.inl 0)) hJ
    simpa only [actualObservation,jointCLM_apply_inl,scoreCLM_apply_zero,unpack_euclideanDisorder,
      jet,iteratedFDeriv_zero_apply,jointScoreTarget,WithLp.toLp_ofLp,Sum.elim_inl,
      PiLp.smul_apply,smul_eq_mul] using hi
  · apply (tangentFrame_gradient_zero_iff c u hu (euclideanDisorder J)).mp
    apply PiLp.ext
    intro i
    have hi:=congrArg (fun v=>v (Sum.inr i)) hJ
    simpa only [actualObservation,jointCLM_apply_inr,jointScoreTarget,WithLp.toLp_ofLp,
      Sum.elim_inr,PiLp.zero_apply] using hi

variable {K:Type*} [TopologicalSpace K] [CompactSpace K]

def actualCriticalBandContinuousField (n d:ℕ) (μ:FiniteMixture) (Q:ℝ)
    (u:Vector (n+1)) (e:Vector d→ₗᵢ[ℝ] Vector (n+1))
    (x:K→Vector d) (hx:Continuous x) : EuclideanDisorder (n+1) μ.maxDegree→L[ℝ] C(K,ℝ):=
  modelContinuousField (mixtureCoefficients μ) (fun v=>transverseBandPoint u e Q (x v))
    ((continuous_const.add (transverseOffset_parameter_continuous e Q x hx)).const_smul (Real.sqrt Q))

omit [CompactSpace K] in
theorem actualCriticalBandContinuousField_apply (n d:ℕ) (μ:FiniteMixture) (Q:ℝ)
    (u:Vector (n+1)) (e:Vector d→ₗᵢ[ℝ] Vector (n+1))
    (x:K→Vector d) (hx:Continuous x) (J:Disorder (n+1) μ.maxDegree) (v:K) :
    actualCriticalBandContinuousField n d μ Q u e x hx (euclideanDisorder J) v=
      field (mixtureCoefficients μ) J (transverseBandPoint u e Q (x v)):=by
  rw [actualCriticalBandContinuousField,modelContinuousField_apply,valueObservation_actual]

omit [CompactSpace K] in
/-- Deterministic identity for the original field on its physical TAP band,
under the literal energy and full zero-gradient first-jet conditions. -/
theorem actualCriticalBandContinuousField_eq_remainder
    (n d:ℕ) (μ:FiniteMixture) {Q:ℝ} (hQ:0<Q)
    (u:Vector (n+1)) (e:Vector d→ₗᵢ[ℝ] Vector (n+1)) (he:∀ y,inner ℝ (e y) u=0)
    (x:K→Vector d) (hx:Continuous x) (J:Disorder (n+1) μ.maxDegree) (E:ℝ)
    (hvalue:field (centerCoefficients (mixtureCoefficients μ) Q) J u=E)
    (hgrad:intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) u (euclideanDisorder J)=0) :
    actualCriticalBandContinuousField n d μ Q u e x hx (euclideanDisorder J)-ContinuousMap.const K E=
      taylorContinuousField (centerCoefficients (mixtureCoefficients μ) Q) u
        (fun v=>transverseOffset e Q (x v)) (transverseOffset_parameter_continuous e Q x hx)
        (euclideanDisorder J):=by
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  ext v
  have htan:=transverseOffset_tangent u e he Q (x v)
  have hdir:fderiv ℝ (field c J) u (transverseOffset e Q (x v))=0:=by
    have ht:transverseOffset e Q (x v) ∈ SphericalForm.tangentPlane u:=
      Submodule.mem_orthogonal_singleton_iff_inner_left.mpr htan
    have H:=intrinsicGamma_inner c u (euclideanDisorder J) ⟨transverseOffset e Q (x v),ht⟩
    change intrinsicGamma c u (euclideanDisorder J)=0 at hgrad
    rw [hgrad,inner_zero_right] at H
    simpa only [jet,iteratedFDeriv_one_apply,unpack_euclideanDisorder] using H.symm
  change actualCriticalBandContinuousField n d μ Q u e x hx (euclideanDisorder J) v-E=
    taylorRemainderCLM c u (transverseOffset e Q (x v)) (euclideanDisorder J)
  rw [actualCriticalBandContinuousField_apply,taylorRemainderCLM_actual,hvalue,hdir,sub_zero]
  exact congrArg (fun a:ℝ=>a-E)
    (field_center_scale (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ) hQ.le J _).symm

/-- Literal actual proper-value posterior law of the original physical
TAP-band field, after subtracting its conditioned bottom energy. -/
theorem actual_value_critical_band_continuous_law
    [SecondCountableTopology K] [T2Space K] [Nonempty K]
    (n d:ℕ) (hd:0<d) (μ:FiniteMixture) {Q:ℝ} (hQ:Q∈Set.Ioo (0:ℝ) 1)
    (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ))
    (e:Vector d→ₗᵢ[ℝ] Vector (n+1)) (he:∀ y,inner ℝ (e y) u=0)
    (x:K→Vector d) (hx:Continuous x) (e₀:ℝ) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    let θ:=μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)
    (valueConditionedLaw c u hu e₀).map (fun J=>
      actualCriticalBandContinuousField n d μ Q u e x hx (euclideanDisorder J)-
        ContinuousMap.const K ((n+1:ℕ)*e₀))=
      (disorderLaw d θ.maxDegree).map (fun J=>Real.sqrt (((n+1:ℕ):ℝ)/(d:ℝ)) •
        modelContinuousField (mixtureCoefficients θ) x hx (euclideanDisorder J)):=by
  dsimp only
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let z:=fun v=>transverseOffset e Q (x v)
  have hz:Continuous z:=transverseOffset_parameter_continuous e Q x hx
  have H₁:=Measure.map_congr (mβ:=borel C(K,ℝ)) ((actual_value_critical_firstJet_ae n μ hQ.1 u hu e₀).mono
    (fun J hJ=>actualCriticalBandContinuousField_eq_remainder n d μ hQ.1 u e he x hx J _ hJ.1 hJ.2))
  have H₂:=actual_critical_taylorContinuousField_value_law (by omega : 0<n+1) c
    (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.1.le) u (tangentFrame u hu)
    z hz (fun v=>transverseOffset_tangent u e he Q (x v)) (jointValueTarget n ((n+1:ℕ)*e₀))
  exact H₁.trans (H₂.trans (transverse_taylorContinuousField_law (by omega) hd μ hQ u hu e he x hx))

/-- The genuine mixed score posterior has the same original physical
TAP-band residual law, independently of its radial mark. -/
theorem actual_mixed_critical_band_continuous_law
    [SecondCountableTopology K] [T2Space K] [Nonempty K]
    (n d:ℕ) (hd:0<d) (μ:FiniteMixture) {Q:ℝ} (hQ:Q∈Set.Ioo (0:ℝ) 1)
    (hnp:μ.minDegree<μ.maxDegree)
    (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ))
    (e:Vector d→ₗᵢ[ℝ] Vector (n+1)) (he:∀ y,inner ℝ (e y) u=0)
    (x:K→Vector d) (hx:Continuous x) (b:EuclideanSpace ℝ (Fin 2)) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    let θ:=μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)
    (mixedConditionedLaw c u hu b).map (fun J=>
      actualCriticalBandContinuousField n d μ Q u e x hx (euclideanDisorder J)-
        ContinuousMap.const K ((n+1:ℕ)*b 0))=
      (disorderLaw d θ.maxDegree).map (fun J=>Real.sqrt (((n+1:ℕ):ℝ)/(d:ℝ)) •
        modelContinuousField (mixtureCoefficients θ) x hx (euclideanDisorder J)):=by
  dsimp only
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let z:=fun v=>transverseOffset e Q (x v)
  have hz:Continuous z:=transverseOffset_parameter_continuous e Q x hx
  have H₁:=Measure.map_congr (mβ:=borel C(K,ℝ)) ((actual_mixed_critical_firstJet_ae n μ hQ.1 hnp u hu b).mono
    (fun J hJ=>actualCriticalBandContinuousField_eq_remainder n d μ hQ.1 u e he x hx J _ hJ.1 hJ.2))
  have H₂:=actual_critical_taylorContinuousField_joint_law (by omega : 0<n+1) c
    (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.1.le) u (tangentFrame u hu)
    z hz (fun v=>transverseOffset_tangent u e he Q (x v)) (jointScoreTarget n (((n+1:ℕ):ℝ) • b))
  exact H₁.trans (H₂.trans (transverse_taylorContinuousField_law (by omega) hd μ hQ u hu e he x hx))

end
end SlowEquilibration.SphericalTAPCriticalBand

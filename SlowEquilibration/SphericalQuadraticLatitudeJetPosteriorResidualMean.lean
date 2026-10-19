-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetPalmFactorization
public import SlowEquilibration.GaussianCoefficientKernelScalarMGF
public import SlowEquilibration.SphericalTAPMixedBandExponent

@[expose] public section

/-! The genuine physical mixed score/zero-gradient posterior shifts the
nonquadratic latitude field by precisely the printed source mean. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory Function SphericalModel SphericalGaussianJet
open WholeFieldRegression GaussianRegression GaussianRegressionCovariance
open SphericalSequentialRegression SphericalCriticalLatitude IntrinsicHessianLaw
open SphericalTAPMixedBandExponent SphericalMarkedWindows
open SphericalTaylorRemainder
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 900000

private theorem originalLatitudePoint_overlap {N : ℕ} (hN : 0 < N)
    (a : ℝ) (u ω : Vector N) (hu : ‖u‖^2=(N:ℝ))
    (hω : inner ℝ ω u=0) :
    overlap (originalLatitudePoint a u ω) u=a := by
  unfold overlap originalLatitudePoint
  rw [inner_add_left,real_inner_smul_left,real_inner_smul_left,
    real_inner_self_eq_norm_sq,hu,hω]
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [mul_zero,add_zero]
  exact mul_div_cancel_right₀ a hn

theorem flatNonquadraticLatitudeField_physicalMixedPalm_mean
    {n : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (a : ℝ) (u ω : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (hω : inner ℝ ω u=0)
    (z : EuclideanSpace ℝ (Fin 2)) :
    let A := jointCLM (centerCoefficients (mixtureCoefficients μ) Q)
      u (tangentFrame u hu)
    flatNonquadraticLatitudeField μ a u ω
      (lift A (jointScoreTarget (n+1) (((n+2:ℕ):ℝ) • z))) =
      ((n+2:ℕ):ℝ)*sourceMixedMean μ Q (z 0) (z 1) a := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let S := scoreCLM c u
  let A := jointCLM c u (tangentFrame u hu)
  let b := ((n+2:ℕ):ℝ) • z
  have hc : ∀ p, 0 ≤ c p :=
    centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hS : Surjective S :=
    center_score_surjective (by omega) μ hQ hnp u hu
  have hA : Surjective A :=
    center_joint_surjective (by omega) μ hQ hnp u hu _
      (tangentFrame_orthonormal u hu) (tangentFrame_tangent u hu)
  have hker : A.ker ≤ S.ker := by
    rw [jointCLM_ker_intrinsic_score c u hu]
    exact fun _ hx => hx.2
  have hLift : lift A (jointScoreTarget (n+1) b)=lift S b := by
    rw [← jointCLM_score_lift c hc u hu hS]
    exact orthogonal_joint_lift S A hA hker b
  have hY : flatQuadraticLatitudeJet μ a u ω
      (lift A (jointScoreTarget (n+1) b))=0 := by
    exact lift_map_eq_zero_of_cross_zero A
      (flatQuadraticLatitudeJet μ a u ω)
      (flatQuadraticLatitudeJet_physicalJoint_cross_zero
        (by omega : 0 < n+2) μ hμ Q a u ω hω (tangentFrame u hu)) _
  have hb : b = ((n+2:ℕ):ℝ) • scorePairEquiv (z 0,z 1) := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [b,scorePairEquiv_apply]
  change (flatJetCLM (mixtureCoefficients μ) 0
      (originalLatitudePoint a u ω) (fun i => Fin.elim0 i) -
      flatQuadraticLatitudeJet μ a u ω)
      (lift A (jointScoreTarget (n+1) b)) = _
  rw [sub_apply,hY,sub_zero,hLift]
  change valueObservation (mixtureCoefficients μ)
    (originalLatitudePoint a u ω) (lift S b)=_
  rw [hb,original_value_physical_score_lift (by omega) μ hQ hnp u hu]
  rw [originalLatitudePoint_overlap (by omega) a u ω hu hω]
  rfl

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance

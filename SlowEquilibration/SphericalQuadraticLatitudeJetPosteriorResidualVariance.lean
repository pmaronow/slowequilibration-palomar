-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetPosteriorResidualMean
public import SlowEquilibration.SphericalCriticalLatitudeSourceTau

@[expose] public section

/-! Exact physical variance of the original nonquadratic latitude field
under genuine mixed score and tangent-gradient conditioning. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory Function SphericalModel SphericalGaussianJet
open WholeFieldRegression GaussianRegression GaussianRegressionCovariance
open SphericalSequentialRegression SphericalCriticalLatitude IntrinsicHessianLaw
open IntrinsicGradientRegression
open SphericalForm
open SphericalTAPMixedBandExponent SphericalTAPCriticalAnalyticNeighborhood
open SphericalTaylorRemainder SphericalTwoPointCovariance
open SphericalParisiConditionedLatitudeCovariance
open SphericalMarkedWindows ConditionedEntrance
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1200000

private theorem scalarCLM_norm_sq_eq {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E →L[ℝ] ℝ) : ‖f‖^2=f (f.adjoint 1) := by
  have hf : f=innerSL ℝ (f.adjoint 1) := by
    ext x
    have hh : f x=inner ℝ (f.adjoint 1) x := by
      rw [f.adjoint_inner_left]
      simp
    simpa only [innerSL_apply_apply] using hh
  rw [hf,innerSL_apply_norm,ContinuousLinearMap.adjoint_innerSL_apply]
  simp [innerSL_apply_apply]

private theorem originalLatitudePoint_norm_sq {N : ℕ}
    (a : ℝ) (ha : 0 ≤ 1-a^2) (u ω : Vector N)
    (hu : ‖u‖^2=(N:ℝ)) (hω : inner ℝ ω u=0)
    (hωn : ‖ω‖^2=(N:ℝ)) :
    ‖originalLatitudePoint a u ω‖^2=(N:ℝ) := by
  have hcross : inner ℝ u ω=0 := by rw [real_inner_comm]; exact hω
  unfold originalLatitudePoint
  rw [norm_add_sq_real]
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    real_inner_smul_left,real_inner_smul_right,hcross,mul_zero,add_zero,
    hu,hωn]
  rw [Real.sq_sqrt ha]
  ring

private theorem originalLatitudePoint_overlap_center {N : ℕ} (hN : 0 < N)
    (a : ℝ) (u ω : Vector N) (hu : ‖u‖^2=(N:ℝ))
    (hω : inner ℝ ω u=0) :
    overlap u (originalLatitudePoint a u ω)=a := by
  rw [overlap_comm]
  unfold overlap originalLatitudePoint
  rw [inner_add_left,real_inner_smul_left,real_inner_smul_left,
    real_inner_self_eq_norm_sq,hu,hω]
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [mul_zero,add_zero]
  exact mul_div_cancel_right₀ a hn

private theorem originalLatitudePoint_overlap_self {N : ℕ} (hN : 0 < N)
    (a : ℝ) (ha : 0 ≤ 1-a^2) (u ω : Vector N)
    (hu : ‖u‖^2=(N:ℝ)) (hω : inner ℝ ω u=0)
    (hωn : ‖ω‖^2=(N:ℝ)) :
    overlap (originalLatitudePoint a u ω)
      (originalLatitudePoint a u ω)=1 := by
  exact overlap_self hN _ (originalLatitudePoint_norm_sq a ha u ω hu hω hωn)

private theorem originalLatitudePoint_score_regression
    {n : ℕ} (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (a : ℝ) (u ω : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (hω : inner ℝ ω u=0) :
    let σ := originalLatitudePoint a u ω
    let f := valueObservation (mixtureCoefficients μ) σ
    let S := scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) u
    f (lift S (S (f.adjoint 1))) =
      ((n+2:ℕ):ℝ)*
        (sourceMixedCross μ Q a 0*valueTheta μ Q a+
          sourceMixedCross μ Q a 1*radialTheta μ Q a) := by
  dsimp only
  let σ := originalLatitudePoint a u ω
  let f := valueObservation (mixtureCoefficients μ) σ
  let S := scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) u
  have hcross := original_score_value_cross (by omega : 0 < n+2) μ hQ u σ
  rw [originalLatitudePoint_overlap_center (by omega) a u ω hu hω] at hcross
  change S (f.adjoint 1) = ((n+2:ℕ):ℝ) • sourceMixedCross μ Q a at hcross
  rw [hcross]
  have hb : sourceMixedCross μ Q a =
      scorePairEquiv (sourceMixedCross μ Q a 0,sourceMixedCross μ Q a 1) := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [scorePairEquiv_apply]
  rw [hb]
  have hmain := original_value_physical_score_lift
    (by omega : 0 < n+2) μ hQ hnp u hu σ
    (sourceMixedCross μ Q a 0) (sourceMixedCross μ Q a 1)
  have hov : overlap σ u=a := by
    rw [overlap_comm]
    exact originalLatitudePoint_overlap_center (by omega) a u ω hu hω
  rw [hov] at hmain
  change f (lift S (((n+2:ℕ):ℝ) •
    scorePairEquiv (sourceMixedCross μ Q a 0,sourceMixedCross μ Q a 1))) = _ at hmain
  rw [hmain]
  simp [scorePairEquiv_apply,mul_comm]

private theorem originalLatitudePoint_gradient_regression
    {n : ℕ} (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (a : ℝ) (ha : 0 ≤ 1-a^2) (u ω : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (hω : inner ℝ ω u=0)
    (hωn : ‖ω‖^2=((n+2:ℕ):ℝ)) :
    let σ := originalLatitudePoint a u ω
    let f := valueObservation (mixtureCoefficients μ) σ
    let Γ := intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) u
    f (lift Γ (Γ (f.adjoint 1))) =
      ((n+2:ℕ):ℝ)*sourceMixedGradientReduction μ Q a := by
  dsimp only
  let σ := originalLatitudePoint a u ω
  let f := valueObservation (mixtureCoefficients μ) σ
  let Γ := intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) u
  let v := (tangentPlane u).orthogonalProjectionOnto σ
  have hov : overlap u σ=a :=
    originalLatitudePoint_overlap_center (by omega) a u ω hu hω
  have hcross := original_gradient_value_cross (by omega : 0 < n+2) μ hQ u σ
  rw [hov] at hcross
  change Γ (f.adjoint 1) =
    (Real.sqrt Q*μ.xi1 (Real.sqrt Q*a)) • v at hcross
  rw [hcross,map_smul,map_smul]
  have hlift := original_gradient_lift_apply (by omega : 0 < n+2)
    μ hQ u hu σ v
  change f (lift Γ v)=tangentTheta μ Q (overlap σ u)*
    inner ℝ (v : Vector (n+2)) σ at hlift
  rw [overlap_comm,hov] at hlift
  rw [hlift]
  have hproj : inner ℝ (v : Vector (n+2)) σ =
      ((n+2:ℕ):ℝ)*(1-a^2) := by
    have hp := tangent_value_cross_inner (by omega : 0 < n+2) u hu σ σ
    rw [originalLatitudePoint_overlap_self (by omega) a ha u ω hu hω hωn,
      hov] at hp
    change inner ℝ (v : Vector (n+2)) (v : Vector (n+2)) = _ at hp
    have hv : inner ℝ (v : Vector (n+2)) σ =
        inner ℝ (v : Vector (n+2)) (v : Vector (n+2)) :=
      (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left v σ).symm
    rw [hv]
    nlinarith
  rw [hproj,tangentTheta_eq]
  unfold sourceMixedGradientReduction aScore
  have hqr : Q ≠ 0 := hQ.ne'
  have hs : (Real.sqrt Q)^2=Q := Real.sq_sqrt hQ.le
  have hxi : μ.xi1 Q ≠ 0 := (μ.xi1_pos hQ).ne'
  simp only [smul_eq_mul]
  field_simp [hqr,hxi]
  rw [hs]
  ring

theorem originalLatitudePoint_originalField_residualGram
    {n : ℕ} (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (a : ℝ) (ha : 0 ≤ 1-a^2) (u ω : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (hω : inner ℝ ω u=0)
    (hωn : ‖ω‖^2=((n+2:ℕ):ℝ)) :
    let σ := originalLatitudePoint a u ω
    let f := valueObservation (mixtureCoefficients μ) σ
    let A := jointCLM (centerCoefficients (mixtureCoefficients μ) Q)
      u (tangentFrame u hu)
    ‖f.comp (residual A)‖^2 =
      ((n+2:ℕ):ℝ)*sourceMixedVariance μ Q a := by
  dsimp only
  let σ := originalLatitudePoint a u ω
  let f := valueObservation (mixtureCoefficients μ) σ
  let S := scoreCLM (centerCoefficients (mixtureCoefficients μ) Q) u
  let Γ := intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) u
  let A := jointCLM (centerCoefficients (mixtureCoefficients μ) Q)
    u (tangentFrame u hu)
  have hself : f (f.adjoint 1) = ((n+2:ℕ):ℝ)*μ.xi 1 := by
    have h := value_value_coupling (by omega : 0 < n+2)
      (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ) σ σ
    rw [covariancePolynomial_mixture,
      originalLatitudePoint_overlap_self (by omega) a ha u ω hu hω hωn] at h
    exact h
  have hScore : f (lift S (S (f.adjoint 1))) =
      ((n+2:ℕ):ℝ)*
        (sourceMixedCross μ Q a 0*valueTheta μ Q a+
          sourceMixedCross μ Q a 1*radialTheta μ Q a) :=
    originalLatitudePoint_score_regression μ hQ hnp a u ω hu hω
  have hGrad : f (lift Γ (Γ (f.adjoint 1))) =
      ((n+2:ℕ):ℝ)*sourceMixedGradientReduction μ Q a :=
    originalLatitudePoint_gradient_regression μ hQ a ha u ω hu hω hωn
  rw [← criticalCoefficientResidual_eq_joint (n+1) μ hQ hnp u hu]
  rw [scalarCLM_norm_sq_eq,
    critical_residual_scalar_kernel (n+1) μ hQ hnp u hu f f,
    critical_residual_split (n+1) μ hQ u hu]
  simp only [map_sub]
  change f (f.adjoint 1)-f (lift S (S (f.adjoint 1)))-
      f (lift Γ (Γ (f.adjoint 1))) = _
  rw [hself,hScore,hGrad]
  unfold sourceMixedVariance
  ring

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance

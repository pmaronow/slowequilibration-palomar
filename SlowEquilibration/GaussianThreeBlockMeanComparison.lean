-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianThreeBlockComparison

@[expose] public section

/-! Three-block Guerra comparison from the actual disorder-averaged
pair covariance. The fixed perturbation block cancels from the derivative. -/
namespace SlowEquilibration.GaussianThreeBlockComparison
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

def pairKernelExpectation (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Fin 3) (θ : ℝ) (w : EuclideanSpace ℝ ι) : ℝ :=
  ∫ z : V × V,signedKernel L label z.1 z.2
    ∂(GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w).prod
      (GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w)

def meanPairKernel (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Fin 3) (θ : ℝ) : ℝ :=
  ∫ w,pairKernelExpectation ν L label θ w ∂SYK.standardGaussianMeasureOnEuclidean ι

theorem pairKernelExpectation_eq_coordinate_sum (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0≤K) (hb : ∀ᵐ v ∂ν,‖L v‖≤K)
    (label : ι → Fin 3) (θ : ℝ) (w : EuclideanSpace ℝ ι) :
    pairKernelExpectation ν L label θ w=
      ∑ i,covarianceSign label i*
        (GaussianSpinInterpolation.expectation ν (coordinateObservable L i) (rotatedLinear L label θ) w)^2 := by
  let G:=GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w
  let _:=GaussianSpinInterpolation.gibbsMeasure_probability ν _
    (rotatedLinear_measurable L hL label θ) (rotatedLinear_bound ν L hK hb label θ) w
  unfold pairKernelExpectation signedKernel
  rw [integral_finsetSum Finset.univ (fun i _ =>
    (((gibbsCoordinate_memLp ν L hL hK hb label θ w i).integrable (by norm_num)).mul_prod
      ((gibbsCoordinate_memLp ν L hL hK hb label θ w i).integrable (by norm_num))).const_mul _)]
  simp only [integral_const_mul,integral_prod_mul]
  simp_rw [GaussianSpinInterpolation.integral_gibbsMeasure ν _
    (rotatedLinear_measurable L hL label θ) (rotatedLinear_bound ν L hK hb label θ)]
  simp only [pow_two]

theorem pairKernelExpectation_gaussian_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0≤K) (hb : ∀ᵐ v ∂ν,‖L v‖≤K)
    (label : ι → Fin 3) (θ : ℝ) :
    Integrable (pairKernelExpectation ν L label θ) (SYK.standardGaussianMeasureOnEuclidean ι) := by
  rw [show pairKernelExpectation ν L label θ=(fun w => ∑ i,covarianceSign label i*
      (GaussianSpinInterpolation.expectation ν (coordinateObservable L i) (rotatedLinear L label θ) w)^2)
    from funext (pairKernelExpectation_eq_coordinate_sum ν L hL hK hb label θ)]
  apply integrable_finsetSum Finset.univ
  intro i _
  apply Integrable.const_mul
  have hp:=(coordinateObservable_bound ν L hb i).and (rotatedLinear_bound ν L hK hb label θ)
  have hc:=(GaussianSpinInterpolation.expectation_contDiff ν _ _
    (coordinateObservable_measurable L hL i) (rotatedLinear_measurable L hL label θ) hK hK hp).continuous
  apply Integrable.of_bound (hc.pow 2).aestronglyMeasurable (K^2)
  exact .of_forall fun w => by
    change ‖(GaussianSpinInterpolation.expectation ν (coordinateObservable L i) (rotatedLinear L label θ) w)^2‖≤K^2
    rw [norm_pow]
    exact (sq_le_sq₀ (norm_nonneg _) hK).mpr
      (GaussianSpinInterpolation.norm_expectation_le ν _ _
        (coordinateObservable_measurable L hL i) (rotatedLinear_measurable L hL label θ) hK hp w)

theorem meanSignedTrace_eq (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0≤K) (hb : ∀ᵐ v ∂ν,‖L v‖≤K)
    (label : ι → Fin 3) {d : ℝ} (hdiag : ∀ᵐ v ∂ν,signedKernel L label v v=d) (θ : ℝ) :
    (∫ w,(∑ i,covarianceSign label i*variance (coordinateObservable L i)
      (GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w))
      ∂SYK.standardGaussianMeasureOnEuclidean ι)=d-meanPairKernel ν L label θ := by
  have hp (w : EuclideanSpace ℝ ι) :
      (∑ i,covarianceSign label i*variance (coordinateObservable L i)
        (GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w))=
      d-pairKernelExpectation ν L label θ w := by
    let G:=GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w
    let _:=GaussianSpinInterpolation.gibbsMeasure_probability ν _
      (rotatedLinear_measurable L hL label θ) (rotatedLinear_bound ν L hK hb label θ) w
    rw [signedVarianceTrace_eq_kernels ν L hL hK hb label θ w]
    have hd : (∫ v,signedKernel L label v v ∂G)=d := by
      rw [integral_congr_ae (hdiag.filter_mono
        (GaussianSpinInterpolation.gibbsMeasure_absolutelyContinuous ν _ w).ae_le)]
      simp only [integral_const,probReal_univ,one_smul]
    rw [hd]
    rfl
  rw [integral_congr_ae (.of_forall hp),integral_sub (integrable_const d)
    (pairKernelExpectation_gaussian_integrable ν L hL hK hb label θ)]
  simp only [integral_const,probReal_univ,one_smul,meanPairKernel]

theorem gaussian_covariance_comparison_of_mean_pair (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0≤K) (hb : ∀ᵐ v ∂ν,‖L v‖≤K)
    (label : ι → Fin 3) {d c : ℝ} (hdiag : ∀ᵐ v ∂ν,signedKernel L label v v=d)
    (hpair : ∀ θ∈Icc (0:ℝ) (Real.pi/2),meanPairKernel ν L label θ≤c) :
    averagedRotatedLogPartition ν L label 0≤
      averagedRotatedLogPartition ν L label (Real.pi/2)+(c-d)/2 := by
  let F:=averagedRotatedLogPartition ν L label
  let G:=fun t => F t-(d-c)*(Real.sin t)^2/2
  have hF (t : ℝ):=averagedRotatedLogPartition_hasDerivAt_signedTrace ν L hL hK hb label t
  have hG (t : ℝ) : HasDerivAt G
      (Real.sin t*Real.cos t*(d-meanPairKernel ν L label t)-(d-c)*Real.sin t*Real.cos t) t := by
    have hf:=hF t
    rw [meanSignedTrace_eq ν L hL hK hb label hdiag t] at hf
    convert hf.sub ((((Real.hasDerivAt_sin t).pow 2).const_mul (d-c)).div_const 2) using 1
    ring
  have hmono : MonotoneOn G (Icc (0:ℝ) (Real.pi/2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact (show Differentiable ℝ G from fun t => (hG t).differentiableAt).continuous.continuousOn
    · intro t ht
      exact (hG t).differentiableAt.differentiableWithinAt
    · intro t ht
      have hθ : t∈Icc (0:ℝ) (Real.pi/2) := interior_subset ht
      rw [(hG t).deriv]
      have hs:0≤Real.sin t:=Real.sin_nonneg_of_mem_Icc ⟨hθ.1,hθ.2.trans (by linarith [Real.pi_pos])⟩
      have hc:0≤Real.cos t:=Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1,Real.pi_pos],hθ.2⟩
      nlinarith [mul_nonneg (mul_nonneg hs hc) (sub_nonneg.mpr (hpair t hθ))]
  have h:=hmono ⟨le_rfl,by positivity⟩ ⟨by positivity,le_rfl⟩ (by positivity : (0:ℝ)≤Real.pi/2)
  dsimp only [G] at h
  simp only [Real.sin_zero,Real.sin_pi_div_two,zero_pow (by norm_num : 2≠0),one_pow,
    mul_zero] at h
  dsimp only [F] at h
  linarith

end
end SlowEquilibration.GaussianThreeBlockComparison

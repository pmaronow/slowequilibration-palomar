-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianThreeBlockMeanComparison

@[expose] public section

/-! # Three-block comparison with the actual external parameter average

The external parameter measure remains outside the Gibbs partition.
The comparison uses its true averaged replica covariance before the
interpolation inequality, so no single parameter is selected.
-/
namespace SlowEquilibration.GaussianThreeBlockComparison
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X V ι : Type*} [MeasurableSpace X] [MeasurableSpace V]
  [Fintype ι] [DecidableEq ι]

omit [MeasurableSpace X] [DecidableEq ι] in
theorem norm_averagedRotatedLogPartition_le_gaussianNorm
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν,‖L v‖ ≤ K) (label : ι → Fin 3) (θ : ℝ) :
    ‖averagedRotatedLogPartition ν L label θ‖ ≤
      K*(∫ w : EuclideanSpace ℝ ι,‖w‖ ∂SYK.standardGaussianMeasureOnEuclidean ι) := by
  unfold averagedRotatedLogPartition
  calc
    _ ≤ ∫ w,‖GaussianSpinInterpolation.logPartition ν L (rotation label θ w)‖
        ∂SYK.standardGaussianMeasureOnEuclidean ι := norm_integral_le_integral_norm _
    _ ≤ ∫ w,K*‖w‖ ∂SYK.standardGaussianMeasureOnEuclidean ι := by
      apply integral_mono_ae (logPartition_rotated_gaussian_integrable ν L hL hK hb label θ).norm
        ((GaussianSpinInterpolation.gaussian_norm_integrable (ι := ι)).const_mul K)
      exact .of_forall fun w => by
        dsimp only
        rw [Real.norm_eq_abs]
        exact (GaussianSpinInterpolation.abs_logPartition_le ν L hL hb _).trans
          (mul_le_mul_of_nonneg_left (rotation_norm_le label θ w) hK)
    _ = _ := integral_const_mul _ _

omit [MeasurableSpace X] [DecidableEq ι] in
theorem norm_deriv_averagedRotatedLogPartition_le_gaussianNorm
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν,‖L v‖ ≤ K) (label : ι → Fin 3) (θ : ℝ) :
    ‖deriv (averagedRotatedLogPartition ν L label) θ‖ ≤
      K*(∫ w : EuclideanSpace ℝ ι,‖w‖ ∂SYK.standardGaussianMeasureOnEuclidean ι) := by
  rw [(averagedRotatedLogPartition_hasDerivAt ν L hL hK hb label θ).deriv]
  have hc : Continuous (fun w => GaussianSpinInterpolation.score ν L
      (rotation label θ w) (rotationDerivative label θ w)) :=
    ((GaussianSpinInterpolation.score_continuous ν L hL hK hb).comp
      (rotation label θ).continuous).clm_apply (rotationDerivative label θ).continuous
  have hbscore (w : EuclideanSpace ℝ ι) :
      ‖GaussianSpinInterpolation.score ν L (rotation label θ w) (rotationDerivative label θ w)‖ ≤ K*‖w‖ :=
    ((GaussianSpinInterpolation.score ν L (rotation label θ w)).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (GaussianSpinInterpolation.norm_score_le ν L hL hK hb _)
        (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left (rotationDerivative_norm_le label θ w) hK))
  have hi := ((GaussianSpinInterpolation.gaussian_norm_integrable (ι := ι)).const_mul K).mono'
    hc.aestronglyMeasurable (.of_forall hbscore)
  calc
    _ ≤ ∫ w,‖GaussianSpinInterpolation.score ν L (rotation label θ w) (rotationDerivative label θ w)‖
        ∂SYK.standardGaussianMeasureOnEuclidean ι := norm_integral_le_integral_norm _
    _ ≤ ∫ w,K*‖w‖ ∂SYK.standardGaussianMeasureOnEuclidean ι :=
      integral_mono_ae hi.norm ((GaussianSpinInterpolation.gaussian_norm_integrable (ι := ι)).const_mul K)
        (.of_forall hbscore)
    _ = _ := integral_const_mul _ _

def parameterAveragedPressure (ρ : Measure X) (ν : Measure V)
    (L : X → V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (label : ι → Fin 3) (θ : ℝ) : ℝ :=
  ∫ x,averagedRotatedLogPartition ν (L x) label θ ∂ρ

def parameterAveragedPairKernel (ρ : Measure X) (ν : Measure V)
    (L : X → V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (label : ι → Fin 3) (θ : ℝ) : ℝ :=
  ∫ x,meanPairKernel ν (L x) label θ ∂ρ

/-- Genuine differentiation of the quenched external parameter average.
The only parameter regularity inputs concern the literal pressure and
replica-integral measurability; all domination follows from the true
uniform feature norm. -/
theorem parameterAveragedPressure_hasDerivAt (ρ : Measure X) [IsProbabilityMeasure ρ]
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : X → V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : ∀ x,Measurable (L x))
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ x ∂ρ,∀ᵐ v ∂ν,‖L x v‖ ≤ K)
    (label : ι → Fin 3) {d : ℝ}
    (hdiag : ∀ᵐ x ∂ρ,∀ᵐ v ∂ν,signedKernel (L x) label v v=d)
    (hPm : ∀ θ : ℝ,AEStronglyMeasurable (fun x => averagedRotatedLogPartition ν (L x) label θ) ρ)
    (hPi : ∀ θ : ℝ,Integrable (fun x => meanPairKernel ν (L x) label θ) ρ) (θ : ℝ) :
    HasDerivAt (parameterAveragedPressure ρ ν L label)
      (Real.sin θ*Real.cos θ*(d-parameterAveragedPairKernel ρ ν L label θ)) θ := by
  let B := K*(∫ w : EuclideanSpace ℝ ι,‖w‖ ∂SYK.standardGaussianMeasureOnEuclidean ι)
  let D := fun t x => Real.sin t*Real.cos t*(d-meanPairKernel ν (L x) label t)
  have hPint (t : ℝ) : Integrable (fun x => averagedRotatedLogPartition ν (L x) label t) ρ := by
    apply Integrable.of_bound (hPm t) B
    filter_upwards [hb] with x hx
    exact norm_averagedRotatedLogPartition_le_gaussianNorm ν (L x) (hL x) hK hx label t
  have hd : ∀ᵐ x ∂ρ,∀ t : ℝ,
      HasDerivAt (averagedRotatedLogPartition ν (L x) label) (D t x) t := by
    filter_upwards [hb,hdiag] with x hx hdx t
    have hh := averagedRotatedLogPartition_hasDerivAt_signedTrace ν (L x) (hL x) hK hx label t
    rw [meanSignedTrace_eq ν (L x) (hL x) hK hx label hdx t] at hh
    exact hh
  have hDb : ∀ᵐ x ∂ρ,∀ t∈(univ : Set ℝ),‖D t x‖ ≤ B := by
    filter_upwards [hb,hd] with x hx hdx t _
    rw [← (hdx t).deriv]
    exact norm_deriv_averagedRotatedLogPartition_le_gaussianNorm ν (L x) (hL x) hK hx label t
  have hDmeas : AEStronglyMeasurable (D θ) ρ :=
    ((aestronglyMeasurable_const.sub (hPi θ).aestronglyMeasurable).const_mul (Real.sin θ*Real.cos θ))
  have hh := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ρ) (s := univ)
    (F := fun t x => averagedRotatedLogPartition ν (L x) label t) (F' := D)
    (bound := fun _ => B) (by simp) (.of_forall hPm) (hPint θ) hDmeas hDb
    (integrable_const B) (hd.mono fun x hx t _ => hx t)).2
  convert hh using 1
  · rfl
  · dsimp only [D]
    rw [integral_const_mul,integral_sub (integrable_const d) (hPi θ)]
    simp only [integral_const,probReal_univ,one_smul,parameterAveragedPairKernel]

/-- True three-block comparison after averaging all external parameters.
The replica covariance is averaged before the interpolation estimate. -/
theorem gaussian_covariance_comparison_of_parameter_mean_pair
    (ρ : Measure X) [IsProbabilityMeasure ρ] (ν : Measure V) [IsProbabilityMeasure ν]
    (L : X → V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : ∀ x,Measurable (L x))
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ x ∂ρ,∀ᵐ v ∂ν,‖L x v‖ ≤ K)
    (label : ι → Fin 3) {d c : ℝ}
    (hdiag : ∀ᵐ x ∂ρ,∀ᵐ v ∂ν,signedKernel (L x) label v v=d)
    (hPm : ∀ θ : ℝ,AEStronglyMeasurable (fun x => averagedRotatedLogPartition ν (L x) label θ) ρ)
    (hPi : ∀ θ : ℝ,Integrable (fun x => meanPairKernel ν (L x) label θ) ρ)
    (hpair : ∀ θ∈Icc (0 : ℝ) (Real.pi/2),parameterAveragedPairKernel ρ ν L label θ ≤ c) :
    parameterAveragedPressure ρ ν L label 0 ≤
      parameterAveragedPressure ρ ν L label (Real.pi/2)+(c-d)/2 := by
  let F := parameterAveragedPressure ρ ν L label
  let G := fun t => F t-(d-c)*(Real.sin t)^2/2
  have hF (t : ℝ) := parameterAveragedPressure_hasDerivAt ρ ν L hL hK hb label hdiag hPm hPi t
  have hG (t : ℝ) : HasDerivAt G
      (Real.sin t*Real.cos t*(d-parameterAveragedPairKernel ρ ν L label t)-
        (d-c)*Real.sin t*Real.cos t) t := by
    convert (hF t).sub ((((Real.hasDerivAt_sin t).pow 2).const_mul (d-c)).div_const 2) using 1
    ring
  have hmono : MonotoneOn G (Icc (0 : ℝ) (Real.pi/2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact (show Differentiable ℝ G from fun t => (hG t).differentiableAt).continuous.continuousOn
    · intro t _
      exact (hG t).differentiableAt.differentiableWithinAt
    · intro t ht
      have hθ : t∈Icc (0 : ℝ) (Real.pi/2) := interior_subset ht
      rw [(hG t).deriv]
      have hs : 0 ≤ Real.sin t := Real.sin_nonneg_of_mem_Icc ⟨hθ.1,hθ.2.trans (by linarith [Real.pi_pos])⟩
      have hc : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1,Real.pi_pos],hθ.2⟩
      nlinarith [mul_nonneg (mul_nonneg hs hc) (sub_nonneg.mpr (hpair t hθ))]
  have h := hmono ⟨le_rfl,by positivity⟩ ⟨by positivity,le_rfl⟩ (by positivity : (0 : ℝ) ≤ Real.pi/2)
  dsimp only [G] at h
  simp only [Real.sin_zero,Real.sin_pi_div_two,zero_pow (by norm_num : 2≠0),one_pow,mul_zero] at h
  dsimp only [F] at h
  linarith

end
end SlowEquilibration.GaussianThreeBlockComparison

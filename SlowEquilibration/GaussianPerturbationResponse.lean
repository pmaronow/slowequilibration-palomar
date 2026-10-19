-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianPerturbationSelfAveraging

@[expose] public section

/-! # Actual partial-coordinate Gaussian variance response

Gaussian IBP for the selected coordinate gives the literal perturbation mean
response as parameter times Gibbs variance. No response identity or overlap
positivity is assumed.
-/

namespace SlowEquilibration.GaussianPerturbationResponse
noncomputable section
open MeasureTheory Set
open scoped Topology BigOperators
open GaussianSpinInterpolation GaussianSpinComparison GaussianPerturbationParameter
  GaussianPerturbationSelfAveraging

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

theorem coordinateMask_single (label : ι → Bool) (b : Bool) (i : ι) :
    coordinateMask label b (EuclideanSpace.single i 1) =
      (if label i=b then (1 : ℝ) else 0) • EuclideanSpace.single i 1 := by
  ext j
  by_cases hji : j=i
  · subst j
    by_cases hi : label i=b <;> simp [coordinateMask,diagonal_apply,hi]
  · by_cases hi : label i=b <;> simp [coordinateMask,diagonal_apply,hji,hi]

theorem parameterOperator_single_of_active (label : ι → Bool) (x : ℝ) (i : ι)
    (hi : label i=true) :
    parameterOperator label x (EuclideanSpace.single i 1)=x • EuclideanSpace.single i 1 := by
  rw [parameterOperator,add_apply,smul_apply,
    coordinateMask_single,coordinateMask_single]
  simp [hi]

theorem parameterLinear_single_of_active (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Bool) (x : ℝ) (i : ι) (hi : label i=true) (v : V) :
    parameterLinear L label x v (EuclideanSpace.single i 1)=x*coordinateObservable L i v := by
  simp only [parameterLinear,ContinuousLinearMap.comp_apply,parameterOperator_single_of_active label x i hi,
    map_smul,smul_eq_mul,coordinateObservable]

def coordinateVariance (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Bool) (x : ℝ) (w : EuclideanSpace ℝ ι) (i : ι) : ℝ :=
  ProbabilityTheory.variance (coordinateObservable L i)
    (gibbsMeasure ν (parameterLinear L label x) w)

theorem coordinateVariance_eq (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (x : ℝ) (w : EuclideanSpace ℝ ι) (i : ι) :
    coordinateVariance ν L label x w i =
      expectation ν (fun v => (coordinateObservable L i v)^2) (parameterLinear L label x) w-
        (expectation ν (coordinateObservable L i) (parameterLinear L label x) w)^2 := by
  symm
  exact expectation_variance ν _ _ (coordinateObservable_measurable L hL i)
    (parameterLinear_measurable L hL label x)
    ((coordinateObservable_bound ν L hb i).and (parameterLinear_bound ν L hK hb label x)) w

theorem coordinateVariance_mem_Icc (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (x : ℝ) (w : EuclideanSpace ℝ ι) (i : ι) :
    coordinateVariance ν L label x w i ∈ Icc 0 (K^2) := by
  refine ⟨ProbabilityTheory.variance_nonneg _ _,?_⟩
  rw [coordinateVariance_eq ν L hL hK hb]
  have hρb : ∀ᵐ v ∂ν, |(coordinateObservable L i v)^2| ≤ K^2 := by
    filter_upwards [coordinateObservable_bound ν L hb i] with v hv
    simpa only [abs_pow,sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).mpr hv
  have hh := norm_expectation_le ν (fun v => (coordinateObservable L i v)^2)
    (parameterLinear L label x) ((coordinateObservable_measurable L hL i).pow_const 2)
    (parameterLinear_measurable L hL label x) (sq_nonneg K)
    (hρb.and (parameterLinear_bound ν L hK hb label x)) w
  rw [Real.norm_eq_abs] at hh
  exact sub_le_iff_le_add.mpr ((le_abs_self _).trans hh |>.trans (le_add_of_nonneg_right (sq_nonneg _)))

theorem coordinateVariance_gaussian_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (x : ℝ) (i : ι) :
    Integrable (fun w => coordinateVariance ν L label x w i)
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hbound := (coordinateObservable_bound ν L hb i).and (parameterLinear_bound ν L hK hb label x)
  have hbound2 : ∀ᵐ v ∂ν, |(coordinateObservable L i v)^2| ≤ K^2 ∧
      ‖parameterLinear L label x v‖ ≤ (1+|x|)*K := by
    filter_upwards [hbound] with v hv
    exact ⟨by simpa only [abs_pow,sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).mpr hv.1,hv.2⟩
  have hc1 := (expectation_contDiff ν (coordinateObservable L i) (parameterLinear L label x)
    (coordinateObservable_measurable L hL i) (parameterLinear_measurable L hL label x) hK
    (mul_nonneg (by positivity) hK) hbound).continuous
  have hc2 := (expectation_contDiff ν (fun v => (coordinateObservable L i v)^2) (parameterLinear L label x)
    ((coordinateObservable_measurable L hL i).pow_const 2) (parameterLinear_measurable L hL label x)
    (sq_nonneg K) (mul_nonneg (by positivity) hK) hbound2).continuous
  have heq : (fun w => coordinateVariance ν L label x w i) =
      fun w => expectation ν (fun v => (coordinateObservable L i v)^2) (parameterLinear L label x) w-
        (expectation ν (coordinateObservable L i) (parameterLinear L label x) w)^2 :=
    funext fun w => coordinateVariance_eq ν L hL hK hb label x w i
  have hc : Continuous (fun w => coordinateVariance ν L label x w i) := by
    rw [heq];exact hc2.sub (hc1.pow 2)
  apply Integrable.of_bound hc.aestronglyMeasurable (K^2)
  exact .of_forall fun w => by
    rw [Real.norm_eq_abs,abs_of_nonneg (coordinateVariance_mem_Icc ν L hL hK hb label x w i).1]
    exact (coordinateVariance_mem_Icc ν L hL hK hb label x w i).2

theorem coordinate_energy_gaussian_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (x : ℝ) (i : ι) :
    Integrable (fun w => w i*expectation ν (coordinateObservable L i) (parameterLinear L label x) w)
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hb' := (coordinateObservable_bound ν L hb i).and (parameterLinear_bound ν L hK hb label x)
  have hc : Continuous (fun w : EuclideanSpace ℝ ι =>
      w i*expectation ν (coordinateObservable L i) (parameterLinear L label x) w) :=
    (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i).mul
      (expectation_contDiff ν _ _ (coordinateObservable_measurable L hL i)
        (parameterLinear_measurable L hL label x) hK (mul_nonneg (by positivity) hK) hb').continuous
  apply (gaussian_norm_integrable (ι := ι) |>.const_mul K).mono' hc.aestronglyMeasurable
  exact .of_forall fun w => by
    rw [norm_mul]
    exact (mul_le_mul (PiLp.norm_apply_le w i)
      (norm_expectation_le ν _ _ (coordinateObservable_measurable L hL i)
        (parameterLinear_measurable L hL label x) hK hb' w) (norm_nonneg _) (norm_nonneg _)).trans_eq (by ring)

/-- The genuine selected-coordinate mean response, from actual Gaussian IBP. -/
theorem coordinate_response (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (x : ℝ) (i : ι) (hi : label i=true) :
    (∫ w,w i*expectation ν (coordinateObservable L i) (parameterLinear L label x) w
      ∂SYK.standardGaussianMeasureOnEuclidean ι) =
      x*(∫ w,coordinateVariance ν L label x w i ∂SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hbound := (coordinateObservable_bound ν L hb i).and (parameterLinear_bound ν L hK hb label x)
  have h := gaussian_expectation_ibp ν (coordinateObservable L i) (parameterLinear L label x)
    (coordinateObservable_measurable L hL i) (parameterLinear_measurable L hL label x) hK
    (mul_nonneg (by positivity) hK) hbound (EuclideanSpace.single i 1)
  simp only [EuclideanSpace.inner_single_left,one_mul,conj_trivial] at h
  rw [h,← integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun w => by
    dsimp only
    rw [expectationDerivative_apply ν _ _ (coordinateObservable_measurable L hL i)
      (parameterLinear_measurable L hL label x) hbound,
      coordinateVariance_eq ν L hL hK hb]
    simp_rw [parameterLinear_single_of_active L label x i hi]
    have hprod : (fun v => coordinateObservable L i v*(x*coordinateObservable L i v)) =
        fun v => x*(coordinateObservable L i v)^2 := by funext v;ring
    rw [hprod,expectation_const_mul,expectation_const_mul]
    ring

def varianceTrace (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Bool) (x : ℝ) (w : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, if label i=true then coordinateVariance ν L label x w i else 0

theorem parameterScore_eq_sum (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Bool)
    (x : ℝ) (w : EuclideanSpace ℝ ι) :
    parameterScore ν L label w x = ∑ i, if label i=true then
      w i*expectation ν (coordinateObservable L i) (parameterLinear L label x) w else 0 := by
  rw [parameterScore,score_eq_coordinate_sum ν L hL hb]
  apply Finset.sum_congr rfl
  intro i _
  rw [coordinateMask,diagonal_apply]
  by_cases hi : label i=true
  · simp only [hi,ite_true,one_mul]
    rfl
  · simp [hi]

/-- The actual Gaussian mean energy is parameter times actual thermal
variance trace. -/
theorem meanScore_response (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (x : ℝ) :
    meanScore ν L label x =
      x*(∫ w,varianceTrace ν L label x w ∂SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hi1 (i : ι) : Integrable (fun w => if label i=true then
      w i*expectation ν (coordinateObservable L i) (parameterLinear L label x) w else 0)
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
    by_cases hi : label i=true
    · simpa only [hi,ite_true] using coordinate_energy_gaussian_integrable ν L hL hK hb label x i
    · simp [hi]
  have hi2 (i : ι) : Integrable (fun w => if label i=true then coordinateVariance ν L label x w i else 0)
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
    by_cases hi : label i=true
    · simpa only [hi,ite_true] using coordinateVariance_gaussian_integrable ν L hL hK hb label x i
    · simp [hi]
  unfold meanScore varianceTrace
  simp_rw [parameterScore_eq_sum ν L hL hb]
  rw [integral_finsetSum Finset.univ (fun i _ => hi1 i),
    integral_finsetSum Finset.univ (fun i _ => hi2 i),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : label i=true
  · simp only [hi,ite_true]
    exact coordinate_response ν L hL hK hb label x i hi
  · simp [hi]

theorem varianceTrace_mem_Icc (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K a : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool)
    (hdiag : ∀ᵐ v ∂ν, (∑ i, if label i=true then (coordinateObservable L i v)^2 else 0) ≤ a)
    (x : ℝ) (w : EuclideanSpace ℝ ι) : varianceTrace ν L label x w ∈ Icc 0 a := by
  let LX := parameterLinear L label x
  have hLX := parameterLinear_measurable L hL label x
  have hLXb := parameterLinear_bound ν L hK hb label x
  let G := gibbsMeasure ν LX w
  have : IsProbabilityMeasure G := gibbsMeasure_probability ν LX hLX hLXb w
  have hac : G ≪ ν := gibbsMeasure_absolutelyContinuous ν LX w
  have hi (i : ι) : Integrable (fun v => (coordinateObservable L i v)^2) G := by
    have hm : MemLp (coordinateObservable L i) 2 G :=
      MemLp.of_bound (coordinateObservable_measurable L hL i).aestronglyMeasurable K
        (((coordinateObservable_bound ν L hb i).mono
          fun v hv => by simpa only [Real.norm_eq_abs] using hv).filter_mono hac.ae_le)
    exact hm.integrable_sq
  have his (i : ι) : Integrable (fun v => if label i=true then (coordinateObservable L i v)^2 else 0) G := by
    by_cases hi' : label i=true
    · simpa only [hi',ite_true] using hi i
    · simp [hi']
  constructor
  · exact Finset.sum_nonneg fun i _ => by
      by_cases hi' : label i=true
      · simp only [hi',ite_true]
        exact ProbabilityTheory.variance_nonneg _ _
      · simp [hi']
  · calc
      _ ≤ ∑ i, if label i=true then
          expectation ν (fun v => (coordinateObservable L i v)^2) LX w else 0 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi' : label i=true
        · simp only [hi',ite_true]
          rw [coordinateVariance_eq ν L hL hK hb]
          exact sub_le_self _ (sq_nonneg _)
        · simp [hi']
      _ = ∑ i, ∫ v, (if label i=true then (coordinateObservable L i v)^2 else 0) ∂G := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi' : label i=true
        · simp only [hi',ite_true]
          exact (integral_gibbsMeasure ν LX hLX hLXb w _).symm
        · simp [hi']
      _ = ∫ v, ∑ i, if label i=true then (coordinateObservable L i v)^2 else 0 ∂G :=
        (integral_finsetSum Finset.univ (fun i _ => his i)).symm
      _ ≤ ∫ _v,a ∂G := integral_mono_ae (integrable_finsetSum Finset.univ (fun i _ => his i))
        (integrable_const a) (hdiag.filter_mono hac.ae_le)
      _ = a := by simp

/-- The absolute genuine mean perturbation energy is controlled by the
literal selected-coordinate diagonal feature energy. -/
theorem abs_meanScore_le (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K a : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool)
    (hdiag : ∀ᵐ v ∂ν, (∑ i, if label i=true then (coordinateObservable L i v)^2 else 0) ≤ a)
    (x : ℝ) : |meanScore ν L label x| ≤ |x| * a := by
  have htrace := norm_integral_le_of_norm_le_const (μ := SYK.standardGaussianMeasureOnEuclidean ι)
    (.of_forall fun w => by
      rw [Real.norm_eq_abs,abs_of_nonneg (varianceTrace_mem_Icc ν L hL hK hb label hdiag x w).1]
      exact (varianceTrace_mem_Icc ν L hL hK hb label hdiag x w).2)
  rw [meanScore_response ν L hL hK hb label x,abs_mul]
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
    mul_le_mul_of_nonneg_left htrace (abs_nonneg x)

end
end SlowEquilibration.GaussianPerturbationResponse

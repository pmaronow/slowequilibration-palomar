-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianSpinComparison
public import SlowEquilibration.GaussianSpinHessian
public import SlowEquilibration.GaussianPerturbationFluctuation
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-! # Actual Gaussian-coordinate perturbation parameter calculus

Only selected Gaussian coordinates are multiplied by the real parameter.
The literal integral log-partition has first derivative equal to perturbation
energy and second derivative equal to its actual Gibbs thermal variance.
Its Gaussian mean is differentiated by a proved global Gaussian-norm envelope.
-/

namespace SlowEquilibration.GaussianPerturbationParameter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open GaussianSpinInterpolation GaussianSpinComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

def parameterOperator (label : ι → Bool) (x : ℝ) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  coordinateMask label false+x • coordinateMask label true

theorem coordinateMask_norm_le (label : ι → Bool) (b : Bool) (w : EuclideanSpace ℝ ι) :
    ‖coordinateMask label b w‖ ≤ ‖w‖ := by
  simpa only [coordinateMask,one_mul] using diagonal_norm_le
    (fun i => if label i=b then (1 : ℝ) else 0) zero_le_one
    (fun _ => by split_ifs <;> norm_num) w

theorem parameterOperator_norm_le (label : ι → Bool) (x : ℝ) (w : EuclideanSpace ℝ ι) :
    ‖parameterOperator label x w‖ ≤ (1+|x|)*‖w‖ := by
  calc
    _ ≤ ‖coordinateMask label false w‖+‖x • coordinateMask label true w‖ := norm_add_le _ _
    _ ≤ ‖w‖+|x| * ‖w‖ := by rw [norm_smul,Real.norm_eq_abs];gcongr <;> apply coordinateMask_norm_le
    _ = _ := by ring

theorem parameterOperator_hasDerivAt (label : ι → Bool) (w : EuclideanSpace ℝ ι) (x : ℝ) :
    HasDerivAt (fun y => parameterOperator label y w) (coordinateMask label true w) x := by
  change HasDerivAt (fun y => coordinateMask label false w+y • coordinateMask label true w)
    (coordinateMask label true w) x
  simpa only [id_eq,zero_add,one_smul] using
    ((hasDerivAt_id x).smul_const (coordinateMask label true w)).const_add
      (coordinateMask label false w)

def parameterLogPartition (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Bool) (w : EuclideanSpace ℝ ι) (x : ℝ) : ℝ :=
  logPartition ν L (parameterOperator label x w)

def parameterScore (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Bool) (w : EuclideanSpace ℝ ι) (x : ℝ) : ℝ :=
  score ν L (parameterOperator label x w) (coordinateMask label true w)

def parameterVariance (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Bool) (w : EuclideanSpace ℝ ι) (x : ℝ) : ℝ :=
  ProbabilityTheory.variance (fun v => L v (coordinateMask label true w))
    (gibbsMeasure ν L (parameterOperator label x w))

/-- The actual perturbation energy is the ordinary derivative. -/
theorem parameterLogPartition_hasDerivAt (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (w : EuclideanSpace ℝ ι) (x : ℝ) :
    HasDerivAt (parameterLogPartition ν L label w) (parameterScore ν L label w x) x := by
  change HasDerivAt (fun y => logPartition ν L (parameterOperator label y w))
    (score ν L (parameterOperator label x w) (coordinateMask label true w)) x
  simpa only [Function.comp_def] using
    (logPartition_hasFDerivAt ν L hL hK hb (parameterOperator label x w)).comp_hasDerivAt x
      (parameterOperator_hasDerivAt label w x)

/-- The perturbation-energy derivative is the literal thermal variance. -/
theorem parameterScore_hasDerivAt (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (w : EuclideanSpace ℝ ι) (x : ℝ) :
    HasDerivAt (parameterScore ν L label w) (parameterVariance ν L label w x) x := by
  let d := coordinateMask label true w
  let z := parameterOperator label x w
  have hd := ((ContinuousLinearMap.apply ℝ ℝ d).hasFDerivAt.comp z
    (score_hasFDerivAt ν L hL hK hb z)).comp_hasDerivAt x
      (parameterOperator_hasDerivAt label w x)
  have hv : hessian ν L z d d = parameterVariance ν L label w x := by
    rw [hessian_apply_covariance ν L hL hK hb]
    have hρ : Measurable (fun v => L v d) :=
      (ContinuousLinearMap.apply ℝ ℝ d).continuous.measurable.comp hL
    simpa only [parameterVariance,d,z,pow_two] using
      expectation_variance ν (fun v => L v d) L hρ hL (directionalObservable_bound ν L hb d) z
  change HasDerivAt (fun y => score ν L (parameterOperator label y w) d)
    (hessian ν L z d d) x at hd
  rw [hv] at hd
  exact hd

theorem parameter_deriv_eq_score (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (w : EuclideanSpace ℝ ι) :
    deriv (parameterLogPartition ν L label w) = parameterScore ν L label w :=
  funext fun x => (parameterLogPartition_hasDerivAt ν L hL hK hb label w x).deriv

/-- Convexity of the actual perturbation log-partition is derived from
thermal variance nonnegativity, not stipulated. -/
theorem parameterLogPartition_convex (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (w : EuclideanSpace ℝ ι) :
    ConvexOn ℝ univ (parameterLogPartition ν L label w) := by
  have hdiff : Differentiable ℝ (parameterLogPartition ν L label w) :=
    fun x => (parameterLogPartition_hasDerivAt ν L hL hK hb label w x).differentiableAt
  apply convexOn_of_deriv2_nonneg convex_univ hdiff.continuous.continuousOn hdiff.differentiableOn
  · rw [parameter_deriv_eq_score ν L hL hK hb label w]
    exact (show Differentiable ℝ (parameterScore ν L label w) from
      fun x => (parameterScore_hasDerivAt ν L hL hK hb label w x).differentiableAt).differentiableOn
  · intro x _
    change 0 ≤ deriv (deriv (parameterLogPartition ν L label w)) x
    rw [parameter_deriv_eq_score ν L hL hK hb label w,
      (parameterScore_hasDerivAt ν L hL hK hb label w x).deriv]
    exact ProbabilityTheory.variance_nonneg _ _

theorem parameterLogPartition_gaussian_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (x : ℝ) :
    Integrable (fun w => parameterLogPartition ν L label w x)
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hc := (logPartition_contDiff ν L hL hK hb).continuous.comp (parameterOperator label x).continuous
  apply (gaussian_norm_integrable (ι := ι) |>.const_mul (K*(1+|x|))).mono' hc.aestronglyMeasurable
  exact .of_forall fun w => by
    rw [Real.norm_eq_abs]
    exact (abs_logPartition_le ν L hL hb _).trans
      ((mul_le_mul_of_nonneg_left (parameterOperator_norm_le label x w) hK).trans_eq (by ring))

def parameterMean (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Bool) (x : ℝ) : ℝ :=
  ∫ w,parameterLogPartition ν L label w x ∂SYK.standardGaussianMeasureOnEuclidean ι

/-- The Gaussian mean is genuinely differentiated by a uniform Gaussian
norm envelope, for every value of the perturbation parameter. -/
theorem parameterMean_hasDerivAt (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (x : ℝ) :
    HasDerivAt (parameterMean ν L label)
      (∫ w,parameterScore ν L label w x ∂SYK.standardGaussianMeasureOnEuclidean ι) x := by
  have hc : Continuous (fun w => parameterScore ν L label w x) :=
    ((score_continuous ν L hL hK hb).comp (parameterOperator label x).continuous).clm_apply
      (coordinateMask label true).continuous
  have hbound : ∀ᵐ w ∂SYK.standardGaussianMeasureOnEuclidean ι, ∀ y ∈ (univ : Set ℝ),
      ‖parameterScore ν L label w y‖ ≤ K*‖w‖ := .of_forall fun w y _ =>
    ((score ν L (parameterOperator label y w)).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (norm_score_le ν L hL hK hb _) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (coordinateMask_norm_le label true w) hK))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := SYK.standardGaussianMeasureOnEuclidean ι) (s := univ)
    (F := fun y w => parameterLogPartition ν L label w y)
    (F' := fun y w => parameterScore ν L label w y) (bound := fun w => K*‖w‖) (by simp)
    (.of_forall fun y => (parameterLogPartition_gaussian_integrable ν L hL hK hb label y).aestronglyMeasurable)
    (parameterLogPartition_gaussian_integrable ν L hL hK hb label x) hc.aestronglyMeasurable hbound
    (gaussian_norm_integrable (ι := ι) |>.const_mul K)
    (.of_forall fun w y _ => parameterLogPartition_hasDerivAt ν L hL hK hb label w y)).2

/-- The actual Gaussian mean remains convex by integrating proved
log-partition convexity with genuine integrability at every parameter. -/
theorem parameterMean_convex (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) : ConvexOn ℝ univ (parameterMean ν L label) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb' hab
  simp only [smul_eq_mul]
  unfold parameterMean
  calc
    _ ≤ ∫ w,a*parameterLogPartition ν L label w x+b*parameterLogPartition ν L label w y
        ∂SYK.standardGaussianMeasureOnEuclidean ι := by
      apply integral_mono (parameterLogPartition_gaussian_integrable ν L hL hK hb label _)
        (((parameterLogPartition_gaussian_integrable ν L hL hK hb label x).const_mul a).add
          ((parameterLogPartition_gaussian_integrable ν L hL hK hb label y).const_mul b))
      intro w
      simpa only [smul_eq_mul,Pi.add_apply] using
        (parameterLogPartition_convex ν L hL hK hb label w).2 (mem_univ x) (mem_univ y) ha hb' hab
    _ = _ := by
      rw [integral_add ((parameterLogPartition_gaussian_integrable ν L hL hK hb label x).const_mul a)
        ((parameterLogPartition_gaussian_integrable ν L hL hK hb label y).const_mul b),
        integral_const_mul,integral_const_mul]

end
end SlowEquilibration.GaussianPerturbationParameter

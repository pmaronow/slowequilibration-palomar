-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianSpinComparison
public import Mathlib.Analysis.Calculus.FDeriv.WithLp

@[expose] public section

/-! Actual original/trial Gaussian rotation with a third independent perturbation
block held fixed. Its derivative has exactly zero contribution from that block. -/

namespace SlowEquilibration.GaussianThreeBlockComparison

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {ι V : Type*} [Fintype ι] [MeasurableSpace V]

/-- The actual diagonal linear map on the Euclidean disorder coordinates. -/
def diagonal (a : ι → ℝ) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => a i • PiLp.proj 2 (fun _ : ι => ℝ) i))

omit [Fintype ι] in
@[simp] theorem diagonal_apply (a : ι → ℝ) (w : EuclideanSpace ℝ ι) (i : ι) :
    diagonal a w i = a i * w i := rfl

theorem diagonal_norm_le (a : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ i, |a i| ≤ C) (w : EuclideanSpace ℝ ι) : ‖diagonal a w‖ ≤ C*‖w‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg w))).mp
  rw [EuclideanSpace.real_norm_sq_eq, mul_pow, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [diagonal_apply, mul_pow]
  have hsq : (a i)^2 ≤ C^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (a i)) hC).mpr (ha i)
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

def coordinateMask (label : ι → Fin 3) (b : Fin 3) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  diagonal (fun i => if label i = b then 1 else 0)

def rotation (label : ι → Fin 3) (θ : ℝ) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  Real.cos θ • coordinateMask label 0 + Real.sin θ • coordinateMask label 1 + coordinateMask label 2

def rotationDerivative (label : ι → Fin 3) (θ : ℝ) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  -Real.sin θ • coordinateMask label 0 + Real.cos θ • coordinateMask label 1

def rotationCoefficient (label : ι → Fin 3) (θ : ℝ) (i : ι) : ℝ :=
  if label i=0 then Real.cos θ else if label i=1 then Real.sin θ else 1

def rotationCoefficientDerivative (label : ι → Fin 3) (θ : ℝ) (i : ι) : ℝ :=
  if label i=0 then -Real.sin θ else if label i=1 then Real.cos θ else 0

@[simp] theorem rotation_apply (label : ι → Fin 3) (θ : ℝ) (w : EuclideanSpace ℝ ι) (i : ι) :
    rotation label θ w i = rotationCoefficient label θ i * w i := by
  generalize h : label i = k; fin_cases k <;>
    simp [rotation, coordinateMask, PiLp.add_apply, PiLp.smul_apply, rotationCoefficient, h]

@[simp] theorem rotationDerivative_apply (label : ι → Fin 3) (θ : ℝ) (w : EuclideanSpace ℝ ι) (i : ι) :
    rotationDerivative label θ w i = rotationCoefficientDerivative label θ i * w i := by
  generalize h : label i = k; fin_cases k <;>
    simp [rotationDerivative, coordinateMask, PiLp.add_apply, PiLp.smul_apply, rotationCoefficientDerivative, h]

theorem rotation_norm_le (label : ι → Fin 3) (θ : ℝ) (w : EuclideanSpace ℝ ι) :
    ‖rotation label θ w‖ ≤ ‖w‖ := by
  have heq : rotation label θ=diagonal (rotationCoefficient label θ) := by
    ext g i
    simp only [rotation_apply,diagonal_apply]
  rw [heq]
  simpa only [one_mul] using diagonal_norm_le (rotationCoefficient label θ) zero_le_one
    (fun i => by
      generalize h : label i = k; fin_cases k
      · simpa [rotationCoefficient,h] using Real.abs_cos_le_one θ
      · simpa [rotationCoefficient,h] using Real.abs_sin_le_one θ
      · norm_num [rotationCoefficient,h]) w

theorem rotationDerivative_norm_le (label : ι → Fin 3) (θ : ℝ) (w : EuclideanSpace ℝ ι) :
    ‖rotationDerivative label θ w‖ ≤ ‖w‖ := by
  have heq : rotationDerivative label θ=diagonal (rotationCoefficientDerivative label θ) := by
    ext g i
    simp only [rotationDerivative_apply,diagonal_apply]
  rw [heq]
  simpa only [one_mul] using diagonal_norm_le (rotationCoefficientDerivative label θ) zero_le_one
    (fun i => by
      generalize h : label i = k; fin_cases k
      · simpa [rotationCoefficientDerivative,h] using Real.abs_sin_le_one θ
      · simpa [rotationCoefficientDerivative,h] using Real.abs_cos_le_one θ
      · norm_num [rotationCoefficientDerivative,h]) w

theorem rotation_hasDerivAt (label : ι → Fin 3) (w : EuclideanSpace ℝ ι) (θ : ℝ) :
    HasDerivAt (fun t => rotation label t w) (rotationDerivative label θ w) θ := by
  convert (((Real.hasDerivAt_cos θ).smul_const (coordinateMask label 0 w)).add
    ((Real.hasDerivAt_sin θ).smul_const (coordinateMask label 1 w))).add_const
      (coordinateMask label 2 w) using 1
  · funext t
    rfl
  · rfl

def rotatedLinear (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (label : ι → Fin 3) (θ : ℝ) :=
  fun v => (L v).comp (rotation label θ)

theorem rotatedLinear_measurable (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hL : Measurable L) (label : ι → Fin 3) (θ : ℝ) : Measurable (rotatedLinear L label θ) := by
  have hc : Continuous (fun l : EuclideanSpace ℝ ι →L[ℝ] ℝ => l.comp (rotation label θ)) :=
    continuous_id.clm_comp continuous_const
  exact hc.measurable.comp hL

theorem rotatedLinear_bound (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Fin 3) (θ : ℝ) :
    ∀ᵐ v ∂ν, ‖rotatedLinear L label θ v‖ ≤ K := by
  filter_upwards [hb] with v hv
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro w
  exact ((L v).le_opNorm (rotation label θ w)).trans
    ((mul_le_mul_of_nonneg_left (rotation_norm_le label θ w) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hv (norm_nonneg _)))

theorem logPartition_rotated_hasDerivAt (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Fin 3) (w : EuclideanSpace ℝ ι) (θ : ℝ) :
    HasDerivAt (fun t => GaussianSpinInterpolation.logPartition ν L (rotation label t w))
      (GaussianSpinInterpolation.score ν L (rotation label θ w) (rotationDerivative label θ w)) θ := by
  simpa only [Function.comp_def] using
    (GaussianSpinInterpolation.logPartition_hasFDerivAt ν L hL hK hb (rotation label θ w)).comp_hasDerivAt θ
      (rotation_hasDerivAt label w θ)

def averagedRotatedLogPartition (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Fin 3) (θ : ℝ) : ℝ :=
  ∫ w, GaussianSpinInterpolation.logPartition ν L (rotation label θ w)
    ∂SYK.standardGaussianMeasureOnEuclidean ι

theorem logPartition_rotated_gaussian_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Fin 3) (θ : ℝ) :
    Integrable (fun w => GaussianSpinInterpolation.logPartition ν L (rotation label θ w))
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hc := (GaussianSpinInterpolation.logPartition_contDiff ν L hL hK hb).continuous.comp
    (rotation label θ).continuous
  apply (GaussianSpinInterpolation.gaussian_norm_integrable (ι := ι) |>.const_mul K).mono' hc.aestronglyMeasurable
  exact .of_forall fun w => by
    rw [Real.norm_eq_abs]
    exact (GaussianSpinInterpolation.abs_logPartition_le ν L hL hb _).trans
      (mul_le_mul_of_nonneg_left (rotation_norm_le label θ w) hK)

/-- Exact differentiation of the actual three-block Gaussian rotation
interpolation; its Gaussian norm envelope is proved from the spin feature bound. -/
theorem averagedRotatedLogPartition_hasDerivAt (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Fin 3) (θ : ℝ) :
    HasDerivAt (averagedRotatedLogPartition ν L label)
      (∫ w, GaussianSpinInterpolation.score ν L (rotation label θ w) (rotationDerivative label θ w)
        ∂SYK.standardGaussianMeasureOnEuclidean ι) θ := by
  have hc : Continuous (fun w => GaussianSpinInterpolation.score ν L
      (rotation label θ w) (rotationDerivative label θ w)) :=
    ((GaussianSpinInterpolation.score_continuous ν L hL hK hb).comp
      (rotation label θ).continuous).clm_apply (rotationDerivative label θ).continuous
  have hbound : ∀ᵐ w ∂SYK.standardGaussianMeasureOnEuclidean ι, ∀ t ∈ (univ : Set ℝ),
      ‖GaussianSpinInterpolation.score ν L (rotation label t w) (rotationDerivative label t w)‖ ≤ K*‖w‖ :=
    .of_forall fun w t _ =>
      ((GaussianSpinInterpolation.score ν L (rotation label t w)).le_opNorm _).trans
        ((mul_le_mul_of_nonneg_right (GaussianSpinInterpolation.norm_score_le ν L hL hK hb _)
          (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left (rotationDerivative_norm_le label t w) hK))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := SYK.standardGaussianMeasureOnEuclidean ι) (s := univ)
    (F := fun t w => GaussianSpinInterpolation.logPartition ν L (rotation label t w))
    (F' := fun t w => GaussianSpinInterpolation.score ν L (rotation label t w) (rotationDerivative label t w))
    (bound := fun w => K*‖w‖) (by simp)
    (.of_forall fun t => (logPartition_rotated_gaussian_integrable ν L hL hK hb label t).aestronglyMeasurable)
    (logPartition_rotated_gaussian_integrable ν L hL hK hb label θ) hc.aestronglyMeasurable hbound
    (GaussianSpinInterpolation.gaussian_norm_integrable (ι := ι) |>.const_mul K)
    (.of_forall fun w t _ => logPartition_rotated_hasDerivAt ν L hL hK hb label w t)).2

variable [DecidableEq ι]

def coordinateObservable (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (i : ι) : V → ℝ :=
  fun v => L v (EuclideanSpace.single i 1)

theorem coordinateObservable_measurable (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hL : Measurable L) (i : ι) : Measurable (coordinateObservable L i) :=
  (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).continuous.measurable.comp hL

theorem coordinateObservable_bound (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {K : ℝ} (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (i : ι) : ∀ᵐ v ∂ν, |coordinateObservable L i v| ≤ K := by
  filter_upwards [hb] with v hv
  have hh := (L v).le_opNorm (EuclideanSpace.single i 1)
  have he : ‖(EuclideanSpace.single i 1 : EuclideanSpace ℝ ι)‖ = 1 := by simp
  rw [Real.norm_eq_abs, he, mul_one] at hh
  exact hh.trans hv

theorem rotation_single (label : ι → Fin 3) (θ : ℝ) (i : ι) :
    rotation label θ (EuclideanSpace.single i 1) =
      rotationCoefficient label θ i • EuclideanSpace.single i 1 := by
  ext j
  rw [rotation_apply, PiLp.smul_apply]
  by_cases hj : j = i
  · subst j
    simp only [PiLp.single_apply, ite_true, mul_one, smul_eq_mul]
  · simp only [PiLp.single_apply, hj, ite_false, mul_zero, smul_eq_mul]

omit [MeasurableSpace V] in
theorem rotatedLinear_single (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Fin 3) (θ : ℝ) (v : V) (i : ι) :
    rotatedLinear L label θ v (EuclideanSpace.single i 1) =
      rotationCoefficient label θ i * coordinateObservable L i v := by
  simp only [rotatedLinear, ContinuousLinearMap.comp_apply, rotation_single, map_smul,
    smul_eq_mul, coordinateObservable]

omit [DecidableEq ι] in
theorem expectation_rotatedLinear (ν : Measure V) (ρ : V → ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (label : ι → Fin 3) (θ : ℝ) (w : EuclideanSpace ℝ ι) :
    GaussianSpinInterpolation.expectation ν ρ (rotatedLinear L label θ) w =
      GaussianSpinInterpolation.expectation ν ρ L (rotation label θ w) := by
  simp only [GaussianSpinInterpolation.expectation, GaussianSpinInterpolation.moment,
    GaussianSpinInterpolation.weight, rotatedLinear, ContinuousLinearMap.comp_apply]

theorem coordinate_expectation_integrable (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Fin 3) (θ : ℝ) (i : ι) :
    Integrable (fun w => w i * GaussianSpinInterpolation.expectation ν
      (coordinateObservable L i) (rotatedLinear L label θ) w)
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hobs := coordinateObservable_measurable L hL i
  have hLt := rotatedLinear_measurable L hL label θ
  have hbt := (coordinateObservable_bound ν L hb i).and (rotatedLinear_bound ν L hK hb label θ)
  have hc : Continuous (fun w : EuclideanSpace ℝ ι => w i * GaussianSpinInterpolation.expectation ν
      (coordinateObservable L i) (rotatedLinear L label θ) w) :=
    (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i).mul
      (GaussianSpinInterpolation.expectation_contDiff ν _ _ hobs hLt hK hK hbt).continuous
  apply (GaussianSpinInterpolation.gaussian_norm_integrable (ι := ι) |>.const_mul K).mono' hc.aestronglyMeasurable
  exact .of_forall fun w => by
    rw [norm_mul]
    calc
      _ ≤ ‖w‖*K := mul_le_mul (PiLp.norm_apply_le w i)
        (GaussianSpinInterpolation.norm_expectation_le ν _ _ hobs hLt hK hbt w)
        (norm_nonneg _) (norm_nonneg _)
      _ = _ := mul_comm _ _

/-- Each component of the covariance rotation is a genuine variance under
the interpolated Gibbs probability measure. -/
theorem gaussian_coordinate_rotation_response (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Fin 3) (θ : ℝ) (i : ι) :
    (∫ w, w i * GaussianSpinInterpolation.expectation ν (coordinateObservable L i)
      (rotatedLinear L label θ) w ∂SYK.standardGaussianMeasureOnEuclidean ι) =
      rotationCoefficient label θ i * ∫ w,
        variance (coordinateObservable L i)
          (GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w)
        ∂SYK.standardGaussianMeasureOnEuclidean ι := by
  have hobs := coordinateObservable_measurable L hL i
  have hLt := rotatedLinear_measurable L hL label θ
  have hbt := (coordinateObservable_bound ν L hb i).and (rotatedLinear_bound ν L hK hb label θ)
  have h := GaussianSpinInterpolation.gaussian_expectation_ibp ν _ _ hobs hLt hK hK hbt
    (EuclideanSpace.single i 1)
  have hpoint (w : EuclideanSpace ℝ ι) :
      GaussianSpinInterpolation.expectationDerivative ν (coordinateObservable L i) (rotatedLinear L label θ)
        w (EuclideanSpace.single i 1) = rotationCoefficient label θ i *
          variance (coordinateObservable L i) (GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w) := by
    rw [GaussianSpinInterpolation.expectationDerivative_apply ν _ _ hobs hLt hbt]
    have hp : (fun v => coordinateObservable L i v * rotatedLinear L label θ v (EuclideanSpace.single i 1)) =
        fun v => rotationCoefficient label θ i * (coordinateObservable L i v)^2 := by
      funext v
      rw [rotatedLinear_single]
      ring
    have hlin : (fun v => rotatedLinear L label θ v (EuclideanSpace.single i 1)) =
        fun v => rotationCoefficient label θ i * coordinateObservable L i v := by
      funext v
      exact rotatedLinear_single L label θ v i
    rw [hp, hlin, GaussianSpinInterpolation.expectation_const_mul,
      GaussianSpinInterpolation.expectation_const_mul,
      ← GaussianSpinInterpolation.expectation_variance ν _ _ hobs hLt hbt w]
    ring
  simpa only [EuclideanSpace.inner_single_left, conj_trivial, one_mul,
    integral_congr_ae (.of_forall hpoint), integral_const_mul] using h

/-- The exact three-block Gaussian interpolation derivative, before
rewriting the two coordinate blocks as overlap covariance kernels. -/
theorem averagedRotatedLogPartition_hasDerivAt_variance (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Fin 3) (θ : ℝ) :
    HasDerivAt (averagedRotatedLogPartition ν L label)
      (∑ i, (rotationCoefficientDerivative label θ i * rotationCoefficient label θ i) *
        ∫ w, variance (coordinateObservable L i)
          (GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w)
        ∂SYK.standardGaussianMeasureOnEuclidean ι) θ := by
  have hd := averagedRotatedLogPartition_hasDerivAt ν L hL hK hb label θ
  have hpoint (w : EuclideanSpace ℝ ι) :
      GaussianSpinInterpolation.score ν L (rotation label θ w) (rotationDerivative label θ w) =
      ∑ i, rotationCoefficientDerivative label θ i *
        (w i * GaussianSpinInterpolation.expectation ν (coordinateObservable L i) (rotatedLinear L label θ) w) := by
    rw [GaussianSpinInterpolation.score_eq_coordinate_sum ν L hL hb]
    simp only [rotationDerivative_apply, expectation_rotatedLinear]
    apply Finset.sum_congr rfl
    intro i _
    change rotationCoefficientDerivative label θ i * w i *
      GaussianSpinInterpolation.expectation ν (fun v => L v (EuclideanSpace.single i 1)) L (rotation label θ w) =
      rotationCoefficientDerivative label θ i * (w i *
        GaussianSpinInterpolation.expectation ν (fun v => L v (EuclideanSpace.single i 1)) L (rotation label θ w))
    ring
  convert hd using 1
  rw [integral_congr_ae (.of_forall hpoint), integral_finsetSum Finset.univ (fun i _ =>
    (coordinate_expectation_integrable ν L hL hK hb label θ i).const_mul _)]
  simp_rw [integral_const_mul, gaussian_coordinate_rotation_response ν L hL hK hb label θ]
  apply Finset.sum_congr rfl
  intro i _
  ring

def covarianceSign (label : ι → Fin 3) (i : ι) : ℝ := if label i=0 then -1 else if label i=1 then 1 else 0

def signedKernel (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (label : ι → Fin 3) (v u : V) : ℝ :=
  ∑ i, covarianceSign label i * (coordinateObservable L i v * coordinateObservable L i u)

theorem coordinateVariance_integrable (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Fin 3) (θ : ℝ) (i : ι) :
    Integrable (fun w => variance (coordinateObservable L i)
      (GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w))
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  let ρ := coordinateObservable L i
  let Lt := rotatedLinear L label θ
  have hρ := coordinateObservable_measurable L hL i
  have hLt := rotatedLinear_measurable L hL label θ
  have hp := (coordinateObservable_bound ν L hb i).and (rotatedLinear_bound ν L hK hb label θ)
  have hp2 : ∀ᵐ v ∂ν, |(ρ v)^2| ≤ K^2 ∧ ‖Lt v‖ ≤ K := by
    filter_upwards [hp] with v hv
    exact ⟨by simpa only [abs_pow, sq_abs] using
      (sq_le_sq₀ (abs_nonneg (ρ v)) hK).mpr hv.1, hv.2⟩
  have hcont1 := (GaussianSpinInterpolation.expectation_contDiff ν ρ Lt hρ hLt hK hK hp).continuous
  have hcont2 := (GaussianSpinInterpolation.expectation_contDiff ν (fun v => (ρ v)^2) Lt
    (hρ.pow_const 2) hLt (sq_nonneg K) hK hp2).continuous
  have hi : Integrable (fun w => GaussianSpinInterpolation.expectation ν (fun v => (ρ v)^2) Lt w -
      (GaussianSpinInterpolation.expectation ν ρ Lt w)^2)
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
    apply Integrable.of_bound (hcont2.sub (hcont1.pow 2)).aestronglyMeasurable (2*K^2)
    exact .of_forall fun w => by
      have h1 := GaussianSpinInterpolation.norm_expectation_le ν ρ Lt hρ hLt hK hp w
      have h2 := GaussianSpinInterpolation.norm_expectation_le ν (fun v => (ρ v)^2) Lt
        (hρ.pow_const 2) hLt (sq_nonneg K) hp2 w
      have hs : ‖(GaussianSpinInterpolation.expectation ν ρ Lt w)^2‖ ≤ K^2 := by
        rw [norm_pow]
        exact (sq_le_sq₀ (norm_nonneg _) hK).mpr h1
      apply (norm_sub_le _ _).trans
      change ‖GaussianSpinInterpolation.expectation ν (fun v => (ρ v)^2) Lt w‖ +
        ‖(GaussianSpinInterpolation.expectation ν ρ Lt w)^2‖ ≤ 2*K^2
      linarith
  apply hi.congr
  exact .of_forall fun w => GaussianSpinInterpolation.expectation_variance ν ρ Lt hρ hLt hp w

/-- Exact diagonal/replica decomposition under the interpolated ordinary
Gibbs law, with signed coordinate blocks retained. -/
theorem signedVarianceTrace_eq_kernels (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Fin 3) (θ : ℝ)
    (w : EuclideanSpace ℝ ι) :
    (∑ i, covarianceSign label i * variance (coordinateObservable L i)
      (GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w)) =
      (∫ v, signedKernel L label v v ∂GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w) -
      ∫ z : V × V, signedKernel L label z.1 z.2
        ∂(GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w).prod
          (GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w) := by
  let G := GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w
  have hLt := rotatedLinear_measurable L hL label θ
  have hbt := rotatedLinear_bound ν L hK hb label θ
  have : IsProbabilityMeasure G := GaussianSpinInterpolation.gibbsMeasure_probability ν _ hLt hbt w
  have hac : G ≪ ν := GaussianSpinInterpolation.gibbsMeasure_absolutelyContinuous ν _ w
  have hLp (i : ι) : MemLp (coordinateObservable L i) 2 G :=
    MemLp.of_bound (coordinateObservable_measurable L hL i).aestronglyMeasurable K
      (((coordinateObservable_bound ν L hb i).mono (fun v hv => by
        simpa only [Real.norm_eq_abs] using hv)).filter_mono hac.ae_le)
  have hvar (i : ι) : variance (coordinateObservable L i) G =
      (∫ v, (coordinateObservable L i v)^2 ∂G) - (∫ v, coordinateObservable L i v ∂G)^2 := by
    rw [← covariance_self (hLp i).aemeasurable, covariance_eq_sub (hLp i) (hLp i)]
    simp only [Pi.mul_apply, pow_two]
  change (∑ i, covarianceSign label i * variance (coordinateObservable L i) G) =
    (∫ v, signedKernel L label v v ∂G) - ∫ z : V × V, signedKernel L label z.1 z.2 ∂G.prod G
  simp_rw [hvar, mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · unfold signedKernel
    simp only [← pow_two]
    rw [integral_finsetSum Finset.univ (fun i _ => (hLp i).integrable_sq.const_mul _)]
    simp only [integral_const_mul]
  · unfold signedKernel
    rw [integral_finsetSum Finset.univ (fun i _ =>
      (((hLp i).integrable (by norm_num)).mul_prod ((hLp i).integrable (by norm_num))).const_mul _)]
    simp only [integral_const_mul, integral_prod_mul, pow_two]

omit [Fintype ι] [DecidableEq ι] in
theorem rotationCoefficient_product (label : ι → Fin 3) (θ : ℝ) (i : ι) :
    rotationCoefficientDerivative label θ i * rotationCoefficient label θ i =
      Real.sin θ * Real.cos θ * covarianceSign label i := by
  generalize h : label i = k; fin_cases k <;> simp [rotationCoefficientDerivative, rotationCoefficient, covarianceSign, h,
    mul_comm]

theorem averagedRotatedLogPartition_hasDerivAt_signedTrace (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Fin 3) (θ : ℝ) :
    HasDerivAt (averagedRotatedLogPartition ν L label)
      (Real.sin θ * Real.cos θ * ∫ w,
        (∑ i, covarianceSign label i * variance (coordinateObservable L i)
          (GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w))
        ∂SYK.standardGaussianMeasureOnEuclidean ι) θ := by
  have hd := averagedRotatedLogPartition_hasDerivAt_variance ν L hL hK hb label θ
  convert hd using 1
  rw [integral_finsetSum Finset.univ (fun i _ => (coordinateVariance_integrable ν L hL hK hb label θ i).const_mul _)]
  simp only [rotationCoefficient_product, integral_const_mul, Finset.mul_sum, mul_assoc]

theorem gibbsCoordinate_memLp (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Fin 3) (θ : ℝ)
    (w : EuclideanSpace ℝ ι) (i : ι) :
    MemLp (coordinateObservable L i) 2 (GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w) := by
  have : IsProbabilityMeasure (GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w) :=
    GaussianSpinInterpolation.gibbsMeasure_probability ν _ (rotatedLinear_measurable L hL label θ)
      (rotatedLinear_bound ν L hK hb label θ) w
  apply MemLp.of_bound (coordinateObservable_measurable L hL i).aestronglyMeasurable K
  exact ((coordinateObservable_bound ν L hb i).mono (fun v hv => by
    simpa only [Real.norm_eq_abs] using hv)).filter_mono
    (GaussianSpinInterpolation.gibbsMeasure_absolutelyContinuous ν _ w).ae_le

theorem signedKernel_diagonal_integrable (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Fin 3) (θ : ℝ)
    (w : EuclideanSpace ℝ ι) :
    Integrable (fun v => signedKernel L label v v)
      (GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w) := by
  apply integrable_finsetSum Finset.univ
  intro i _
  have hm := gibbsCoordinate_memLp ν L hL hK hb label θ w i
  exact (hm.integrable_mul hm).const_mul (covarianceSign label i)

theorem signedKernel_pair_integrable (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Fin 3) (θ : ℝ)
    (w : EuclideanSpace ℝ ι) :
    Integrable (fun z : V × V => signedKernel L label z.1 z.2)
      ((GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w).prod
        (GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w)) := by
  have : IsProbabilityMeasure (GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w) :=
    GaussianSpinInterpolation.gibbsMeasure_probability ν _ (rotatedLinear_measurable L hL label θ)
      (rotatedLinear_bound ν L hK hb label θ) w
  apply integrable_finsetSum Finset.univ
  intro i _
  have hm := (gibbsCoordinate_memLp ν L hL hK hb label θ w i).integrable (by norm_num)
  exact (hm.mul_prod hm).const_mul (covarianceSign label i)

/-- Kernel comparison is transferred to actual Gibbs replicas through
absolute continuity and the exact variance decomposition. -/
theorem signedTrace_ge_of_kernel_comparison (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Fin 3)
    {d c : ℝ} (hdiag : ∀ᵐ v ∂ν, signedKernel L label v v = d)
    (hpair : ∀ᵐ z ∂ν.prod ν, signedKernel L label z.1 z.2 ≤ c)
    (θ : ℝ) (w : EuclideanSpace ℝ ι) :
    d-c ≤ ∑ i, covarianceSign label i * variance (coordinateObservable L i)
      (GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w) := by
  let G := GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w
  have : IsProbabilityMeasure G := GaussianSpinInterpolation.gibbsMeasure_probability ν _
    (rotatedLinear_measurable L hL label θ) (rotatedLinear_bound ν L hK hb label θ) w
  have hac : G ≪ ν := GaussianSpinInterpolation.gibbsMeasure_absolutelyContinuous ν _ w
  have hd : (∫ v, signedKernel L label v v ∂G) = d := by
    rw [integral_congr_ae (hdiag.filter_mono hac.ae_le)]
    simp only [integral_const, probReal_univ, one_smul]
  have hp : (∫ z : V × V, signedKernel L label z.1 z.2 ∂G.prod G) ≤ c := by
    have h := integral_mono_ae (signedKernel_pair_integrable ν L hL hK hb label θ w)
      (integrable_const c) (hpair.filter_mono (hac.prod hac).ae_le)
    simpa only [integral_const, probReal_univ, one_smul] using h
  rw [signedVarianceTrace_eq_kernels ν L hL hK hb label θ w, hd]
  exact sub_le_sub_left hp d

theorem averagedRotatedLogPartition_deriv_ge (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Fin 3)
    {d c θ : ℝ} (hdiag : ∀ᵐ v ∂ν, signedKernel L label v v = d)
    (hpair : ∀ᵐ z ∂ν.prod ν, signedKernel L label z.1 z.2 ≤ c)
    (hθ : θ ∈ Icc 0 (Real.pi/2)) :
    Real.sin θ * Real.cos θ * (d-c) ≤ deriv (averagedRotatedLogPartition ν L label) θ := by
  rw [(averagedRotatedLogPartition_hasDerivAt_signedTrace ν L hL hK hb label θ).deriv]
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hs hc)
  have hi := integrable_finsetSum Finset.univ (fun i _ =>
    (coordinateVariance_integrable ν L hL hK hb label θ i).const_mul (covarianceSign label i))
  have h := integral_mono_ae (integrable_const (d-c)) hi
    (.of_forall (signedTrace_ge_of_kernel_comparison ν L hL hK hb label hdiag hpair θ))
  simpa only [integral_const, probReal_univ, one_smul] using h

/-- A genuine continuous-spin Gaussian covariance comparison. The endpoint
partition integrals are the actual rotations of the same finite Gaussian
disorder, and the error is determined by the explicit covariance kernels. -/
theorem gaussian_covariance_comparison (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Fin 3)
    {d c : ℝ} (hdiag : ∀ᵐ v ∂ν, signedKernel L label v v = d)
    (hpair : ∀ᵐ z ∂ν.prod ν, signedKernel L label z.1 z.2 ≤ c) :
    averagedRotatedLogPartition ν L label 0 ≤
      averagedRotatedLogPartition ν L label (Real.pi/2) + (c-d)/2 := by
  let F := averagedRotatedLogPartition ν L label
  let C := fun t : ℝ => (d-c)/2*(Real.sin t)^2
  have hF (t : ℝ) := averagedRotatedLogPartition_hasDerivAt ν L hL hK hb label t
  have hC (t : ℝ) : HasDerivAt C ((d-c)*Real.sin t*Real.cos t) t := by
    convert ((Real.hasDerivAt_sin t).pow 2).const_mul ((d-c)/2) using 1
    ring
  have hG (t : ℝ) := (hF t).sub (hC t)
  have hmono : MonotoneOn (fun t => F t-C t) (Icc 0 (Real.pi/2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (continuous_iff_continuousAt.mpr (fun t => (hG t).continuousAt)).continuousOn
      (fun t _ => (hG t).differentiableAt.differentiableWithinAt)
    intro t ht
    have hθ := interior_subset ht
    have hh := averagedRotatedLogPartition_deriv_ge ν L hL hK hb label hdiag hpair hθ
    rw [(hG t).deriv, ← (hF t).deriv]
    change 0 ≤ deriv F t - (d-c)*Real.sin t*Real.cos t
    nlinarith
  have h := hmono (show 0 ∈ Icc 0 (Real.pi/2) by constructor <;> linarith [Real.pi_pos])
    (show Real.pi/2 ∈ Icc 0 (Real.pi/2) by constructor <;> linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])
  simp only [F, C, Real.sin_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_zero,
    Real.sin_pi_div_two, one_pow, mul_one] at h
  linarith

end
end SlowEquilibration.GaussianThreeBlockComparison

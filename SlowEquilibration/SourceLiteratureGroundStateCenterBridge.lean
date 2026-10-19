-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagTAP
public import SlowEquilibration.SourceLiteratureGroundState
public import SlowEquilibration.SourceLiteratureGroundStateRadialCoefficients
public import SlowEquilibration.SphericalTaylorResidualKernel

/-!
# The center-sphere expected maximum is a Chen–Sen ground energy

Source Section 5, after `thm:th-ground`: the maximum of the original field
on the sphere of squared radius `N q` is the maximum on the radius-`sqrt N`
sphere of a field with covariance `N ξ(q R)`. This file proves the exact
expected-maximum identity in every positive dimension:

`expectedCenterGroundEnergy N μ q = canonicalGroundEnergy (centerMixture μ q) N`.

The original disorder is indexed by the degrees of `μ`, while Chen–Sen's
ordered tensor model is indexed by those of the center mixture. The two
continuous Gaussian fields are identified through their evaluation
covariances, so no cast between degree types is needed.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceLiteratureGroundStateCenterBridge

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalCriticalLatitude
open SphericalTaylorRemainder SphericalTwoPointCovariance GaussianContinuousFieldLaw
open SphericalParisiContinuousMaximum SphericalParisiFiniteMixtureGroundBridge
open SourceLiteratureGroundState SourceLiteratureGroundStateRadialCoefficients
open LiteratureSubagTAP PureTensorJetBounds
open scoped Topology RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original field restricted to the center sphere, written on the
unit sphere as `u ↦ H_N(sqrt(N q) u)`, over the original disorder
coordinates. -/
def centerContinuousField (μ : FiniteMixture) (q : ℝ) (N : ℕ) :
    EuclideanDisorder N μ.maxDegree →L[ℝ] C(UnitSphere N, ℝ) :=
  modelContinuousField (centerCoefficients (mixtureCoefficients μ) q)
    (fun v : UnitSphere N => Real.sqrt (N : ℝ) • v.val)
    (physical_sphere_parameter_continuous _ continuous_subtype_val)

theorem centerContinuousField_covariance (μ : FiniteMixture) {q : ℝ}
    (hq : 0 < q) {N : ℕ} (hN : 0 < N) (v w : UnitSphere N) :
    cov[fun g => centerContinuousField μ q N g v,
      fun g => centerContinuousField μ q N g w;
        stdGaussian (EuclideanDisorder N μ.maxDegree)] =
      (N : ℝ) * (centerMixture μ q hq).xi (inner ℝ v.val w.val) := by
  have hEval (a : UnitSphere N) : evaluationFeature (centerContinuousField μ q N) a =
      valueObservation (centerCoefficients (mixtureCoefficients μ) q)
        (Real.sqrt (N : ℝ) • a.val) := by
    ext g
    rfl
  have hOverlap : overlap (Real.sqrt (N : ℝ) • v.val) (Real.sqrt (N : ℝ) • w.val) =
      inner ℝ v.val w.val := by
    unfold overlap
    simp only [real_inner_smul_left, real_inner_smul_right]
    rw [show Real.sqrt (N : ℝ) * (Real.sqrt (N : ℝ) * inner ℝ v.val w.val) =
      (Real.sqrt (N : ℝ)) ^ 2 * inner ℝ v.val w.val by ring,
      Real.sq_sqrt (Nat.cast_nonneg N)]
    exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hN.ne')
  rw [evaluation_covariance, hEval v, hEval w,
    value_value_coupling hN _ (centerCoefficients_nonnegative _
      (mixtureCoefficients_nonnegative μ) hq.le),
    covariancePolynomial_center, covariancePolynomial_mixture, hOverlap,
    centerMixture_xi]

/-- Equality of the two full continuous-field laws. -/
theorem centerContinuousField_law (μ : FiniteMixture) {q : ℝ} (hq : 0 < q)
    {N : ℕ} (hN : 0 < N) :
    haveI : NeZero N := ⟨hN.ne'⟩
    (stdGaussian (EuclideanDisorder N μ.maxDegree)).map (centerContinuousField μ q N) =
      (stdGaussian (EuclideanDisorder N (centerMixture μ q hq).maxDegree)).map
        (physicalResidualContinuousField (centerMixture μ q hq) N N
          (fun x : UnitSphere N => x.val) continuous_subtype_val) := by
  have : NeZero N := ⟨hN.ne'⟩
  apply continuous_field_law_eq_of_covariance
  intro v w
  rw [centerContinuousField_covariance μ hq hN,
    physicalResidualContinuousField_covariance (centerMixture μ q hq) N N hN]

/-- Pathwise: the supremum over the radius-`sqrt N` sphere is the maximum
of the unit-sphere continuous field. -/
theorem sSup_sphere_eq_maximum (μ : FiniteMixture) (q : ℝ) {N : ℕ} (hN : 0 < N)
    (J : Disorder N μ.maxDegree) :
    haveI : NeZero N := ⟨hN.ne'⟩
    sSup ((field (centerCoefficients (mixtureCoefficients μ) q) J) ''
        {u : Vector N | ‖u‖ ^ 2 = (N : ℝ)}) =
      maximum (centerContinuousField μ q N (euclideanDisorder J)) := by
  have : NeZero N := ⟨hN.ne'⟩
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hset : (field (centerCoefficients (mixtureCoefficients μ) q) J) ''
      {u : Vector N | ‖u‖ ^ 2 = (N : ℝ)} =
      range (centerContinuousField μ q N (euclideanDisorder J)) := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hun : ‖u‖ = Real.sqrt (N : ℝ) := by
        rw [← Real.sqrt_sq (norm_nonneg u), hu]
      let v : UnitSphere N := ⟨(Real.sqrt (N : ℝ))⁻¹ • u, by
        simp only [UnitSphere, Metric.mem_sphere, dist_zero_right, norm_smul,
          Real.norm_eq_abs, abs_inv, abs_of_pos hs, hun]
        exact inv_mul_cancel₀ hs.ne'⟩
      refine ⟨v, ?_⟩
      change valueObservation _ (Real.sqrt (N : ℝ) • v.val) (euclideanDisorder J) = _
      rw [valueObservation_actual]
      congr 1
      change Real.sqrt (N : ℝ) • ((Real.sqrt (N : ℝ))⁻¹ • u) = u
      rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    · rintro ⟨v, rfl⟩
      refine ⟨Real.sqrt (N : ℝ) • v.val, ?_, ?_⟩
      · have hv : ‖v.val‖ = 1 := by
          simpa only [UnitSphere, Metric.mem_sphere, dist_zero_right] using v.property
        simp only [Set.mem_ofPred_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hs, hv,
          mul_one]
        exact Real.sq_sqrt (Nat.cast_nonneg N)
      · change field _ J _ = valueObservation _ (Real.sqrt (N : ℝ) • v.val)
          (euclideanDisorder J)
        rw [valueObservation_actual]
  rw [hset]
  rfl

/-- The center-sphere expected maximum equals the Chen–Sen ordered-tensor
ground energy of the center mixture, in every positive dimension. -/
theorem expectedCenterGroundEnergy_eq_canonical (μ : FiniteMixture) {q : ℝ}
    (hq : 0 < q) {N : ℕ} (hN : 0 < N) :
    expectedCenterGroundEnergy N μ q =
      canonicalGroundEnergy (centerMixture μ q hq) N := by
  have : NeZero N := ⟨hN.ne'⟩
  have hpath : ∀ J : Disorder N μ.maxDegree,
      sSup ((field (mixtureCoefficients μ) J) ''
        {m : Vector N | ‖m‖ ^ 2 = (N : ℝ) * q}) =
      maximum (centerContinuousField μ q N (euclideanDisorder J)) := by
    intro J
    rw [centerSphere_sup_eq_scaledMixture μ q hq J, centerMixture_coefficients μ q hq]
    exact sSup_sphere_eq_maximum μ q hN J
  have hmeas : AEStronglyMeasurable
      (fun g => maximum (centerContinuousField μ q N g))
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)) :=
    (maximum_continuous.comp (centerContinuousField μ q N).continuous).aestronglyMeasurable
  have htransport := (euclideanDisorder_hasLaw N μ.maxDegree).integral_comp hmeas
  simp only [Function.comp_def] at htransport
  have hG : SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree) =
      stdGaussian (EuclideanDisorder N μ.maxDegree) := by
    rw [SYK.standardGaussianMeasureOnEuclidean, map_pi_eq_stdGaussian]
  have hlaw := maximum_integral_eq_of_field_law _ _
    (centerContinuousField μ q N)
    (physicalResidualContinuousField (centerMixture μ q hq) N N
      (fun x : UnitSphere N => x.val) continuous_subtype_val)
    (centerContinuousField μ q N).continuous.measurable
    (physicalResidualContinuousField (centerMixture μ q hq) N N
      (fun x : UnitSphere N => x.val) continuous_subtype_val).continuous.measurable
    (centerContinuousField_law μ hq hN)
  have hexp := physicalResidualContinuousField_expected_maximum
    (centerMixture μ q hq) N N hN
  have hone : Real.sqrt ((N : ℝ) / (N : ℝ)) = 1 := by
    rw [div_self (Nat.cast_ne_zero.mpr hN.ne'), Real.sqrt_one]
  unfold expectedCenterGroundEnergy canonicalGroundEnergy
  congr 1
  rw [integral_congr_ae (.of_forall hpath)]
  change (∫ J, (fun g => maximum (centerContinuousField μ q N g))
    (euclideanDisorder J) ∂disorderLaw N μ.maxDegree) = _
  rw [htransport, hG, hlaw, hexp, hone, one_mul]

/-- With Chen–Sen's theorem, the center ground energy converges to the
minimum of the Chen–Sen functional of the center covariance. -/
theorem center_ground_limit (hChenSen : ChenSenFiniteGround) (μ : FiniteMixture)
    {q : ℝ} (hq : 0 < q) :
    ∃ u : GroundProfile,
      (∀ v : GroundProfile, groundFunctional (centerMixture μ q hq) u ≤
        groundFunctional (centerMixture μ q hq) v) ∧
      Tendsto (fun N : ℕ => expectedCenterGroundEnergy N μ q) atTop
        (𝓝 (groundFunctional (centerMixture μ q hq) u)) := by
  obtain ⟨u, hmin, hlim⟩ := hChenSen (centerMixture μ q hq)
  refine ⟨u, hmin, hlim.congr' ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  exact (expectedCenterGroundEnergy_eq_canonical μ hq hN).symm

end SlowEquilibration.SourceLiteratureGroundStateCenterBridge

-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureProbePhysicalMomentTransfer
public import SlowEquilibration.GaussianVarianceTraceContinuity
public import SlowEquilibration.GaussianFeatureEndpoints

@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalPureProbePhysicalPressureResponse

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel GaussianFeatureDirac
open GaussianSpinInterpolation GaussianSpinComparison
open GaussianPerturbationParameter GaussianPerturbationSelfAveraging
open GaussianPerturbationResponse GaussianVarianceTraceContinuity
open SphericalPureProbeSelectedKernel SphericalPureProbeFiniteResponse
open SphericalPureProbeBaseGibbs SphericalPureProbePhysicalMomentTransfer
open PureCapturePhysicalFullOverlapArray
open scoped Topology RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def probePressure (N p : ℕ) (hp : 2 ≤ p) (μ : FiniteMixture) (β s : ℝ) : ℝ :=
  GaussianPerturbationParameter.parameterMean (sphereLaw N)
    (sourcePureProbeLinear N p hp μ β) heldLabel s / (N : ℝ)

/-- Removing the independent pure-spin probe recovers the exact original
finite quenched pressure. -/
theorem probePressure_zero_eq_quenchedPressure
    {N p : ℕ} (hN : 1 ≤ N) (hp : 2 ≤ p)
    (μ : FiniteMixture) (β : ℝ) :
    probePressure N p hp μ β 0 = quenchedPressure N μ β := by
  let A : Vector N → EuclideanSpace ℝ (Coordinate N μ.maxDegree) :=
    fieldFeature (mixtureCoefficients μ)
  let W := pureProbeFeature N p hp β
  have hA : Continuous A := fieldFeature_continuous _
  unfold probePressure sourcePureProbeLinear
  rw [three_parameterMean_zero hN A hA β 0 W 0,
    twoMean_zero_eq_original hN A hA β 0]
  change GaussianSpinInterpolation.averagedLogPartition (sphereLaw N)
    (sphereLinear (mixtureCoefficients μ)) β / (N : ℝ) = _
  exact gaussianMeanLogPartition_eq_quenchedPressure hN μ β

theorem sourcePureProbeLinear_measurable_bound
    {N p : ℕ} (hN : 1 ≤ N) (hp : 2 ≤ p)
    (μ : FiniteMixture) (β : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
      Measurable (sourcePureProbeLinear N p hp μ β) ∧
      ∀ᵐ x ∂sphereLaw N, ‖sourcePureProbeLinear N p hp μ β x‖ ≤ B := by
  let A : Vector N → EuclideanSpace ℝ (Coordinate N μ.maxDegree) :=
    fieldFeature (mixtureCoefficients μ)
  let W := pureProbeFeature N p hp β
  have hA : Continuous A := fieldFeature_continuous _
  have hW : Continuous W := (fieldFeature_continuous _).const_smul β
  obtain ⟨B,hB,hBound⟩ := exists_threeLinear_sphere_bound A hA β 0 W hW
  refine ⟨B,hB,?_,?_⟩
  · exact GaussianThreeBlockComparison.rotatedLinear_measurable _
      (threeLinear_continuous A hA β 0 W hW).measurable threeLabel 0
  · exact GaussianThreeBlockComparison.rotatedLinear_bound (sphereLaw N)
      (threeLinear A β 0 W) hB
      ((sphereLaw_support hN).mono fun x hx => hBound x hx) threeLabel 0

/-- The averaged zero-probe trace is exactly the physical pair-power
response, with no auxiliary overlap law. -/
theorem pureProbe_traceMean_eq_physicalMoment
    {N p : ℕ} (n : ℕ) (hN : N = n+2) (hp : 2 ≤ p)
    (μ : FiniteMixture) (β : ℝ) :
    (∫ w : EuclideanSpace ℝ
        (ThreeCoordinate N (Coordinate N μ.maxDegree)
          (Coordinate N (pureProbe p hp).maxDegree)),
      varianceTrace (sphereLaw N) (sourcePureProbeLinear N p hp μ β)
        heldLabel 0 w ∂SYK.standardGaussianMeasureOnEuclidean _) =
      β^2*(N : ℝ)*(1-
        ∫ c, (c 0 1)^p ∂(physicalFullOverlapLaw
          (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2))) := by
  subst N
  let E := ThreeCoordinate (n+2) (Coordinate (n+2) μ.maxDegree)
    (Coordinate (n+2) (pureProbe p hp).maxDegree)
  let F : EuclideanSpace ℝ E → ℝ := fun w =>
    ∫ z : Vector (n+2) × Vector (n+2), (overlap z.1 z.2)^p
      ∂(sourcePureProbeGibbs (n+2) p hp μ β w).prod
        (sourcePureProbeGibbs (n+2) p hp μ β w)
  have hF : StronglyMeasurable F := by
    have hd := (physical_pairPower_disorder_measurable_bounded (N := n+2)
      (by omega) μ β p).1
    have hproj : Measurable (fun w : EuclideanSpace ℝ E =>
        unpackDisorder (SphericalModel.projectGaussian Sum.inl (threeLeft w))) := by
      have hleft : Measurable (threeLeft : EuclideanSpace ℝ E →
          EuclideanSpace ℝ (TwoCoordinate (n+2) (Coordinate (n+2) μ.maxDegree))) := by
        unfold threeLeft
        fun_prop
      have hp : Measurable (SphericalModel.projectGaussian
          (Sum.inl : Coordinate (n+2) μ.maxDegree →
            TwoCoordinate (n+2) (Coordinate (n+2) μ.maxDegree))) :=
        SphericalModel.projectGaussian_measurable _
      have hu : Measurable (unpackDisorder (N:=n+2) (P:=μ.maxDegree)) := by
        unfold unpackDisorder
        fun_prop
      exact hu.comp (hp.comp hleft)
    have heq : F = fun w =>
        (fun J : Disorder (n+2) μ.maxDegree =>
          ∫ z : Vector (n+2) × Vector (n+2), (overlap z.1 z.2)^p
            ∂(gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)).prod
              (gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)))
          (unpackDisorder (SphericalModel.projectGaussian Sum.inl (threeLeft w))) := by
      funext w
      unfold F
      rw [sourcePureProbeGibbs_eq_original hp μ β w]
    rw [heq]
    exact hd.comp_measurable hproj
  have hFi : Integrable F (SYK.standardGaussianMeasureOnEuclidean E) := by
    apply Integrable.of_bound hF.aestronglyMeasurable 1
    apply Eventually.of_forall
    intro w
    change ‖F w‖ ≤ 1
    rw [Real.norm_eq_abs]
    have hh := (physical_pairPower_disorder_measurable_bounded (N := n+2)
      (by omega) μ β p).2
      (unpackDisorder (SphericalModel.projectGaussian Sum.inl (threeLeft w)))
    simpa only [F, sourcePureProbeGibbs_eq_original] using hh
  have hpoint (w : EuclideanSpace ℝ E) :
      varianceTrace (sphereLaw (n+2))
        (sourcePureProbeLinear (n+2) p hp μ β) heldLabel 0 w =
        β^2*((n+2 : ℕ) : ℝ)*(1-F w) :=
    pureProbe_varianceTrace_eq_replicaPower (by omega) hp μ β w
  rw [integral_congr_ae (.of_forall hpoint), integral_const_mul,
    integral_sub (integrable_const (1 : ℝ)) hFi,
    integral_const]
  simp only [probReal_univ, one_smul]
  rw [extended_zeroProbe_pairPower_eq_physical μ β n p hp]

/-- Exact finite-volume right response to turning on an independent
pure-p Gaussian covariance. The limit is in probe amplitude squared;
there is no thermodynamic-limit interchange in this theorem. -/
theorem probePressure_quadraticResponse_physical
    (μ : FiniteMixture) (β : ℝ) (n p : ℕ) (hp : 2 ≤ p) :
    Tendsto (fun s =>
      (probePressure (n+2) p hp μ β s-quenchedPressure (n+2) μ β)/s^2)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((β^2/2)*(1-
        ∫ c, (c 0 1)^p ∂(physicalFullOverlapLaw
          (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2))))) := by
  obtain ⟨B,hB,hL,hbound⟩ :=
    sourcePureProbeLinear_measurable_bound (N := n+2) (by omega) hp μ β
  have ht := parameterMean_quadratic_response_tendsto_unconditional
    (sphereLaw (n+2)) (sourcePureProbeLinear (n+2) p hp μ β)
    hL hB hbound heldLabel
  have hs := ht.div_const ((n+2 : ℕ) : ℝ)
  convert hs using 1
  · funext s
    rw [← probePressure_zero_eq_quenchedPressure (by omega) hp μ β]
    unfold probePressure
    field_simp [show ((n+2 : ℕ) : ℝ) ≠ 0 by exact_mod_cast (by omega : n+2≠0)]
  · rw [pureProbe_traceMean_eq_physicalMoment n rfl hp μ β]
    field_simp [show ((n+2 : ℕ) : ℝ) ≠ 0 by exact_mod_cast (by omega : n+2≠0)]

end SlowEquilibration.SphericalPureProbePhysicalPressureResponse

-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureProbeBaseGibbs
public import SlowEquilibration.PureCapturePhysicalPairPowerIdentity
public import SlowEquilibration.SphericalNormalizedLikelihoodLowerTail

@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalPureProbePhysicalMomentTransfer

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel GaussianFeatureDirac
open GaussianSpinInterpolation
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalPairMeanWeakLimit
open PureCapturePhysicalPairPowerIdentity
open SphericalPureProbeSelectedKernel SphericalPureProbeFiniteResponse
open SphericalPureProbeBaseGibbs
open PureCapturePhysicalFiniteMeasurability
open scoped Topology RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The original Gaussian Gibbs pair-power statistic is a measurable,
uniformly bounded function of the original tensor disorder. -/
theorem physical_pairPower_disorder_measurable_bounded
    {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (p : ℕ) :
    StronglyMeasurable (fun J : Disorder N μ.maxDegree =>
      ∫ z : Vector N × Vector N, (overlap z.1 z.2)^p
        ∂(gibbsLaw N β (field (mixtureCoefficients μ) J)).prod
          (gibbsLaw N β (field (mixtureCoefficients μ) J))) ∧
    (∀ J : Disorder N μ.maxDegree,
      |∫ z : Vector N × Vector N, (overlap z.1 z.2)^p
        ∂(gibbsLaw N β (field (mixtureCoefficients μ) J)).prod
          (gibbsLaw N β (field (mixtureCoefficients μ) J))| ≤ 1) := by
  let G := allDimensionGibbsKernel (N := N) (mixtureCoefficients μ) β
  let ψ : Vector N × Vector N → ℝ :=
    fun z => (clipOverlap (overlap z.1 z.2))^p
  have hψ : Continuous ψ :=
    (clipOverlap_continuous.comp overlap_joint_continuous).pow p
  have hψb (z : Vector N × Vector N) : |ψ z| ≤ 1 := by
    change |(clipOverlap (overlap z.1 z.2))^p| ≤ 1
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr (clipOverlap_mem_Icc _))
  have hpair (J : Disorder N μ.maxDegree) :
      (∫ z : Vector N × Vector N, (overlap z.1 z.2)^p
        ∂(gibbsLaw N β (field (mixtureCoefficients μ) J)).prod
          (gibbsLaw N β (field (mixtureCoefficients μ) J))) =
      ∫ z : Vector N × Vector N, ψ z ∂(G ×ₖ G) J := by
    rw [Kernel.prod_apply]
    simp only [G, allDimensionGibbsKernel_apply]
    apply integral_congr_ae
    let ν := gibbsLaw N β (field (mixtureCoefficients μ) J)
    have : IsProbabilityMeasure ν := gibbsLaw_probability hN β
      (field_contDiff (mixtureCoefficients μ) J).continuous
    have hpairSphere : ∀ᵐ z : Vector N × Vector N ∂ν.prod ν,
        ‖z.1‖^2=(N : ℝ) ∧ ‖z.2‖^2=(N : ℝ) := by
      apply (Measure.ae_prod_iff_ae_ae (by
        exact (isClosed_eq (continuous_fst.norm.pow 2) continuous_const).measurableSet.inter
          (isClosed_eq (continuous_snd.norm.pow 2) continuous_const).measurableSet)).mpr
      filter_upwards [gibbsLaw_support hN β (field (mixtureCoefficients μ) J)] with x hx
      filter_upwards [gibbsLaw_support hN β (field (mixtureCoefficients μ) J)] with y hy
      exact ⟨hx,hy⟩
    exact hpairSphere.mono fun z hz => by
      have hr := overlap_mem_Icc_of_norm_sq hN z.1 z.2 hz.1 hz.2
      simp [ψ, clipOverlap_eq_of_mem_Icc hr]
  constructor
  · have hh : StronglyMeasurable (fun J : Disorder N μ.maxDegree =>
        ∫ z : Vector N × Vector N, ψ z ∂(G ×ₖ G) J) :=
      hψ.measurable.stronglyMeasurable.integral_kernel
    convert hh using 1
    funext J
    exact hpair J
  · intro J
    rw [hpair]
    have : IsProbabilityMeasure ((G ×ₖ G) J) := by infer_instance
    have hh := norm_integral_le_of_norm_le_const
      (μ := (G ×ₖ G) J) (C := 1) (Eventually.of_forall (fun z => by
        change ‖ψ z‖ ≤ 1
        simpa only [Real.norm_eq_abs] using hψb z))
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hh

/-- The enlarged Gaussian bank at zero probe amplitude yields exactly the
literal physical pair-power moment after averaging its original block. -/
theorem extended_zeroProbe_pairPower_eq_physical
    (μ : FiniteMixture) (β : ℝ) (n p : ℕ) (hp : 2 ≤ p) :
    (∫ w : EuclideanSpace ℝ
        (ThreeCoordinate (n+2) (Coordinate (n+2) μ.maxDegree)
          (Coordinate (n+2) (pureProbe p hp).maxDegree)),
      (∫ z : Vector (n+2) × Vector (n+2), (overlap z.1 z.2)^p
        ∂(sourcePureProbeGibbs (n+2) p hp μ β w).prod
          (sourcePureProbeGibbs (n+2) p hp μ β w))
      ∂SYK.standardGaussianMeasureOnEuclidean _) =
    ∫ c, (c 0 1)^p ∂(physicalFullOverlapLaw
      (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)) := by
  let project : EuclideanSpace ℝ
      (ThreeCoordinate (n+2) (Coordinate (n+2) μ.maxDegree)
        (Coordinate (n+2) (pureProbe p hp).maxDegree)) →
      EuclideanDisorder (n+2) μ.maxDegree :=
    fun w => SphericalModel.projectGaussian Sum.inl (threeLeft w)
  have hproject_eq (w) : project w =
      SphericalModel.projectGaussian (fun i : Coordinate (n+2) μ.maxDegree =>
        Sum.inl (Sum.inl i)) w := by
    ext i
    rfl
  have hproj : HasLaw project
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate (n+2) μ.maxDegree))
      (SYK.standardGaussianMeasureOnEuclidean
        (ThreeCoordinate (n+2) (Coordinate (n+2) μ.maxDegree)
          (Coordinate (n+2) (pureProbe p hp).maxDegree))) := by
    let embed : Coordinate (n+2) μ.maxDegree →
        ThreeCoordinate (n+2) (Coordinate (n+2) μ.maxDegree)
          (Coordinate (n+2) (pureProbe p hp).maxDegree) :=
      fun i => Sum.inl (Sum.inl i)
    have hh := SphericalModel.projectGaussian_hasLaw embed
        (fun i j h => Sum.inl_injective (Sum.inl_injective h))
    change HasLaw project _ _
    rw [show project = SphericalModel.projectGaussian embed from funext hproject_eq]
    exact hh
  have hdis : HasLaw (fun w => unpackDisorder (project w))
      (disorderLaw (n+2) μ.maxDegree)
      (SYK.standardGaussianMeasureOnEuclidean
        (ThreeCoordinate (n+2) (Coordinate (n+2) μ.maxDegree)
          (Coordinate (n+2) (pureProbe p hp).maxDegree))) := by
    simpa only [Function.comp_def] using
      (unpackDisorder_hasLaw (n+2) μ.maxDegree).comp hproj
  let F : Disorder (n+2) μ.maxDegree → ℝ := fun J =>
    ∫ z : Vector (n+2) × Vector (n+2), (overlap z.1 z.2)^p
      ∂(gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)).prod
        (gibbsLaw (n+2) β (field (mixtureCoefficients μ) J))
  have hF := (physical_pairPower_disorder_measurable_bounded (N := n+2)
    (by omega) μ β p).1
  have hint := hdis.integral_comp hF.aestronglyMeasurable
  calc
    _ = ∫ w : EuclideanSpace ℝ
          (ThreeCoordinate (n+2) (Coordinate (n+2) μ.maxDegree)
            (Coordinate (n+2) (pureProbe p hp).maxDegree)),
          F (unpackDisorder (project w))
          ∂SYK.standardGaussianMeasureOnEuclidean _ := by
        apply integral_congr_ae
        exact .of_forall fun w => by
          change (∫ z : Vector (n+2) × Vector (n+2), (overlap z.1 z.2)^p
            ∂(sourcePureProbeGibbs (n+2) p hp μ β w).prod
              (sourcePureProbeGibbs (n+2) p hp μ β w)) =
            F (unpackDisorder (project w))
          rw [sourcePureProbeGibbs_eq_original hp μ β w]
    _ = ∫ J, F J ∂disorderLaw (n+2) μ.maxDegree := by
      simpa only [Function.comp_def] using hint
    _ = _ := (physicalPairPower_eq_disorderIntegral μ β n p).symm

end SlowEquilibration.SphericalPureProbePhysicalMomentTransfer

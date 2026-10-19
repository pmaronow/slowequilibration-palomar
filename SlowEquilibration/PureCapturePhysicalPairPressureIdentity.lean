-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalPairMeanDirecting
public import SlowEquilibration.SphericalGaussianInterpolation
public import SlowEquilibration.GaussianReplicaTransport

/-! Exact finite-volume covariance-pair identity for the physical
annealed Gibbs law. This is the pair mean in the source's pressure
derivative formula, without an auxiliary measure-identification premise. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalPairPressureIdentity

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalPairMeanWeakLimit
open PureCapturePhysicalFiniteMeasurability
open GaussianReplicaKernel
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

theorem physicalPairCovarianceMean_eq_disorderIntegral
    (μ : FiniteMixture) (β : ℝ) (n : ℕ) :
    (∫ c, μ.xi (c 0 1) ∂(physicalFullOverlapLaw
      (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2))) =
    ∫ J : Disorder (n+2) μ.maxDegree,
      (∫ z : Vector (n+2) × Vector (n+2), μ.xi (overlap z.1 z.2)
        ∂(gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)).prod
          (gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)))
        ∂disorderLaw (n+2) μ.maxDegree := by
  let G := allDimensionGibbsKernel (N := n+2) (mixtureCoefficients μ) β
  let d := disorderLaw (n+2) μ.maxDegree
  let F : (Fin 2 → Vector (n+2)) → ℝ :=
    fun σ => clippedPairCovariance μ (physicalFullOverlapCoordinates σ)
  have hF : Measurable F :=
    (clippedPairCovariance μ).continuous.measurable.comp
      physicalFullOverlapCoordinates_continuous.measurable
  have hFb (σ : Fin 2 → Vector (n+2)) : ‖F σ‖ ≤ μ.xi 1 := by
    change |μ.xi (clipOverlap (overlap (σ 0) (σ 1)))| ≤ μ.xi 1
    exact SlowEquilibration.DirectingPhysical.finiteMixture_xi_abs_le μ
      (by norm_num) (abs_le.mpr (clipOverlap_mem_Icc _))
  have hfull : HasLaw (physicalFullOverlapCoordinates (N := n+2) (m := 2))
      (physicalFullOverlapLaw (n := n) (m := 2) μ β)
      (physicalReplicaLaw (n := n) (m := 2) μ β) := by
    refine ⟨physicalFullOverlapCoordinates_continuous.measurable.aemeasurable, ?_⟩
    rfl
  have hmap := hfull.integral_comp
    (clippedPairCovariance μ).continuous.measurable.aestronglyMeasurable
  have hdis : (∫ σ, F σ ∂physicalReplicaLaw
      (n := n) (m := 2) μ β) =
      ∫ J, (∫ σ, F σ ∂Measure.pi (fun _ : Fin 2 => G J)) ∂d := by
    change (∫ σ, F σ ∂law d G 2) = _
    exact GaussianReplicaKernel.integral_law d G 2 F hF hFb
  have hcond (J : Disorder (n+2) μ.maxDegree) :
      (∫ σ, F σ ∂Measure.pi (fun _ : Fin 2 => G J)) =
      ∫ z : Vector (n+2) × Vector (n+2),
        μ.xi (overlap z.1 z.2)
        ∂(gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)).prod
          (gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)) := by
    let ν := gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)
    letI : IsProbabilityMeasure ν :=
      gibbsLaw_probability (by omega) β
        (field_contDiff (mixtureCoefficients μ) J).continuous
    simp only [G, allDimensionGibbsKernel_apply]
    let ψ : ℝ → ℝ := fun r => μ.xi (clipOverlap r)
    have hψ : Continuous ψ :=
      (continuous_iff_continuousAt.mpr fun r =>
        (μ.hasDerivAt_xi r).continuousAt).comp clipOverlap_continuous
    have hpair := (pair_pi_hasLaw ν (0 : Fin 2) 1 (by decide)).integral_comp
      ((hψ.measurable.comp overlap_joint_continuous.measurable).aestronglyMeasurable)
    have hleft : (∫ σ, F σ ∂Measure.pi (fun _ : Fin 2 => ν)) =
        ∫ z : Vector (n+2) × Vector (n+2), ψ (overlap z.1 z.2) ∂ν.prod ν := by
      simpa [F, ψ, clippedPairCovariance, physicalFullOverlapCoordinates]
        using hpair
    rw [hleft]
    apply integral_congr_ae
    have hpairSphere : ∀ᵐ z : Vector (n+2) × Vector (n+2) ∂ν.prod ν,
        ‖z.1‖ ^ 2 = ((n+2 : ℕ) : ℝ) ∧
          ‖z.2‖ ^ 2 = ((n+2 : ℕ) : ℝ) := by
      apply (Measure.ae_prod_iff_ae_ae (by
        exact (isClosed_eq (continuous_fst.norm.pow 2) continuous_const).measurableSet.inter
          (isClosed_eq (continuous_snd.norm.pow 2) continuous_const).measurableSet)).mpr
      filter_upwards [gibbsLaw_support (by omega) β
        (field (mixtureCoefficients μ) J)] with u hu
      filter_upwards [gibbsLaw_support (by omega) β
        (field (mixtureCoefficients μ) J)] with v hv
      exact ⟨hu, hv⟩
    exact hpairSphere.mono fun z hz => by
      have hr : overlap z.1 z.2 ∈ Icc (-1 : ℝ) 1 :=
        ⟨(overlap_mem_Icc_of_norm_sq (by omega) z.1 z.2 hz.1 hz.2).1,
          (overlap_mem_Icc_of_norm_sq (by omega) z.1 z.2 hz.1 hz.2).2⟩
      simp [ψ, clipOverlap_eq_of_mem_Icc hr]
  calc
    _ = ∫ c, clippedPairCovariance μ c
        ∂(physicalFullOverlapLaw (n := n) (m := 2) μ β :
          Measure (FullOverlapCoordinates 2)) :=
      (physicalPairCovarianceMean_eq_clipped μ β n).symm
    _ = ∫ σ, F σ ∂physicalReplicaLaw (n := n) (m := 2) μ β := hmap.symm
    _ = ∫ J, (∫ σ, F σ ∂Measure.pi (fun _ : Fin 2 => G J)) ∂d := hdis
    _ = _ := by simp_rw [hcond]; rfl

end SlowEquilibration.PureCapturePhysicalPairPressureIdentity

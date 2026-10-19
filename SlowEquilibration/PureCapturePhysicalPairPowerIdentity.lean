-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalPairPressureIdentity

@[expose] public section
noncomputable section

namespace SlowEquilibration.PureCapturePhysicalPairPowerIdentity

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

/-- Every actual finite physical overlap-power moment is the ordinary
disorder average of the true two-replica Gibbs overlap-power integral. -/
theorem physicalPairPower_eq_disorderIntegral
    (μ : FiniteMixture) (β : ℝ) (n p : ℕ) :
    (∫ c, (c 0 1)^p ∂(physicalFullOverlapLaw
      (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2))) =
    ∫ J : Disorder (n+2) μ.maxDegree,
      (∫ z : Vector (n+2) × Vector (n+2), (overlap z.1 z.2)^p
        ∂(gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)).prod
          (gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)))
        ∂disorderLaw (n+2) μ.maxDegree := by
  let G := allDimensionGibbsKernel (N := n+2) (mixtureCoefficients μ) β
  let d := disorderLaw (n+2) μ.maxDegree
  let ψ : ℝ → ℝ := fun r => (clipOverlap r)^p
  let F : (Fin 2 → Vector (n+2)) → ℝ :=
    fun σ => ψ (overlap (σ 0) (σ 1))
  have hψ : Continuous ψ := (clipOverlap_continuous.pow p)
  have hoverlap : Continuous (fun σ : Fin 2 → Vector (n+2) =>
      overlap (σ 0) (σ 1)) := by
    have hpair : Continuous (fun σ : Fin 2 → Vector (n+2) => (σ 0,σ 1)) :=
      (continuous_apply (0 : Fin 2)).prodMk (continuous_apply (1 : Fin 2))
    exact overlap_joint_continuous.comp hpair
  have hF : Measurable F := hψ.measurable.comp hoverlap.measurable
  have hFb (σ : Fin 2 → Vector (n+2)) : ‖F σ‖ ≤ 1 := by
    change |(clipOverlap (overlap (σ 0) (σ 1)))^p| ≤ 1
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr (clipOverlap_mem_Icc _))
  have hfull : HasLaw (physicalFullOverlapCoordinates (N := n+2) (m := 2))
      (physicalFullOverlapLaw (n := n) (m := 2) μ β)
      (physicalReplicaLaw (n := n) (m := 2) μ β) := by
    refine ⟨physicalFullOverlapCoordinates_continuous.measurable.aemeasurable, ?_⟩
    rfl
  have hcoord : Continuous (fun c : FullOverlapCoordinates 2 => c 0 1) :=
    (continuous_apply (1 : Fin 2)).comp (continuous_apply (0 : Fin 2))
  have hmap := hfull.integral_comp
    (hψ.measurable.comp hcoord.measurable).aestronglyMeasurable
  have hdis : (∫ σ, F σ ∂physicalReplicaLaw
      (n := n) (m := 2) μ β) =
      ∫ J, (∫ σ, F σ ∂Measure.pi (fun _ : Fin 2 => G J)) ∂d := by
    change (∫ σ, F σ ∂law d G 2) = _
    exact GaussianReplicaKernel.integral_law d G 2 F hF hFb
  have hcond (J : Disorder (n+2) μ.maxDegree) :
      (∫ σ, F σ ∂Measure.pi (fun _ : Fin 2 => G J)) =
      ∫ z : Vector (n+2) × Vector (n+2),
        (overlap z.1 z.2)^p
        ∂(gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)).prod
          (gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)) := by
    let ν := gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)
    have : IsProbabilityMeasure ν :=
      gibbsLaw_probability (by omega) β
        (field_contDiff (mixtureCoefficients μ) J).continuous
    simp only [G, allDimensionGibbsKernel_apply]
    have hpair := (pair_pi_hasLaw ν (0 : Fin 2) 1 (by decide)).integral_comp
      ((hψ.measurable.comp overlap_joint_continuous.measurable).aestronglyMeasurable)
    have hleft : (∫ σ, F σ ∂Measure.pi (fun _ : Fin 2 => ν)) =
        ∫ z : Vector (n+2) × Vector (n+2), ψ (overlap z.1 z.2) ∂ν.prod ν := by
      simpa [F, ψ] using hpair
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
        overlap_mem_Icc_of_norm_sq (by omega) z.1 z.2 hz.1 hz.2
      simp [ψ, clipOverlap_eq_of_mem_Icc hr]
  calc
    _ = ∫ c, ψ (c 0 1)
        ∂(physicalFullOverlapLaw (n := n) (m := 2) μ β :
          Measure (FullOverlapCoordinates 2)) := by
      apply integral_congr_ae
      exact (physicalFullOverlapLaw_cube_ae μ β).mono fun c hc => by
        simp [ψ, clipOverlap_eq_of_mem_Icc (hc 0 (mem_univ _) 1 (mem_univ _))]
    _ = ∫ σ, F σ ∂physicalReplicaLaw (n := n) (m := 2) μ β := hmap.symm
    _ = ∫ J, (∫ σ, F σ ∂Measure.pi (fun _ : Fin 2 => G J)) ∂d := hdis
    _ = _ := by simp_rw [hcond]; rfl

end SlowEquilibration.PureCapturePhysicalPairPowerIdentity

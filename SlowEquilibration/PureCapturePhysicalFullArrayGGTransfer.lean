-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalAsymptoticGGFromBudget

/-! Transport of physical replica observables to their full overlap-array
laws, retaining the fresh and old replicas needed by covariance GG. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalFullArrayGGTransfer

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open GaussianReplicaCalculus
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalFiniteGGDefinitions
open PureCapturePhysicalFiniteGGTransfer
open PureCapturePhysicalPairMeanWeakLimit
open SlowEquilibration.DirectingPhysical
open scoped Topology BigOperators BoundedContinuousFunction

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Integration under the literal physical full-array law is integration
of the same test of the physical Gibbs replicas' full overlaps. -/
theorem physicalFullOverlapLaw_integral_comp
    (μ : FiniteMixture) (β : ℝ) (n k : ℕ)
    (F : FullOverlapCoordinates k → ℝ) (hF : Measurable F) :
    (∫ c, F c ∂(physicalFullOverlapLaw (n := n) (m := k) μ β :
      Measure (FullOverlapCoordinates k))) =
    ∫ σ : Fin k → Vector (n+2), F (physicalFullOverlapCoordinates σ)
      ∂physicalReplicaLaw (n := n) (m := k) μ β := by
  have hfull : HasLaw (physicalFullOverlapCoordinates (N := n+2) (m := k))
      (physicalFullOverlapLaw (n := n) (m := k) μ β)
      (physicalReplicaLaw (n := n) (m := k) μ β) := by
    refine ⟨physicalFullOverlapCoordinates_continuous.measurable.aemeasurable, ?_⟩
    rfl
  simpa only [Function.comp_def] using
    (hfull.integral_comp hF.aestronglyMeasurable).symm

/-- A clipped covariance observable at any two overlap-array entries. -/
def clippedArrayCovariance (μ : FiniteMixture) {k : ℕ}
    (i j : Fin k) (c : FullOverlapCoordinates k) : ℝ :=
  μ.xi (clipOverlap (c i j))

theorem clippedArrayCovariance_continuous (μ : FiniteMixture)
    {k : ℕ} (i j : Fin k) :
    Continuous (clippedArrayCovariance μ i j : FullOverlapCoordinates k → ℝ) := by
  have hξ : Continuous μ.xi := continuous_iff_continuousAt.mpr fun r =>
    (μ.hasDerivAt_xi r).continuousAt
  have hc : Continuous (fun c : FullOverlapCoordinates k => c i j) :=
    (continuous_apply j).comp (continuous_apply i)
  exact hξ.comp (clipOverlap_continuous.comp hc)

theorem clippedArrayCovariance_abs_le (μ : FiniteMixture)
    {k : ℕ} (i j : Fin k) (c : FullOverlapCoordinates k) :
    |clippedArrayCovariance μ i j c| ≤ μ.xi 1 :=
  finiteMixture_xi_abs_le μ (by norm_num)
    (abs_le.mpr (clipOverlap_mem_Icc _))

theorem clippedArrayCovariance_physical {N k : ℕ} (μ : FiniteMixture)
    (σ : Fin k → Vector N) (i j : Fin k) (hij : i ≠ j) :
    clippedArrayCovariance μ i j (physicalFullOverlapCoordinates σ) =
      boundedPairCovariance μ (σ i) (σ j) := by
  simp [clippedArrayCovariance, physicalFullOverlapCoordinates, hij,
    boundedPairCovariance]

/-- A pair-covariance test under a full-overlap law is the identical test
under the original Gibbs replica law. -/
theorem physicalFullOverlapLaw_pair_integral_comp
    (μ : FiniteMixture) (β : ℝ) (n k : ℕ)
    (g : FullOverlapCoordinates k → ℝ) (hg : Measurable g)
    (i j : Fin k) (hij : i ≠ j) :
    (∫ c, g c * clippedArrayCovariance μ i j c
      ∂(physicalFullOverlapLaw (n := n) (m := k) μ β :
        Measure (FullOverlapCoordinates k))) =
    ∫ σ : Fin k → Vector (n+2),
      g (physicalFullOverlapCoordinates σ) *
        boundedPairCovariance μ (σ i) (σ j)
      ∂physicalReplicaLaw (n := n) (m := k) μ β := by
  rw [physicalFullOverlapLaw_integral_comp μ β n k
    (fun c => g c * clippedArrayCovariance μ i j c)
    (hg.mul (clippedArrayCovariance_continuous μ i j).measurable)]
  apply integral_congr_ae
  exact .of_forall fun σ => by
    change g (physicalFullOverlapCoordinates σ) *
        clippedArrayCovariance μ i j (physicalFullOverlapCoordinates σ) =
      g (physicalFullOverlapCoordinates σ) *
        boundedPairCovariance μ (σ i) (σ j)
    rw [clippedArrayCovariance_physical μ σ i j hij]

/-- The covariance GG defect as a functional of the complete overlap-array
law. Off-cube entries are clipped, so every covariance factor is bounded. -/
def fullArrayCovarianceGGDefect (μ : FiniteMixture) (m : ℕ)
    (g : FullOverlapCoordinates (m+1) → ℝ)
    (x : FullOverlapLawArray) : ℝ :=
  (∫ c : FullOverlapCoordinates (m+2),
      g (fullOverlapPrefix c) *
        clippedArrayCovariance μ 0 (Fin.last (m+1)) c
      ∂(x (m+2) : Measure (FullOverlapCoordinates (m+2)))) -
  (∫ c : FullOverlapCoordinates (m+1), g c
      ∂(x (m+1) : Measure (FullOverlapCoordinates (m+1)))) *
    (∫ c : FullOverlapCoordinates 2,
      clippedArrayCovariance μ 0 1 c
      ∂(x 2 : Measure (FullOverlapCoordinates 2))) / ((m : ℝ)+1) -
  (∑ j : Fin m, ∫ c : FullOverlapCoordinates (m+1),
      g c * clippedArrayCovariance μ 0 j.succ c
      ∂(x (m+1) : Measure (FullOverlapCoordinates (m+1)))) / ((m : ℝ)+1)

/-- The full-overlap-array GG defect is exactly the defect of the true
physical annealed Gibbs replicas at every finite volume. -/
theorem fullArrayCovarianceGGDefect_physical
    (μ : FiniteMixture) (β : ℝ) (n m : ℕ)
    (g : FullOverlapCoordinates (m+1) → ℝ) (hg : Measurable g) :
    fullArrayCovarianceGGDefect μ m g (physicalFullOverlapLawArray μ β n) =
      physicalCovarianceGGDefect μ β n m
        (fun σ => g (physicalFullOverlapCoordinates σ)) := by
  have hnew :
      (∫ c : FullOverlapCoordinates (m+2),
        g (fullOverlapPrefix c) *
          clippedArrayCovariance μ 0 (Fin.last (m+1)) c
        ∂(physicalFullOverlapLaw (n := n) (m := m+2) μ β :
          Measure (FullOverlapCoordinates (m+2)))) =
      ∫ σ : Fin (m+2) → Vector (n+2),
        g (physicalFullOverlapCoordinates (initialReplicas σ)) *
          boundedPairCovariance μ (σ 0) (σ (Fin.last (m+1)))
        ∂physicalReplicaLaw (n := n) (m := m+2) μ β := by
    rw [physicalFullOverlapLaw_pair_integral_comp μ β n (m+2)
      (fun c => g (fullOverlapPrefix c))
      (hg.comp fullOverlapPrefix_continuous.measurable)
      0 (Fin.last (m+1)) (by simp [Fin.last])]
    apply integral_congr_ae
    exact .of_forall fun σ => by
      change g (fullOverlapPrefix (physicalFullOverlapCoordinates σ)) *
          boundedPairCovariance μ (σ 0) (σ (Fin.last (m+1))) =
        g (physicalFullOverlapCoordinates (initialReplicas σ)) *
          boundedPairCovariance μ (σ 0) (σ (Fin.last (m+1)))
      rw [fullOverlapPrefix_physical]
      rfl
  have hmean :
      (∫ c : FullOverlapCoordinates (m+1), g c
        ∂(physicalFullOverlapLaw (n := n) (m := m+1) μ β :
          Measure (FullOverlapCoordinates (m+1)))) =
      ∫ σ : Fin (m+1) → Vector (n+2),
        g (physicalFullOverlapCoordinates σ)
          ∂physicalReplicaLaw (n := n) (m := m+1) μ β :=
    physicalFullOverlapLaw_integral_comp μ β n (m+1) g hg
  have hpair :
      (∫ c : FullOverlapCoordinates 2,
        clippedArrayCovariance μ 0 1 c
        ∂(physicalFullOverlapLaw (n := n) (m := 2) μ β :
          Measure (FullOverlapCoordinates 2))) =
      ∫ σ : Fin 2 → Vector (n+2),
        boundedPairCovariance μ (σ 0) (σ 1)
          ∂physicalReplicaLaw (n := n) (m := 2) μ β := by
    simpa only [one_mul] using
      (physicalFullOverlapLaw_pair_integral_comp μ β n 2
        (fun _ => 1) measurable_const 0 1 (by decide))
  have hold (j : Fin m) :
      (∫ c : FullOverlapCoordinates (m+1),
        g c * clippedArrayCovariance μ 0 j.succ c
        ∂(physicalFullOverlapLaw (n := n) (m := m+1) μ β :
          Measure (FullOverlapCoordinates (m+1)))) =
      ∫ σ : Fin (m+1) → Vector (n+2),
        g (physicalFullOverlapCoordinates σ) *
          boundedPairCovariance μ (σ 0) (σ j.succ)
          ∂physicalReplicaLaw (n := n) (m := m+1) μ β :=
    physicalFullOverlapLaw_pair_integral_comp μ β n (m+1) g hg 0 j.succ
      (Fin.succ_ne_zero j).symm
  unfold fullArrayCovarianceGGDefect physicalCovarianceGGDefect
    physicalFullOverlapLawArray
  rw [hnew, hmean, hpair]
  simp_rw [hold]


end SlowEquilibration.PureCapturePhysicalFullArrayGGTransfer

-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalShellReplicaTransport

/-! The unperturbed covariance GG defect written on the manuscript's
literal physical annealed replica law, with a globally bounded measurable
covariance test for subsequent weak-limit passage. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalFiniteGGDefinitions

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open GaussianReplicaCalculus GaussianPerturbationSelfAveraging
open GaussianPerturbationDeviation GaussianPerturbationIntegrated
open PureCapturePhysicalShellGG
open PureCapturePhysicalShellReplicaTransport
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalPairMeanWeakLimit
open PureCapturePhysicalFiniteMeasurability
open SlowEquilibration.DirectingPhysical
open scoped Topology BigOperators RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def boundedPairCovariance {N : ℕ} (μ : FiniteMixture)
    (x y : Vector N) : ℝ := μ.xi (clipOverlap (overlap x y))

theorem boundedPairCovariance_measurable {N : ℕ} (μ : FiniteMixture) :
    Measurable (fun z : Vector N × Vector N =>
      boundedPairCovariance μ z.1 z.2) := by
  have hξ : Continuous μ.xi := continuous_iff_continuousAt.mpr fun r =>
    (μ.hasDerivAt_xi r).continuousAt
  exact (hξ.comp (clipOverlap_continuous.comp
    overlap_joint_continuous)).measurable

theorem boundedPairCovariance_abs_le {N : ℕ} (μ : FiniteMixture)
    (x y : Vector N) : |boundedPairCovariance μ x y| ≤ μ.xi 1 :=
  finiteMixture_xi_abs_le μ (by norm_num)
    (abs_le.mpr (clipOverlap_mem_Icc _))

theorem boundedPairCovariance_shell {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (x y : Shell N) :
    boundedPairCovariance μ x.val y.val = μ.xi (overlap x.val y.val) := by
  unfold boundedPairCovariance
  rw [clipOverlap_eq_of_mem_Icc
    (overlap_mem_Icc_of_norm_sq hN x.val y.val x.property y.property)]

def physicalCovarianceGGDefect (μ : FiniteMixture) (β : ℝ)
    (n m : ℕ) (f : (Fin (m+1) → Vector (n+2)) → ℝ) : ℝ :=
  (∫ σ : Fin (m+2) → Vector (n+2),
      f (initialReplicas σ) *
        boundedPairCovariance μ (σ 0) (σ (Fin.last (m+1)))
      ∂physicalReplicaLaw (n := n) (m := m+2) μ β) -
  (∫ σ : Fin (m+1) → Vector (n+2), f σ
      ∂physicalReplicaLaw (n := n) (m := m+1) μ β) *
    (∫ σ : Fin 2 → Vector (n+2),
      boundedPairCovariance μ (σ 0) (σ 1)
      ∂physicalReplicaLaw (n := n) (m := 2) μ β) / ((m : ℝ)+1) -
  (∑ j : Fin m, ∫ σ : Fin (m+1) → Vector (n+2),
      f σ * boundedPairCovariance μ (σ 0) (σ j.succ)
      ∂physicalReplicaLaw (n := n) (m := m+1) μ β) / ((m : ℝ)+1)


end SlowEquilibration.PureCapturePhysicalFiniteGGDefinitions

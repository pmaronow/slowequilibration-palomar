-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalFiniteGGDefinitions

/-! The unperturbed covariance GG defect written on the manuscript's
literal physical annealed replica law, with a globally bounded continuous
covariance test for subsequent weak-limit passage. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalFiniteGGTransfer

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open GaussianReplicaCalculus GaussianPerturbationSelfAveraging
open GaussianPerturbationDeviation GaussianPerturbationIntegrated
open PureCapturePhysicalShellGG
open PureCapturePhysicalShellReplicaTransport
open PureCapturePhysicalFiniteGGDefinitions
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalPairMeanWeakLimit
open PureCapturePhysicalFiniteMeasurability
open SlowEquilibration.DirectingPhysical
open scoped Topology BigOperators RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The bounded physical covariance is continuous in any pair of replica coordinates. -/
theorem boundedPairCovariance_joint_continuous {N : ℕ} (μ : FiniteMixture) :
    Continuous (fun z : Vector N × Vector N => boundedPairCovariance μ z.1 z.2) := by
  have hξ : Continuous μ.xi := continuous_iff_continuousAt.mpr fun r =>
    (μ.hasDerivAt_xi r).continuousAt
  exact hξ.comp (clipOverlap_continuous.comp overlap_joint_continuous)

theorem boundedPairCovariance_replica_continuous {N k : ℕ} (μ : FiniteMixture)
    (i j : Fin k) : Continuous (fun σ : Fin k → Vector N =>
      boundedPairCovariance μ (σ i) (σ j)) := by
  have hi : Continuous (fun σ : Fin k → Vector N => σ i) := continuous_apply i
  have hj : Continuous (fun σ : Fin k → Vector N => σ j) := continuous_apply j
  have hmap : Continuous (fun σ : Fin k → Vector N => (σ i, σ j)) := hi.prodMk hj
  have hcomp : Continuous ((fun z : Vector N × Vector N => boundedPairCovariance μ z.1 z.2) ∘
    (fun σ : Fin k → Vector N => (σ i, σ j))) :=
    (boundedPairCovariance_joint_continuous μ).comp hmap
  simpa only [Function.comp_def] using hcomp

theorem boundedPairCovariance_replica_measurable {N k : ℕ} (μ : FiniteMixture)
    (i j : Fin k) : Measurable (fun σ : Fin k → Vector N =>
      boundedPairCovariance μ (σ i) (σ j)) :=
  (boundedPairCovariance_replica_continuous μ i j).measurable

/-- The true finite physical covariance GG defect has exactly the
Gaussian IBP bound of its original tensor field. -/
theorem physicalCovarianceGGDefect_abs_le
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β) (n m : ℕ)
    (f : (Fin (m+1) → Vector (n+2)) → ℝ)
    (hf : Measurable f) (hfb : ∀ σ, |f σ| ≤ 1) :
    |physicalCovarianceGGDefect μ β n m f| ≤
      (meanThermalDeviation (shellLaw (n+2))
        (shellLinear (mixtureCoefficients μ)) (fun _ => true) β +
       energyFluctuation (shellLaw (n+2))
        (shellLinear (mixtureCoefficients μ)) (fun _ => true) β) /
        (((m : ℝ)+1)*β*((n+2 : ℕ) : ℝ)) := by
  let N := n+2
  let s : Shell N → Vector N := Subtype.val
  let A : Vector N → Vector N → ℝ := boundedPairCovariance μ
  let fs : (Fin (m+1) → Shell N) → ℝ := fun σ =>
    f (GaussianReplicaKernel.mapReplicas s (m+1) σ)
  have hAb (x y : Vector N) : |A x y| ≤ μ.xi 1 :=
    boundedPairCovariance_abs_le μ x y
  have hAF {k : ℕ} (i j : Fin k) :
      Measurable (fun σ : Fin k → Vector N => A (σ i) (σ j)) :=
    boundedPairCovariance_replica_measurable μ i j
  have hprod {k : ℕ} (F : (Fin k → Vector N) → ℝ)
      (hF : Measurable F) (hFb : ∀ σ, |F σ| ≤ 1)
      (i j : Fin k) :
      ∀ σ, ‖F σ * A (σ i) (σ j)‖ ≤ μ.xi 1 := by
    intro σ
    rw [Real.norm_eq_abs, abs_mul]
    simpa only [one_mul] using mul_le_mul (hFb σ) (hAb _ _)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hfs : Measurable fs :=
    hf.comp (GaussianReplicaKernel.mapReplicas_measurable
      measurable_subtype_coe (m+1))
  have hfsb (σ : Fin (m+1) → Shell N) : |fs σ| ≤ 1 := hfb _
  let Lβ : Shell N → EuclideanDisorder N μ.maxDegree →L[ℝ] ℝ :=
    parameterLinear (shellLinear (N := N) (mixtureCoefficients μ))
      (fun _ => true) β
  have hnew : meanReplica (shellLaw N) Lβ (m+2)
      (fun σ => fs (initialReplicas σ) *
        μ.xi (overlap (σ 0).val (σ (Fin.last (m+1))).val)) =
      ∫ σ : Fin (m+2) → Vector N,
        f (initialReplicas σ) * A (σ 0) (σ (Fin.last (m+1)))
          ∂physicalReplicaLaw (n := n) (m := m+2) μ β := by
    let F : (Fin (m+2) → Vector N) → ℝ := fun σ =>
      f (initialReplicas σ) * A (σ 0) (σ (Fin.last (m+1)))
    have hF : Measurable F :=
      (hf.comp (initialReplicas_measurable (m+1))).mul (hAF 0 (Fin.last (m+1)))
    have hFb : ∀ σ, ‖F σ‖ ≤ μ.xi 1 :=
      hprod _ (hf.comp (initialReplicas_measurable (m+1))) (fun σ => hfb _) 0 _
    have ht := shellMeanReplica_eq_physicalReplicaIntegral μ β n (m+2) F hF hFb
    have heq :
        (fun σ : Fin (m+2) → Shell N =>
          fs (initialReplicas σ) *
            μ.xi (overlap (σ 0).val (σ (Fin.last (m+1))).val)) =
        (fun σ => F (GaussianReplicaKernel.mapReplicas Subtype.val (m+2) σ)) := by
      funext σ
      change f (fun i : Fin (m+1) => (σ i.castSucc).val) *
          μ.xi (overlap (σ 0).val (σ (Fin.last (m+1))).val) =
        f (fun i : Fin (m+1) => (σ i.castSucc).val) *
          boundedPairCovariance μ (σ 0).val (σ (Fin.last (m+1))).val
      rw [boundedPairCovariance_shell (by omega) μ (σ 0) (σ (Fin.last (m+1)))]
    rw [heq]
    exact ht
  have hmean : meanReplica (shellLaw N) Lβ (m+1) fs =
      ∫ σ : Fin (m+1) → Vector N, f σ
        ∂physicalReplicaLaw (n := n) (m := m+1) μ β := by
    exact shellMeanReplica_eq_physicalReplicaIntegral μ β n (m+1) f hf
      (fun σ => by simpa only [Real.norm_eq_abs] using hfb σ)
  have hpair : meanReplica (shellLaw N) Lβ 2
      (fun σ => μ.xi (overlap (σ 0).val (σ 1).val)) =
      ∫ σ : Fin 2 → Vector N, A (σ 0) (σ 1)
        ∂physicalReplicaLaw (n := n) (m := 2) μ β := by
    let F : (Fin 2 → Vector N) → ℝ := fun σ => A (σ 0) (σ 1)
    have hF : Measurable F := hAF 0 1
    have hFb : ∀ σ, ‖F σ‖ ≤ μ.xi 1 := fun σ => by
      simpa only [Real.norm_eq_abs] using hAb (σ 0) (σ 1)
    have ht := shellMeanReplica_eq_physicalReplicaIntegral μ β n 2 F hF hFb
    have heq :
        (fun σ : Fin 2 → Shell N => μ.xi (overlap (σ 0).val (σ 1).val)) =
        (fun σ => F (GaussianReplicaKernel.mapReplicas Subtype.val 2 σ)) := by
      funext σ
      exact (boundedPairCovariance_shell (by omega) μ (σ 0) (σ 1)).symm
    rw [heq]
    exact ht
  have hold (j : Fin m) : meanReplica (shellLaw N) Lβ (m+1)
      (fun σ => fs σ * μ.xi (overlap (σ 0).val (σ j.succ).val)) =
      ∫ σ : Fin (m+1) → Vector N,
        f σ * A (σ 0) (σ j.succ)
          ∂physicalReplicaLaw (n := n) (m := m+1) μ β := by
    let F : (Fin (m+1) → Vector N) → ℝ := fun σ =>
      f σ * A (σ 0) (σ j.succ)
    have hF : Measurable F := hf.mul (hAF 0 j.succ)
    have hFb : ∀ σ, ‖F σ‖ ≤ μ.xi 1 := hprod f hf hfb 0 j.succ
    have ht := shellMeanReplica_eq_physicalReplicaIntegral μ β n (m+1) F hF hFb
    have heq :
        (fun σ : Fin (m+1) → Shell N =>
          fs σ * μ.xi (overlap (σ 0).val (σ j.succ).val)) =
        (fun σ => F (GaussianReplicaKernel.mapReplicas Subtype.val (m+1) σ)) := by
      funext σ
      exact congrArg (fs σ * ·)
        (boundedPairCovariance_shell (by omega) μ (σ 0) (σ j.succ)).symm
    rw [heq]
    exact ht
  have hgg : covarianceGG (shellLaw N) Lβ
      (fun x y : Shell N => μ.xi (overlap x.val y.val)) m fs =
      physicalCovarianceGGDefect μ β n m f := by
    unfold covarianceGG physicalCovarianceGGDefect
    rw [hnew, hmean, hpair]
    simp_rw [hold]
    rfl
  rw [← hgg]
  exact shellCovarianceGG_error_le (by omega) μ hβ m fs hfs hfsb

end SlowEquilibration.PureCapturePhysicalFiniteGGTransfer

-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalShellGG
public import SlowEquilibration.GaussianGGKernelIdentity

/-! Transport of the exact-shell Gaussian replica expectations back to
the manuscript's annealed physical finite-replica laws. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalShellReplicaTransport

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open GaussianReplicaCalculus GaussianPerturbationSelfAveraging
open GaussianSpinInterpolation
open PureCapturePhysicalShellGG
open PureCapturePhysicalFullOverlapArray
open scoped Topology BigOperators RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

theorem shellMeanReplica_eq_physicalReplicaIntegral
    (μ : FiniteMixture) (β : ℝ) (n m : ℕ)
    (F : (Fin m → Vector (n+2)) → ℝ)
    (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, ‖F σ‖ ≤ C) :
    meanReplica (shellLaw (n+2))
      (parameterLinear (shellLinear (mixtureCoefficients μ))
        (fun _ => true) β) m
      (fun σ => F (GaussianReplicaKernel.mapReplicas
        (Subtype.val : Shell (n+2) → Vector (n+2)) m σ)) =
      ∫ σ, F σ ∂physicalReplicaLaw (n := n) (m := m) μ β := by
  let N := n+2
  let c := mixtureCoefficients μ
  let L := shellLinear (N := N) c
  let Lβ := parameterLinear L (fun _ => true) β
  let ν := shellLaw N
  letI : IsProbabilityMeasure ν := shellLaw_probability (by omega)
  let KG := (gibbsKernel ν Lβ).map (Subtype.val : Shell N → Vector N)
  have hL : Measurable L := shellLinear_measurable c
  have hK : 0 ≤ Real.sqrt ((N : ℝ)*μ.xi 1) := Real.sqrt_nonneg _
  have hb (x : Shell N) : ‖L x‖ ≤ Real.sqrt ((N : ℝ)*μ.xi 1) := by
    have h := shellLinear_bound (by omega : 1 ≤ N) c
      (mixtureCoefficients_nonnegative μ) x
    simpa [L, c, covariancePolynomial_mixture] using h
  have hLβ : Measurable Lβ := parameterLinear_measurable L hL (fun _ => true) β
  have hbβ : ∀ᵐ x ∂ν, ‖Lβ x‖ ≤
      (1+|β|)*Real.sqrt ((N : ℝ)*μ.xi 1) :=
    .of_forall (parameterLinear_pointwise_bound L (fun _ => true) hK hb β)
  have hKβ : 0 ≤ (1+|β|)*Real.sqrt ((N : ℝ)*μ.xi 1) := by positivity
  letI : IsMarkovKernel KG := by
    dsimp [KG]
    letI : IsMarkovKernel (gibbsKernel ν Lβ) :=
      gibbsKernel_markov ν Lβ hLβ hKβ hbβ
    exact Kernel.IsMarkovKernel.map _ measurable_subtype_coe
  have htransport := meanReplica_transport ν Lβ hLβ hKβ hbβ
    (Subtype.val : Shell N → Vector N) measurable_subtype_coe m F hF
    (fun σ => hFb _)
  have houter : StronglyMeasurable (fun g : EuclideanDisorder N μ.maxDegree =>
      ∫ σ, F σ ∂Measure.pi (fun _ : Fin m => KG g)) := by
    convert hF.stronglyMeasurable.integral_kernel
      (κ := GaussianReplicaKernel.iid KG m) using 1
    funext g
    rw [GaussianReplicaKernel.iid_apply]
  have hdis := (euclideanDisorder_hasLaw N μ.maxDegree).integral_comp
    houter.aestronglyMeasurable
  have hphysical : (∫ J : Disorder N μ.maxDegree,
      (∫ σ, F σ ∂Measure.pi (fun _ : Fin m => KG (euclideanDisorder J)))
        ∂disorderLaw N μ.maxDegree) =
      ∫ σ, F σ ∂physicalReplicaLaw (n := n) (m := m) μ β := by
    have hJ (J : Disorder N μ.maxDegree) :
        KG (euclideanDisorder J) =
          gibbsLaw N β (field c J) := by
      change ((gibbsKernel ν Lβ).map Subtype.val) (euclideanDisorder J) = _
      rw [Kernel.map_apply _ measurable_subtype_coe,
        gibbsKernel_apply ν Lβ hLβ hKβ hbβ,
        shellGibbsLaw_map (by omega) μ β,
        unpack_euclideanDisorder]
    simp_rw [hJ]
    unfold physicalReplicaLaw
    rw [GaussianReplicaKernel.integral_law _ _ m F hF hFb]
    simp [N, c, allDimensionGibbsKernel_apply]
  calc
    _ = ∫ σ, F σ ∂GaussianReplicaKernel.law
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)) KG m :=
        htransport
    _ = ∫ g : EuclideanDisorder N μ.maxDegree,
        (∫ σ, F σ ∂Measure.pi (fun _ : Fin m => KG g))
          ∂SYK.standardGaussianMeasureOnEuclidean
            (Coordinate N μ.maxDegree) := by
          rw [GaussianReplicaKernel.integral_law _ _ m F hF hFb]
    _ = ∫ J : Disorder N μ.maxDegree,
        (∫ σ, F σ ∂Measure.pi (fun _ : Fin m => KG (euclideanDisorder J)))
          ∂disorderLaw N μ.maxDegree :=
      by simpa only [Function.comp_def] using hdis.symm
    _ = _ := hphysical

end SlowEquilibration.PureCapturePhysicalShellReplicaTransport

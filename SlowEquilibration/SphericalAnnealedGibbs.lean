-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGibbsKernel
public import SlowEquilibration.SphericalOrthogonalHaar
public import SlowEquilibration.GaussianReplicaKernel
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! The one-replica Gibbs marginal after averaging the original disorder is
the actual uniform sphere probability, at every real temperature.  This is
distinct from the planted-law marginal: no likelihood tilt is used here.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalAnnealedGibbs

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalOrthogonalHaar
open SphericalAging.HardSphereDynamics
open scoped Topology RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem sphere_integral_comp_rotation {N : ℕ}
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) {f : Vector N → ℝ} (hf : StronglyMeasurable f) :
    (∫ x, f (U x) ∂sphereLaw N) = ∫ x, f x ∂sphereLaw N := by
  have h := integral_map (μ := sphereLaw N) U.continuous.measurable.aemeasurable
    hf.aestronglyMeasurable
  rw [sphereLaw_rotation_invariant U] at h
  exact h.symm

private theorem partition_precomp_rotation {N : ℕ} (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) (U : Vector N ≃ₗᵢ[ℝ] Vector N) :
    partition N β (fun x => H (U.symm x)) = partition N β H :=
  sphere_integral_comp_rotation U.symm
    ((Real.continuous_exp.comp (continuous_const.mul hH)).stronglyMeasurable)

private theorem mixtureGibbsLaw_map_rotation {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) :
    (mixtureGibbsLaw μ β J).map U = mixtureGibbsLaw μ β (rotatedDisorder U J) := by
  have hH := (fieldOfMixture_contDiff μ J).continuous
  have he : fieldOfMixture μ (rotatedDisorder U J) =
      fun x => fieldOfMixture μ J (U.symm x) :=
    funext (field_precomp_rotation (mixtureCoefficients μ) U J)
  have hHr : Continuous (fun x => fieldOfMixture μ J (U.symm x)) := hH.comp U.symm.continuous
  letI := gibbsLaw_probability hN β hH
  letI := gibbsLaw_probability hN β hHr
  unfold mixtureGibbsLaw
  rw [he]
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map U.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable,
    integral_gibbsLaw hN β hH, integral_gibbsLaw hN β hHr]
  have hc : Continuous (fun x =>
      gibbsDensity N β (fun y => fieldOfMixture μ J (U.symm y)) x * f x) :=
    (gibbsDensity_continuous β hHr).mul f.continuous
  rw [← sphere_integral_comp_rotation U hc.stronglyMeasurable]
  congr 1
  funext x
  simp only [gibbsDensity, partition_precomp_rotation β hH U, U.symm_apply_apply]

/-- The spin law obtained by first sampling the original disorder and then
one spin from its quenched Gibbs probability. -/
def annealedGibbsLaw {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) :
    Measure (Vector N) :=
  disorderGibbsKernel hN (mixtureCoefficients μ) β ∘ₘ disorderLaw N μ.maxDegree

instance annealedGibbsLaw_probability {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) : IsProbabilityMeasure (annealedGibbsLaw hN μ β) := by
  unfold annealedGibbsLaw
  infer_instance

/-- The original annealed spin law is supported on the physical sphere. -/
theorem annealedGibbsLaw_onSphere {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) :
    ∀ᵐ x ∂annealedGibbsLaw hN μ β, OnSphere x := by
  apply Measure.ae_comp_of_ae_ae
    (isClosed_eq (continuous_id.inner continuous_id) continuous_const).measurableSet
  exact .of_forall fun J => by
    rw [disorderGibbsKernel_apply]
    exact (gibbsLaw_support hN β (field (mixtureCoefficients μ) J)).mono
      (fun x hx => (onSphere_iff_norm_sq x).mpr hx)

/-- Averaging the exact Gibbs rotation identity over the law-preserving
tensor rotation proves rotation invariance of the annealed spin law. -/
theorem annealedGibbsLaw_rotation {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (U : Vector N ≃ₗᵢ[ℝ] Vector N) :
    (annealedGibbsLaw hN μ β).map U = annealedGibbsLaw hN μ β := by
  unfold annealedGibbsLaw
  rw [Measure.map_comp _ _ U.continuous.measurable]
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.bind_apply hs (Kernel.aemeasurable _)]
  have he (J : Disorder N μ.maxDegree) :
      (disorderGibbsKernel hN (mixtureCoefficients μ) β).map U J =
        disorderGibbsKernel hN (mixtureCoefficients μ) β (rotatedDisorder U J) := by
    rw [Kernel.map_apply _ U.continuous.measurable, disorderGibbsKernel_apply,
      disorderGibbsKernel_apply]
    exact mixtureGibbsLaw_map_rotation hN μ J β U
  simp_rw [he]
  exact (rotatedDisorder_hasLaw U).lintegral_comp
    ((disorderGibbsKernel hN (mixtureCoefficients μ) β).measurable_coe hs).aemeasurable

private theorem invariant_probability_eq_sphereLaw {N : ℕ} (hN : 1 ≤ N)
    (ν : Measure (Vector N)) [IsProbabilityMeasure ν]
    (hsupport : ∀ᵐ x ∂ν, OnSphere x)
    (hinv : ∀ g : OrthogonalGroup N, ν.map (action g) = ν) :
    ν = sphereLaw N := by
  have hav : SphericalOrthogonalHaar.average ν = ν := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    have hc : Continuous (fun p : OrthogonalGroup N × Vector N => f (action p.1 p.2)) :=
      f.continuous.comp (action_continuous N)
    have hi : Integrable (fun p : OrthogonalGroup N × Vector N => f (action p.1 p.2))
        ((haar N).prod ν) := Integrable.of_bound hc.stronglyMeasurable.aestronglyMeasurable
      ‖f‖ (.of_forall fun p => f.norm_coe_le_norm _)
    rw [SphericalOrthogonalHaar.average,
      integral_map (action_continuous N).measurable.aemeasurable
        f.continuous.aestronglyMeasurable, integral_prod _ hi]
    have he (g : OrthogonalGroup N) :
        (∫ x, f (action g x) ∂ν) = ∫ x, f x ∂ν := by
      have hm := integral_map (μ := ν) (φ := action g)
        ((action_continuous N).comp (continuous_const.prodMk continuous_id)).measurable.aemeasurable
        f.continuous.aestronglyMeasurable
      rw [hinv g] at hm
      exact hm.symm
    simp_rw [he]
    simp
  exact hav.symm.trans (average_eq_sphereLaw hN ν hsupport)

/-- At every real inverse temperature, the disorder-averaged one-replica
Gibbs spin has precisely the uniform sphere law. -/
theorem annealedGibbsLaw_eq_sphereLaw {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) : annealedGibbsLaw hN μ β = sphereLaw N := by
  apply invariant_probability_eq_sphereLaw hN _ (annealedGibbsLaw_onSphere hN μ β)
  intro g
  exact annealedGibbsLaw_rotation hN μ β (Unitary.linearIsometryEquiv g)

/-- The original disorder ensemble of finitely many conditionally
independent Gibbs replicas.  Their common disorder is retained. -/
def annealedReplicaLaw {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ)
    (r : ℕ) : Measure (Fin r → Vector N) :=
  GaussianReplicaKernel.law (disorderLaw N μ.maxDegree)
    (disorderGibbsKernel hN (mixtureCoefficients μ) β) r

instance annealedReplicaLaw_probability {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (r : ℕ) :
    IsProbabilityMeasure (annealedReplicaLaw hN μ β r) := by
  unfold annealedReplicaLaw
  infer_instance

/-- Exact disintegration into the original disorder law and its genuine
conditionally independent Gibbs samples. -/
theorem integral_annealedReplicaLaw {N r : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (f : (Fin r → Vector N) → ℝ)
    (hf : Integrable f (annealedReplicaLaw hN μ β r)) :
    (∫ σ, f σ ∂annealedReplicaLaw hN μ β r) =
      ∫ J : Disorder N μ.maxDegree,
        ∫ σ, f σ ∂Measure.pi (fun _ : Fin r => mixtureGibbsLaw μ β J)
        ∂disorderLaw N μ.maxDegree := by
  let G := disorderGibbsKernel hN (mixtureCoefficients μ) β
  have hfi : Integrable f
      ((GaussianReplicaKernel.iid G r ∘ₖ Kernel.const Unit (disorderLaw N μ.maxDegree)) ()) := hf
  have h := ProbabilityTheory.Kernel.integral_comp hfi
  change (∫ σ, f σ
    ∂(GaussianReplicaKernel.iid G r ∘ₖ Kernel.const Unit (disorderLaw N μ.maxDegree)) ()) =
      ∫ J : Disorder N μ.maxDegree,
        ∫ σ, f σ ∂Measure.pi (fun _ : Fin r =>
          gibbsLaw N β (field (mixtureCoefficients μ) J)) ∂disorderLaw N μ.maxDegree
  simpa only [Kernel.const_apply, GaussianReplicaKernel.iid_apply,
    disorderGibbsKernel_apply, G, mixtureGibbsLaw, fieldOfMixture] using h

/-- Every individual replica in the original disorder ensemble is
uniform, even though different replicas need not be independent. -/
theorem annealedReplica_eval_hasLaw {N r : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (i : Fin r) :
    HasLaw (fun σ : Fin r → Vector N => σ i) (sphereLaw N)
      (annealedReplicaLaw hN μ β r) where
  aemeasurable := (measurable_pi_apply i).aemeasurable
  map_eq := by
    unfold annealedReplicaLaw GaussianReplicaKernel.law
    rw [Measure.map_comp _ _ (measurable_pi_apply i)]
    have he :
        (GaussianReplicaKernel.iid (disorderGibbsKernel hN (mixtureCoefficients μ) β) r).map
            (fun σ => σ i) = disorderGibbsKernel hN (mixtureCoefficients μ) β := by
      apply Kernel.ext
      intro J
      rw [Kernel.map_apply _ (measurable_pi_apply i), GaussianReplicaKernel.iid_apply]
      exact (measurePreserving_eval
        (fun _ : Fin r => disorderGibbsKernel hN (mixtureCoefficients μ) β J) i).map_eq
    rw [he]
    exact annealedGibbsLaw_eq_sphereLaw hN μ β

/-- A spin from each of two independent disorder/Gibbs systems forms an
independent uniform sphere pair.  This conclusion does not apply to two
replicas sharing the same disorder system. -/
theorem independent_annealedReplica_pair_hasLaw {N r s : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (i : Fin r) (j : Fin s) :
    HasLaw (fun z : (Fin r → Vector N) × (Fin s → Vector N) => (z.1 i, z.2 j))
      ((sphereLaw N).prod (sphereLaw N))
      ((annealedReplicaLaw hN μ β r).prod (annealedReplicaLaw hN μ β s)) where
  aemeasurable :=
    (((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp measurable_snd)).aemeasurable
  map_eq := by
    change (((annealedReplicaLaw hN μ β r).prod (annealedReplicaLaw hN μ β s)).map
      (Prod.map (fun σ => σ i) (fun σ => σ j))) = _
    rw [← Measure.map_prod_map _ _ (measurable_pi_apply i) (measurable_pi_apply j),
      (annealedReplica_eval_hasLaw hN μ β i).map_eq,
      (annealedReplica_eval_hasLaw hN μ β j).map_eq]

end SlowEquilibration.SphericalAnnealedGibbs

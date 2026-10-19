module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalReversibility
public import SlowEquilibration.SphericalC2Cutoff
public import SlowEquilibration.SphericalInfiniteDimensional

@[expose] public section

/-! # Orthogonal transport of the actual Gibbs form

These are literal transports of the physical sphere, normalized Gibbs law
and spherical gradients, for the genuine orthogonal tensor action.
-/
namespace SlowEquilibration.SphericalRotationCovariance
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalForm SphericalDynamics SphericalReversibility
open SphericalAging.HardSphereDynamics
open scoped Topology ContDiff InnerProductSpace
variable {N : ℕ}

lemma onSphere_map (U : Vector N ≃ₗᵢ[ℝ] Vector N) {x : Vector N} (hx : OnSphere x) :
    OnSphere (U x) := by
  change inner ℝ (U x) (U x) = N
  rw [U.inner_map_map]
  exact hx

lemma sphere_integral_comp (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    {f : Vector N → ℝ} (hf : StronglyMeasurable f) :
    (∫ x, f (U x) ∂sphereLaw N) = ∫ x, f x ∂sphereLaw N := by
  have h := integral_map (μ := sphereLaw N) U.continuous.measurable.aemeasurable hf.aestronglyMeasurable
  rw [sphereLaw_rotation_invariant U] at h
  exact h.symm

lemma partition_precomp_rotation (β : ℝ) {H : Vector N → ℝ} (hH : Continuous H)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) :
    partition N β (fun x => H (U.symm x)) = partition N β H :=
  sphere_integral_comp U.symm ((Real.continuous_exp.comp (continuous_const.mul hH)).stronglyMeasurable)

/-- The actual normalized Gibbs law transforms by image under U. -/
theorem gibbsLaw_precomp_rotation (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) (U : Vector N ≃ₗᵢ[ℝ] Vector N) :
    (gibbsLaw N β H).map U = gibbsLaw N β (fun x => H (U.symm x)) := by
  letI : IsProbabilityMeasure (gibbsLaw N β H) := gibbsLaw_probability hN β hH
  have hHr : Continuous (fun x => H (U.symm x)) := hH.comp U.symm.continuous
  letI : IsProbabilityMeasure (gibbsLaw N β (fun x => H (U.symm x))) := gibbsLaw_probability hN β hHr
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map U.continuous.measurable.aemeasurable f.continuous.stronglyMeasurable.aestronglyMeasurable,
    integral_gibbsLaw hN β hH, integral_gibbsLaw hN β hHr]
  have hc : Continuous (fun x => gibbsDensity N β (fun y => H (U.symm y)) x*f x) :=
    (gibbsDensity_continuous β hHr).mul f.continuous
  have h := sphere_integral_comp U hc.stronglyMeasurable
  rw [← h]
  congr 1
  funext x
  simp only [gibbsDensity,partition_precomp_rotation β hH U,U.symm_apply_apply]

lemma mixtureGibbsLaw_rotation (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (U : Vector N ≃ₗᵢ[ℝ] Vector N) :
    (mixtureGibbsLaw μ β J).map U = mixtureGibbsLaw μ β (rotatedDisorder U J) := by
  have he : fieldOfMixture μ (rotatedDisorder U J) = fun x => fieldOfMixture μ J (U.symm x) :=
    funext (field_precomp_rotation (mixtureCoefficients μ) U J)
  unfold mixtureGibbsLaw
  rw [he]
  exact gibbsLaw_precomp_rotation hN β (fieldOfMixture_contDiff μ J).continuous U

lemma projection_map (U : Vector N ≃ₗᵢ[ℝ] Vector N) (x v : Vector N) :
    U (projection x v) = projection (U x) (U v) := by
  simp only [projection,map_sub,map_smul,U.inner_map_map]

lemma gradient_comp_rotation (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    {f : Vector N → ℝ} (hf : Differentiable ℝ f) (x : Vector N) :
    gradient (fun y => f (U y)) x = U.symm (gradient f (U x)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  have hd := ((hf (U x)).hasFDerivAt.comp x U.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).fderiv
  change (fderiv ℝ (f ∘ U) x) v = _
  rw [hd,ContinuousLinearMap.comp_apply]
  calc
    _ = inner ℝ (gradient f (U x)) (U v) := inner_gradient_left.symm
    _ = inner ℝ (U (U.symm (gradient f (U x)))) (U v) := by simp
    _ = _ := U.inner_map_map _ _

lemma surfaceGradient_comp_rotation (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    {f : Vector N → ℝ} (hf : Differentiable ℝ f) (x : Vector N) :
    surfaceGradient (fun y => f (U y)) x = U.symm (surfaceGradient f (U x)) := by
  apply U.injective
  simp only [surfaceGradient,tangentProjection_apply,gradient_comp_rotation U hf,
    projection_map,U.apply_symm_apply]

/-- The literal Dirichlet form transforms under U, by the genuine
gradient chain rule and the normalized Gibbs image law. -/
theorem dirichletForm_rotation (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    {f g : Vector N → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    dirichletForm N β (fieldOfMixture μ J) (fun x => f (U x)) (fun x => g (U x)) =
      dirichletForm N β (fieldOfMixture μ (rotatedDisorder U J)) f g := by
  unfold dirichletForm
  simp_rw [surfaceGradient_comp_rotation U (hf.differentiable (by simp)),
    surfaceGradient_comp_rotation U (hg.differentiable (by simp)),U.symm.inner_map_map]
  have hc : Continuous (fun x => inner ℝ (surfaceGradient f x) (surfaceGradient g x)) :=
    (surfaceGradient_continuous hf).inner (surfaceGradient_continuous hg)
  have h := integral_map (μ := mixtureGibbsLaw μ β J) U.continuous.measurable.aemeasurable
    hc.stronglyMeasurable.aestronglyMeasurable
  rw [mixtureGibbsLaw_rotation hN μ J β U] at h
  exact h.symm

/-- Genuine Gibbs integration by parts for the literal mixed SDE generator. -/
lemma mixedGenerator_integration_by_parts (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) {f g : Vector N → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g) :
    (∫ x, f x*mixedGenerator μ J β g x ∂mixtureGibbsLaw μ β J) =
      -dirichletForm N β (fieldOfMixture μ J) f g := by
  rw [← rotationGenerator_integration_by_parts hN β
    ((fieldOfMixture_contDiff μ J).of_le (by simp)) hf hg]
  apply integral_congr_ae
  filter_upwards [mixtureGibbsLaw_onSphere hN μ J β] with x hx
  rw [mixedGenerator_eq_rotationGenerator (by omega) μ J β hg x hx]

/-- The two actual physical generators pair correctly after rotating the
field. This follows from transported gradients and actual Gibbs integration
by parts, without a supplied generator covariance assumption. -/
theorem crossGenerator_pairing (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    {f g : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    (∫ x, mixedGenerator μ J β f x*g (U x) ∂mixtureGibbsLaw μ β J) =
      ∫ x, f x*mixedGenerator μ (rotatedDisorder U J) β g (U x) ∂mixtureGibbsLaw μ β J := by
  have hgc : ContDiff ℝ 2 (fun x => g (U x)) := hg.comp U.toContinuousLinearEquiv.contDiff
  have hfc : ContDiff ℝ 2 (fun x => f (U.symm x)) := hf.comp U.symm.toContinuousLinearEquiv.contDiff
  have hleft := mixedGenerator_integration_by_parts hN μ J β (hgc.of_le (by norm_num)) hf
  have hright := mixedGenerator_integration_by_parts hN μ (rotatedDisorder U J) β
    (hfc.of_le (by norm_num)) hg
  have hform := dirichletForm_rotation hN μ J β U (hfc.of_le (by norm_num)) (hg.of_le (by norm_num))
  have hcancel : (fun x => f (U.symm (U x)))=f := by funext x; simp
  rw [hcancel] at hform
  have hmap := integral_map (μ := mixtureGibbsLaw μ β J) U.continuous.measurable.aemeasurable
    (hfc.continuous.mul (Ito.generator_continuous β _
      (mixedGradient_contDiff μ (rotatedDisorder U J)) hg)).stronglyMeasurable.aestronglyMeasurable
  rw [mixtureGibbsLaw_rotation hN μ J β U] at hmap
  change (∫ x, f (U.symm x)*mixedGenerator μ (rotatedDisorder U J) β g x
    ∂mixtureGibbsLaw μ β (rotatedDisorder U J)) =
      ∫ x, f (U.symm (U x))*mixedGenerator μ (rotatedDisorder U J) β g (U x)
        ∂mixtureGibbsLaw μ β J at hmap
  simp only [U.symm_apply_apply] at hmap
  calc
    _ = ∫ x, g (U x)*mixedGenerator μ J β f x ∂mixtureGibbsLaw μ β J := by
      apply integral_congr_ae
      exact .of_forall fun x => mul_comm _ _
    _ = -dirichletForm N β (fieldOfMixture μ J) (fun x => g (U x)) f := hleft
    _ = -dirichletForm N β (fieldOfMixture μ J) f (fun x => g (U x)) := by
      rw [dirichletForm_symmetric]
    _ = -dirichletForm N β (fieldOfMixture μ (rotatedDisorder U J)) (fun x => f (U.symm x)) g :=
      congrArg Neg.neg hform
    _ = ∫ x, f (U.symm x)*mixedGenerator μ (rotatedDisorder U J) β g x
        ∂mixtureGibbsLaw μ β (rotatedDisorder U J) := hright.symm
    _ = _ := hmap

end
end SlowEquilibration.SphericalRotationCovariance

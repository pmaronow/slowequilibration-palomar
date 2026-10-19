-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceAxisCapHitRotation
public import SlowEquilibration.ConditionedEntranceSourceAxisDisorderAverage

/-! Rotation of the literal source cap event after integrating the spherical
start and the original Gaussian disorder. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalRotationCovariance
open SphericalAging.HardSphereDynamics
open scoped NNReal
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {N : ℕ}

theorem sourceCapHitProbability_eq_axis_integral
    (hN : 1 ≤ N) (μ : FiniteMixture)
    (hnp : μ.minDegree < μ.maxDegree)
    (Q : ℝ) (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (α : ℝ) (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (J : Disorder N μ.maxDegree) (e k β : ℝ) (H : ℝ≥0)
    (u : Vector N) (hu : OnSphere u) :
    sourceCapHitProbability μ Q hQ hnp α χ hχ β H (J,(u,(e,k))) =
      ∫ x, sourceAxisCapHitProbability μ hQ hnp J β α χ hχ e k H u x
        ∂sphereLaw N := by
  have hSource := sourceCapHitProbability_eq_actual_uniform hN μ hnp Q hQ hQ1
    α hα χ hχ β H (J,(u,(e,k))) hu
  dsimp only at hSource
  rw [hSource]
  apply integral_congr_ae
  exact .of_forall fun x =>
    (sourceAxisCapHitProbability_eq_actual hN μ hnp Q hQ hQ1 α hα χ hχ
      J e k β H u hu x).symm

theorem sourceCapHitProbability_rotated
    (hN : 1 ≤ N) (μ : FiniteMixture)
    (hnp : μ.minDegree < μ.maxDegree)
    (Q : ℝ) (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (α : ℝ) (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (J : Disorder N μ.maxDegree) (e k β : ℝ) (H : ℝ≥0)
    (u : Vector N) (hu : OnSphere u) :
    sourceCapHitProbability μ Q hQ hnp α χ hχ β H
      (rotatedDisorder U J,(U u,(e,k))) =
    sourceCapHitProbability μ Q hQ hnp α χ hχ β H
      (J,(u,(e,k))) := by
  let J' := rotatedDisorder U J
  let f : Vector N → ℝ := fun x =>
    sourceAxisCapHitProbability μ hQ hnp J' β α χ hχ e k H (U u) x
  have hf : StronglyMeasurable f :=
    ((sourceAxisCapHitProbability_measurable μ hQ hnp J' β α χ hχ e k H).comp
      (measurable_const.prodMk measurable_id)).stronglyMeasurable
  calc
    _ = ∫ x, f x ∂sphereLaw N :=
      sourceCapHitProbability_eq_axis_integral hN μ hnp Q hQ hQ1 α hα χ hχ
        J' e k β H (U u) (onSphere_map U hu)
    _ = ∫ x, f (U x) ∂sphereLaw N := (sphere_integral_comp U hf).symm
    _ = ∫ x, sourceAxisCapHitProbability μ hQ hnp J β α χ hχ e k H u x
          ∂sphereLaw N := by
      apply integral_congr_ae
      filter_upwards [sphereLaw_support hN] with x hx
      exact sourceAxisCapHitProbability_rotated hN μ hQ hnp U J β α χ hχ
        e k H u x ((onSphere_iff_norm_sq x).mpr hx)
    _ = _ := (sourceCapHitProbability_eq_axis_integral hN μ hnp Q hQ hQ1
      α hα χ hχ J e k β H u hu).symm

theorem sourceCapHitProbability_annealed_axis_rotation
    (hN : 1 ≤ N) (μ : FiniteMixture)
    (hnp : μ.minDegree < μ.maxDegree)
    (Q : ℝ) (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (α : ℝ) (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (e k β : ℝ) (H : ℝ≥0)
    (u : Vector N) (hu : OnSphere u) :
    (∫ J, sourceCapHitProbability μ Q hQ hnp α χ hχ β H
      (J,(U u,(e,k))) ∂disorderLaw N μ.maxDegree) =
    ∫ J, sourceCapHitProbability μ Q hQ hnp α χ hχ β H
      (J,(u,(e,k))) ∂disorderLaw N μ.maxDegree := by
  let f : Disorder N μ.maxDegree → ℝ := fun J =>
    sourceCapHitProbability μ Q hQ hnp α χ hχ β H (J,(U u,(e,k)))
  have hf : StronglyMeasurable f :=
    ((sourceCapHitProbability_measurable μ Q hQ hnp α χ hχ β H).comp
      (measurable_id.prodMk (measurable_const.prodMk measurable_const))).stronglyMeasurable
  have hmap := integral_map (μ := disorderLaw N μ.maxDegree)
    (rotatedDisorder_measurable U).aemeasurable hf.aestronglyMeasurable
  rw [(rotatedDisorder_hasLaw U).map_eq] at hmap
  calc
    _ = ∫ J, f (rotatedDisorder U J) ∂disorderLaw N μ.maxDegree := hmap
    _ = ∫ J, sourceCapHitProbability μ Q hQ hnp α χ hχ β H
          (J,(u,(e,k))) ∂disorderLaw N μ.maxDegree := by
      apply integral_congr_ae
      exact .of_forall fun J =>
        sourceCapHitProbability_rotated hN μ hnp Q hQ hQ1 α hα χ hχ
          U J e k β H u hu

theorem sourceCapHitProbability_annealed_axis_constant
    (hN : 1 ≤ N) (μ : FiniteMixture)
    (hnp : μ.minDegree < μ.maxDegree)
    (Q : ℝ) (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (α : ℝ) (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (e k β : ℝ) (H : ℝ≥0)
    (u v : Vector N) (hu : OnSphere u) (hv : OnSphere v) :
    (∫ J, sourceCapHitProbability μ Q hQ hnp α χ hχ β H
      (J,(u,(e,k))) ∂disorderLaw N μ.maxDegree) =
    ∫ J, sourceCapHitProbability μ Q hQ hnp α χ hχ β H
      (J,(v,(e,k))) ∂disorderLaw N μ.maxDegree := by
  have hnu := (onSphere_iff_norm_sq u).mp hu
  have hnv := (onSphere_iff_norm_sq v).mp hv
  have hnorm : ‖u‖ = ‖v‖ := by
    nlinarith [norm_nonneg u, norm_nonneg v]
  let U : Vector N ≃ₗᵢ[ℝ] Vector N := (ℝ ∙ (u-v))ᗮ.reflection
  have hUv : U u = v := Submodule.reflection_sub hnorm
  simpa only [hUv] using
    (sourceCapHitProbability_annealed_axis_rotation hN μ hnp Q hQ hQ1
      α hα χ hχ U e k β H u hu).symm

theorem sourceCapHitProbability_annealed_fixed_axis_eq_average
    (hN : 1 ≤ N) (μ : FiniteMixture)
    (hnp : μ.minDegree < μ.maxDegree)
    (Q : ℝ) (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (α : ℝ) (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (e k β : ℝ) (H : ℝ≥0)
    (u₀ : Vector N) (hu₀ : OnSphere u₀) :
    (∫ J, sourceCapHitProbability μ Q hQ hnp α χ hχ β H
      (J,(u₀,(e,k))) ∂disorderLaw N μ.maxDegree) =
    ∫ J, sourceAxisAveragedCapHitProbability μ Q hQ hnp α χ hχ β H e k J
      ∂disorderLaw N μ.maxDegree := by
  let F : Disorder N μ.maxDegree × Vector N → ℝ := fun z =>
    sourceCapHitProbability μ Q hQ hnp α χ hχ β H (z.1,(z.2,(e,k)))
  have hFm : StronglyMeasurable F :=
    ((sourceCapHitProbability_measurable μ Q hQ hnp α χ hχ β H).comp
      (measurable_fst.prodMk (measurable_snd.prodMk
        (measurable_const.prodMk measurable_const)))).stronglyMeasurable
  have hFb : ∀ z, ‖F z‖ ≤ 1 := by
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg
      (sourceCapHitProbability_mem_unit μ Q hQ hnp α χ hχ β H _).1]
    exact (sourceCapHitProbability_mem_unit μ Q hQ hnp α χ hχ β H _).2
  have hFi : Integrable F ((disorderLaw N μ.maxDegree).prod (sphereLaw N)) :=
    Integrable.of_bound hFm.aestronglyMeasurable 1 (.of_forall hFb)
  have hconst : (∫ u, ∫ J, F (J,u) ∂disorderLaw N μ.maxDegree ∂sphereLaw N) =
      ∫ J, F (J,u₀) ∂disorderLaw N μ.maxDegree := by
    apply integral_eq_const
    filter_upwards [sphereLaw_support hN] with u hu
    exact sourceCapHitProbability_annealed_axis_constant hN μ hnp Q hQ hQ1
      α hα χ hχ e k β H u u₀ ((onSphere_iff_norm_sq u).mpr hu) hu₀
  symm
  calc
    _ = ∫ J, ∫ u, F (J,u) ∂sphereLaw N ∂disorderLaw N μ.maxDegree := rfl
    _ = ∫ u, ∫ J, F (J,u) ∂disorderLaw N μ.maxDegree ∂sphereLaw N :=
      integral_integral_swap hFi
    _ = ∫ J, F (J,u₀) ∂disorderLaw N μ.maxDegree := hconst

end SlowEquilibration.ConditionedEntrance

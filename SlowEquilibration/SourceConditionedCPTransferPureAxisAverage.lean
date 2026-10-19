-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceConditionedCPTransferPureAxisRotation
public import SlowEquilibration.ConditionedEntrancePureAxisDisorderAverage

/-! Exact conversion from the proper pure axis-averaged entrance bound
to every prescribed physical axis, using original tensor isotropy. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceConditionedCPTransferPureAxisAverage

open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalRotationCovariance
open SphericalAging.HardSphereDynamics ConditionedEntrance
open SourceConditionedCPTransferPureAxisRotation
open scoped NNReal

set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {N : ℕ}

theorem pureSourceCapHitProbability_rotated (hN : 1 ≤ N)
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (α : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (e β : ℝ) (T : ℝ≥0) (u : Vector N) :
    pureSourceCapHitProbability p hp c hc Q α χ hχ β T
      (rotatedDisorder U J,(U u,(e,0))) =
      pureSourceCapHitProbability p hp c hc Q α χ hχ β T (J,(u,(e,0))) := by
  let J' := rotatedDisorder U J
  let f : Vector N → ℝ := fun x =>
    pureAxisCapHitProbability p hp c hc Q J' β α χ hχ e T (U u) x
  have hf : StronglyMeasurable f :=
    ((pureAxisCapHitProbability_measurable p hp c hc Q J' β α χ hχ e T).comp
      (measurable_const.prodMk measurable_id)).stronglyMeasurable
  calc
    _ = ∫ x, f x ∂sphereLaw N :=
      pureSourceCapHitProbability_eq_axisIntegral p hp c hc Q J' β α χ hχ e T (U u)
    _ = ∫ x, f (U x) ∂sphereLaw N := (sphere_integral_comp U hf).symm
    _ = ∫ x, pureAxisCapHitProbability p hp c hc Q J β α χ hχ e T u x
        ∂sphereLaw N := by
      apply integral_congr_ae
      filter_upwards [sphereLaw_support hN] with x hx
      exact pureAxisCapHitProbability_rotated hN p hp c hc Q U J β α χ hχ e T u x
        ((onSphere_iff_norm_sq x).mpr hx)
    _ = _ := (pureSourceCapHitProbability_eq_axisIntegral p hp c hc Q J β α χ hχ e T u).symm

theorem pureSourceCapHitProbability_annealed_axis_rotation (hN : 1 ≤ N)
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (α : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (e β : ℝ) (T : ℝ≥0) (u : Vector N) :
    (∫ J, pureSourceCapHitProbability p hp c hc Q α χ hχ β T
      (J,(U u,(e,0))) ∂disorderLaw N (FiniteMixture.pure p hp c hc).maxDegree) =
      ∫ J, pureSourceCapHitProbability p hp c hc Q α χ hχ β T
        (J,(u,(e,0))) ∂disorderLaw N (FiniteMixture.pure p hp c hc).maxDegree := by
  let μ := FiniteMixture.pure p hp c hc
  let f : Disorder N μ.maxDegree → ℝ := fun J =>
    pureSourceCapHitProbability p hp c hc Q α χ hχ β T (J,(U u,(e,0)))
  have hf : StronglyMeasurable f :=
    ((pureSourceCapHitProbability_measurable p hp c hc Q α χ hχ β T).comp
      (measurable_id.prodMk (measurable_const.prodMk measurable_const))).stronglyMeasurable
  have hmap := integral_map (μ := disorderLaw N μ.maxDegree)
    (rotatedDisorder_measurable U).aemeasurable hf.aestronglyMeasurable
  rw [(rotatedDisorder_hasLaw U).map_eq] at hmap
  calc
    _ = ∫ J, f (rotatedDisorder U J) ∂disorderLaw N μ.maxDegree := hmap
    _ = _ := integral_congr_ae (.of_forall fun J =>
      pureSourceCapHitProbability_rotated hN p hp c hc Q α χ hχ U J e β T u)

theorem pureSourceCapHitProbability_annealed_axis_constant (hN : 1 ≤ N)
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (α : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (e β : ℝ) (T : ℝ≥0) (u v : Vector N) (hu : OnSphere u) (hv : OnSphere v) :
    (∫ J, pureSourceCapHitProbability p hp c hc Q α χ hχ β T
      (J,(u,(e,0))) ∂disorderLaw N (FiniteMixture.pure p hp c hc).maxDegree) =
      ∫ J, pureSourceCapHitProbability p hp c hc Q α χ hχ β T
        (J,(v,(e,0))) ∂disorderLaw N (FiniteMixture.pure p hp c hc).maxDegree := by
  have hnu := (onSphere_iff_norm_sq u).mp hu
  have hnv := (onSphere_iff_norm_sq v).mp hv
  have hnorm : ‖u‖ = ‖v‖ := by nlinarith [norm_nonneg u,norm_nonneg v]
  let U : Vector N ≃ₗᵢ[ℝ] Vector N := (ℝ ∙ (u-v))ᗮ.reflection
  have hUv : U u = v := Submodule.reflection_sub hnorm
  simpa only [hUv] using
    (pureSourceCapHitProbability_annealed_axis_rotation hN p hp c hc Q α χ hχ
      U e β T u).symm

/-- The literal expected proper-pure source cap-hit probability at any
fixed physical axis equals its disorder-and-axis average. -/
theorem pureSourceCapHitProbability_annealed_fixed_axis_eq_average (hN : 1 ≤ N)
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (α : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (e β : ℝ) (T : ℝ≥0) (u₀ : Vector N) (hu₀ : OnSphere u₀) :
    (∫ J, pureSourceCapHitProbability p hp c hc Q α χ hχ β T
      (J,(u₀,(e,0))) ∂disorderLaw N (FiniteMixture.pure p hp c hc).maxDegree) =
      ∫ J, pureAxisAveragedCapHitProbability p hp c hc Q α χ hχ β T e J
        ∂disorderLaw N (FiniteMixture.pure p hp c hc).maxDegree := by
  let μ := FiniteMixture.pure p hp c hc
  let F : Disorder N μ.maxDegree × Vector N → ℝ := fun z =>
    pureSourceCapHitProbability p hp c hc Q α χ hχ β T (z.1,(z.2,(e,0)))
  have hFm : StronglyMeasurable F :=
    ((pureSourceCapHitProbability_measurable p hp c hc Q α χ hχ β T).comp
      (measurable_fst.prodMk (measurable_snd.prodMk
        (measurable_const.prodMk measurable_const)))).stronglyMeasurable
  have hFb : ∀ z, ‖F z‖ ≤ 1 := by
    intro z
    rw [Real.norm_eq_abs,abs_of_nonneg
      (pureSourceCapHitProbability_mem_unit p hp c hc Q α χ hχ β T _).1]
    exact (pureSourceCapHitProbability_mem_unit p hp c hc Q α χ hχ β T _).2
  have hFi : Integrable F ((disorderLaw N μ.maxDegree).prod (sphereLaw N)) :=
    Integrable.of_bound hFm.aestronglyMeasurable 1 (.of_forall hFb)
  have hconst : (∫ u, ∫ J, F (J,u) ∂disorderLaw N μ.maxDegree ∂sphereLaw N) =
      ∫ J, F (J,u₀) ∂disorderLaw N μ.maxDegree := by
    apply integral_eq_const
    filter_upwards [sphereLaw_support hN] with u hu
    exact pureSourceCapHitProbability_annealed_axis_constant hN p hp c hc Q α χ hχ
      e β T u u₀ ((onSphere_iff_norm_sq u).mpr hu) hu₀
  symm
  calc
    _ = ∫ J, ∫ u, F (J,u) ∂sphereLaw N ∂disorderLaw N μ.maxDegree := rfl
    _ = ∫ u, ∫ J, F (J,u) ∂disorderLaw N μ.maxDegree ∂sphereLaw N :=
      integral_integral_swap hFi
    _ = _ := hconst

end SlowEquilibration.SourceConditionedCPTransferPureAxisAverage

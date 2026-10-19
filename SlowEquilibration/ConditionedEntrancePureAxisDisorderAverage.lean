-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureJointCapHit

/-! A measurable disorder observable for the source's axis-averaged,
uniform-start cap-hit probability, exactly equal to the physical path
quantity controlled by the quenched exponential-horizon estimate. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalOverlapExponential
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
open SphericalAging HardSphereDynamics
set_option autoImplicit false
set_option maxHeartbeats 900000

def pureAxisAveragedCapHitProbability {N : ℕ} (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (H : ℝ≥0) (e : ℝ) (J : Disorder N (FiniteMixture.pure d hd c hc).maxDegree) : ℝ :=
  ∫ u,pureSourceCapHitProbability d hd c hc Q α χ hχ β H (J,(u,(e,0)))
    ∂sphereLaw N

theorem pureAxisAveragedCapHitProbability_measurable {N : ℕ}
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (Q : ℝ) (α : ℝ) (χ : ℝ→ℝ)
    (hχ : ContDiff ℝ 2 χ) (β : ℝ) (H : ℝ≥0) (e : ℝ) :
    Measurable (pureAxisAveragedCapHitProbability d hd c hc Q α χ hχ β H e
      (N:=N)) := by
  have hm : Measurable (fun z : Disorder N (FiniteMixture.pure d hd c hc).maxDegree×Vector N =>
      pureSourceCapHitProbability d hd c hc Q α χ hχ β H
        (z.1,(z.2,(e,0)))) :=
    (pureSourceCapHitProbability_measurable d hd c hc Q α χ hχ β H).comp (by fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem pureAxisAveragedCapHitProbability_mem_unit {N : ℕ}
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (Q : ℝ) (α : ℝ) (χ : ℝ→ℝ)
    (hχ : ContDiff ℝ 2 χ) (β : ℝ) (H : ℝ≥0) (e : ℝ)
    (J : Disorder N (FiniteMixture.pure d hd c hc).maxDegree) :
    pureAxisAveragedCapHitProbability d hd c hc Q α χ hχ β H e J ∈ Set.Icc 0 1 := by
  let : IsProbabilityMeasure (sphereLaw N) := sphereLaw_probability N
  have hm : Measurable (fun u : Vector N =>
      pureSourceCapHitProbability d hd c hc Q α χ hχ β H (J,(u,(e,0)))) :=
    (pureSourceCapHitProbability_measurable d hd c hc Q α χ hχ β H).comp (by fun_prop)
  have hi : Integrable (fun u : Vector N =>
      pureSourceCapHitProbability d hd c hc Q α χ hχ β H (J,(u,(e,0)))) (sphereLaw N) := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact .of_forall fun u => by
      rw [Real.norm_eq_abs,abs_of_nonneg
        (pureSourceCapHitProbability_mem_unit d hd c hc Q α χ hχ β H (J,(u,(e,0)))).1]
      exact (pureSourceCapHitProbability_mem_unit d hd c hc Q α χ hχ β H (J,(u,(e,0)))).2
  constructor
  · exact integral_nonneg (fun u =>
      (pureSourceCapHitProbability_mem_unit d hd c hc Q α χ hχ β H (J,(u,(e,0)))).1)
  · exact (integral_mono hi (integrable_const 1) (fun u =>
      (pureSourceCapHitProbability_mem_unit d hd c hc Q α χ hχ β H (J,(u,(e,0)))).2)).trans_eq (by simp)

end SlowEquilibration.ConditionedEntrance

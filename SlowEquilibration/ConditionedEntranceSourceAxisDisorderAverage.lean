-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceQuenchedUniformCapHitExponentialHorizon
public import SlowEquilibration.ConditionedEntranceJointSourceCapHit

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

def sourceAxisAveragedCapHitProbability {N : ℕ} (μ : FiniteMixture)
    (Q : ℝ) (hQ : 0<Q) (hnp : μ.minDegree<μ.maxDegree)
    (α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (H : ℝ≥0) (e k : ℝ) (J : Disorder N μ.maxDegree) : ℝ :=
  ∫ u,sourceCapHitProbability μ Q hQ hnp α χ hχ β H (J,(u,(e,k)))
    ∂sphereLaw N

theorem sourceAxisAveragedCapHitProbability_measurable {N : ℕ}
    (μ : FiniteMixture) (Q : ℝ) (hQ : 0<Q)
    (hnp : μ.minDegree<μ.maxDegree) (α : ℝ) (χ : ℝ→ℝ)
    (hχ : ContDiff ℝ 2 χ) (β : ℝ) (H : ℝ≥0) (e k : ℝ) :
    Measurable (sourceAxisAveragedCapHitProbability μ Q hQ hnp α χ hχ β H e k
      (N:=N)) := by
  have hm : Measurable (fun z : Disorder N μ.maxDegree×Vector N =>
      sourceCapHitProbability μ Q hQ hnp α χ hχ β H
        (z.1,(z.2,(e,k)))) :=
    (sourceCapHitProbability_measurable μ Q hQ hnp α χ hχ β H).comp (by fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem sourceAxisAveragedCapHitProbability_mem_unit {N : ℕ}
    (μ : FiniteMixture) (Q : ℝ) (hQ : 0<Q)
    (hnp : μ.minDegree<μ.maxDegree) (α : ℝ) (χ : ℝ→ℝ)
    (hχ : ContDiff ℝ 2 χ) (β : ℝ) (H : ℝ≥0) (e k : ℝ)
    (J : Disorder N μ.maxDegree) :
    sourceAxisAveragedCapHitProbability μ Q hQ hnp α χ hχ β H e k J ∈ Set.Icc 0 1 := by
  let : IsProbabilityMeasure (sphereLaw N) := sphereLaw_probability N
  have hm : Measurable (fun u : Vector N =>
      sourceCapHitProbability μ Q hQ hnp α χ hχ β H (J,(u,(e,k)))) :=
    (sourceCapHitProbability_measurable μ Q hQ hnp α χ hχ β H).comp (by fun_prop)
  have hi : Integrable (fun u : Vector N =>
      sourceCapHitProbability μ Q hQ hnp α χ hχ β H (J,(u,(e,k)))) (sphereLaw N) := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact .of_forall fun u => by
      rw [Real.norm_eq_abs,abs_of_nonneg
        (sourceCapHitProbability_mem_unit μ Q hQ hnp α χ hχ β H (J,(u,(e,k)))).1]
      exact (sourceCapHitProbability_mem_unit μ Q hQ hnp α χ hχ β H (J,(u,(e,k)))).2
  constructor
  · exact integral_nonneg (fun u =>
      (sourceCapHitProbability_mem_unit μ Q hQ hnp α χ hχ β H (J,(u,(e,k)))).1)
  · exact (integral_mono hi (integrable_const 1) (fun u =>
      (sourceCapHitProbability_mem_unit μ Q hQ hnp α χ hχ β H (J,(u,(e,k)))).2)).trans_eq (by simp)

theorem sourceAxisAveragedCapHitProbability_eq_physical {N : ℕ} (hN : 1≤N)
    (μ : FiniteMixture) (hnp : μ.minDegree<μ.maxDegree)
    (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≤1)
    (α : ℝ) (hα : 0<α) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (H : ℝ≥0) (e k : ℝ) (J : Disorder N μ.maxDegree) :
    sourceAxisAveragedCapHitProbability μ Q hQ hnp α χ hχ β H e k J =
      ∫ u,∫ x,sourceAxisCapHitProbability μ hQ hnp J β α χ hχ e k H u x
        ∂sphereLaw N ∂sphereLaw N := by
  unfold sourceAxisAveragedCapHitProbability
  apply integral_congr_ae
  filter_upwards [sphereLaw_support hN] with u hu
  have hu' : OnSphere u := (onSphere_iff_norm_sq u).mpr hu
  have hSource := sourceCapHitProbability_eq_actual_uniform hN μ hnp Q hQ hQ1
    α hα χ hχ β H (J,(u,(e,k))) hu'
  dsimp only at hSource
  have hAxis (x : Vector N) := sourceAxisCapHitProbability_eq_actual
    hN μ hnp Q hQ hQ1 α hα χ hχ J e k β H u hu' x
  calc
    sourceCapHitProbability μ Q hQ hnp α χ hχ β H (J,(u,(e,k))) =
        ∫ x,(VectorBrownian.law N).real {omega | ∃ t : ℝ≥0,t≤H ∧
          α/2≤|overlapValue u
            (SmoothKilled.process (SmoothKilled.SourceData.atSourceParameters hN μ hnp
              Q hQ hQ1 α hα χ hχ (J,(u,(e,k))) hu') β x t omega)|}
          ∂sphereLaw N := hSource
    _ = ∫ x,sourceAxisCapHitProbability μ hQ hnp J β α χ hχ e k H u x
          ∂sphereLaw N := by
        apply integral_congr_ae
        exact .of_forall fun x => (hAxis x).symm

end SlowEquilibration.ConditionedEntrance

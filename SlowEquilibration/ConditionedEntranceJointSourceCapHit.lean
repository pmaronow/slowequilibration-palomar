-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSmoothParameterCapHit
public import SlowEquilibration.SphericalJointSpatialGradient

/-! Literal joint original-disorder/axis/mark cap-hit probability for the
actual smooth source Hamiltonian and genuine uniform spherical initial law. -/
@[expose] public section
namespace SlowEquilibration.ConditionedEntrance
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalForm SphericalSmoothTensorStationarity SphericalSmoothParameter
open SphericalAging HardSphereDynamics SphericalOverlapExponential
open scoped Topology NNReal ENNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000
variable {N : ℕ}

def sourceCapHitProbability (μ : FiniteMixture) (Q : ℝ) (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (T : ℝ≥0) (p : SourceParameters N μ) : ℝ :=
  uniformCapHitProbability β (jointSpatialGradient (sourceJointHamiltonian μ Q hQ hnp α χ))
    (sourceJointSpatialGradient_contDiff μ Q hQ hnp α χ hχ) T (α/2) (p.2.1,p)

theorem sourceCapHitProbability_measurable (μ : FiniteMixture) (Q : ℝ) (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (T : ℝ≥0) :
    Measurable (sourceCapHitProbability (N:=N) μ Q hQ hnp α χ hχ β T) :=
  (uniformCapHitProbability_measurable β _ _ T (α/2)).comp (measurable_snd.fst.prodMk measurable_id)

theorem sourceCapHitProbability_mem_unit (μ : FiniteMixture) (Q : ℝ) (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (T : ℝ≥0) (p : SourceParameters N μ) :
    sourceCapHitProbability μ Q hQ hnp α χ hχ β T p ∈ Icc 0 1 :=
  uniformCapHitProbability_mem_unit β _ _ T (α/2) (p.2.1,p)

/-- This is the actual existing SourceData Brownian process at every
original parameter/initial slice, averaged against the literal uniform sphere. -/
theorem sourceCapHitProbability_eq_actual_uniform (hN : 1 ≤ N) (μ : FiniteMixture)
    (hnp : μ.minDegree < μ.maxDegree) (Q : ℝ) (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (α : ℝ) (hα : 0 < α) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (T : ℝ≥0) (p : SourceParameters N μ) (hp : OnSphere p.2.1) :
    let D := SmoothKilled.SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp
    sourceCapHitProbability μ Q hQ hnp α χ hχ β T p =
      ∫ x : Vector N,(VectorBrownian.law N).real {ω | ∃ t : ℝ≥0,t ≤ T ∧
        α/2 ≤ |overlapValue D.axis (SmoothKilled.process D β x t ω)|} ∂sphereLaw N := by
  dsimp only
  let D := SmoothKilled.SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp
  rw [sourceCapHitProbability,uniformCapHitProbability_eq_actual]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [SmoothKilled.process_ae_actual D β x] with ω he
  apply propext
  constructor <;> rintro ⟨t,ht,hh⟩ <;> refine ⟨t,ht,?_⟩
  · rw [he t,overlapValue_eq]
    exact hh
  · rw [he t,overlapValue_eq] at hh
    exact hh

/-- True finite-measure integrability over original disorder, spherical
axis and arbitrary marks, with no cap-hit or moment integrability premise. -/
theorem sourceCapHitProbability_integrable (μ : FiniteMixture) (Q : ℝ) (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (T : ℝ≥0) (ν : Measure (SourceParameters N μ)) [IsFiniteMeasure ν] :
    Integrable (sourceCapHitProbability μ Q hQ hnp α χ hχ β T) ν := by
  apply Integrable.of_bound (sourceCapHitProbability_measurable μ Q hQ hnp α χ hχ β T).aestronglyMeasurable 1
  apply ae_of_all
  intro p
  rw [Real.norm_eq_abs,abs_of_nonneg (sourceCapHitProbability_mem_unit μ Q hQ hnp α χ hχ β T p).1]
  exact (sourceCapHitProbability_mem_unit μ Q hQ hnp α χ hχ β T p).2

end
end SlowEquilibration.ConditionedEntrance

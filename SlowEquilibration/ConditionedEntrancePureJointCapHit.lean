-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSmoothParameterCapHit
public import SlowEquilibration.ConditionedEntrancePureJointHamiltonian
public import SlowEquilibration.SphericalOverlapExponentialGridLaw

/-! Literal proper-pure smooth-source joint cap hitting, with the true
two-atom scalar-value posterior correction and the actual Brownian law. -/
@[expose] public section
namespace SlowEquilibration.ConditionedEntrance
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalForm SphericalSmoothTensorStationarity SphericalSmoothParameter
open SphericalOverlapExponential SphericalAging HardSphereDynamics
open scoped Topology NNReal ENNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000
variable {N : ℕ}

def pureSourceCapHitProbability (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ) (β : ℝ) (T : ℝ≥0)
    (q : SourceParameters N (FiniteMixture.pure p hp c hc)) : ℝ :=
  uniformCapHitProbability β (jointSpatialGradient (pureSourceJointHamiltonian p hp c hc Q α χ))
    (pureSourceJointSpatialGradient_contDiff p hp c hc Q α χ hχ) T (α/2) (q.2.1,q)

theorem pureSourceCapHitProbability_measurable (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ) (β : ℝ) (T : ℝ≥0) :
    Measurable (pureSourceCapHitProbability (N:=N) p hp c hc Q α χ hχ β T) :=
  (uniformCapHitProbability_measurable β _ _ T (α/2)).comp (measurable_snd.fst.prodMk measurable_id)

theorem pureSourceCapHitProbability_mem_unit (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ) (β : ℝ) (T : ℝ≥0)
    (q : SourceParameters N (FiniteMixture.pure p hp c hc)) :
    pureSourceCapHitProbability p hp c hc Q α χ hχ β T q ∈ Icc 0 1 :=
  uniformCapHitProbability_mem_unit β _ _ T (α/2) (q.2.1,q)

theorem pureSourceCapHitProbability_eq_actual_uniform (hN : 1 ≤ N)
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) (Q α : ℝ)
    (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ) (β : ℝ) (T : ℝ≥0)
    (q : SourceParameters N (FiniteMixture.pure p hp c hc)) :
    let H := pureSourceSmoothCutoffField p hp c hc Q q.1 q.2.1 q.2.2.1 α χ
    let hH := pureSourceSmoothCutoffField_contDiff hN p hp c hc Q q.1 q.2.1 q.2.2.1 α χ hχ
    pureSourceCapHitProbability p hp c hc Q α χ hχ β T q =
      ∫ x : Vector N,(VectorBrownian.law N).real {ω | ∃ t : ℝ≥0,t ≤ T ∧ α/2 ≤
        |overlapValue q.2.1 (jointPhysicalProcess β (smoothGradient H hH) (smoothGradient_contDiff H hH) x t ω)|}
        ∂sphereLaw N := by
  dsimp only
  let H := pureSourceSmoothCutoffField p hp c hc Q q.1 q.2.1 q.2.2.1 α χ
  let hH := pureSourceSmoothCutoffField_contDiff hN p hp c hc Q q.1 q.2.1 q.2.2.1 α χ hχ
  rw [pureSourceCapHitProbability,uniformCapHitProbability_eq_actual]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [jointPhysicalProcess_ae_actual β (smoothGradient H hH) (smoothGradient_contDiff H hH) x] with ω he
  apply propext
  constructor <;> rintro ⟨t,ht,hh⟩ <;> refine ⟨t,ht,?_⟩
  · rw [he t,overlapValue_eq]
    exact hh
  · rw [he t,overlapValue_eq] at hh
    exact hh

theorem pureSourceCapHitProbability_integrable (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ) (β : ℝ) (T : ℝ≥0)
    (ν : Measure (SourceParameters N (FiniteMixture.pure p hp c hc))) [IsFiniteMeasure ν] :
    Integrable (pureSourceCapHitProbability p hp c hc Q α χ hχ β T) ν := by
  apply Integrable.of_bound (pureSourceCapHitProbability_measurable p hp c hc Q α χ hχ β T).aestronglyMeasurable 1
  apply ae_of_all
  intro q
  rw [Real.norm_eq_abs,abs_of_nonneg (pureSourceCapHitProbability_mem_unit p hp c hc Q α χ hχ β T q).1]
  exact (pureSourceCapHitProbability_mem_unit p hp c hc Q α χ hχ β T q).2

end
end SlowEquilibration.ConditionedEntrance

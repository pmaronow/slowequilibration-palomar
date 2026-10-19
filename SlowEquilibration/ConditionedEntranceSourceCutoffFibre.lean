-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceJointSourceCapHit
public import SlowEquilibration.ConditionedEntranceSourceJointKilling
public import SlowEquilibration.ConditionedEntranceSmoothKilledSemigroup

/-! The jointly measurable one-start source cutoff probability is exactly
the physical Brownian cap-hit probability on spherical axes. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalSmoothTensorStationarity
open SphericalSmoothParameter SphericalOverlapExponential
open SphericalAging HardSphereDynamics SmoothKilled
open scoped NNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 700000

def sourceCapHitFibre {N : ℕ} (μ : FiniteMixture) (Q : ℝ) (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (α : ℝ) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ 2 χ) (β : ℝ) (H : ℝ≥0)
    (z : SourceParameters N μ × Vector N) : ℝ :=
  capHitProbability β
    (jointSpatialGradient (sourceJointHamiltonian μ Q hQ hnp α χ))
    (sourceJointSpatialGradient_contDiff μ Q hQ hnp α χ hχ)
    H (α/2) (z.1.2.1,(z.1,z.2))

theorem sourceCapHitFibre_measurable {N : ℕ} (μ : FiniteMixture)
    (Q : ℝ) (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (α : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (H : ℝ≥0) :
    Measurable (sourceCapHitFibre (N:=N) μ Q hQ hnp α χ hχ β H) := by
  unfold sourceCapHitFibre
  exact (capHitProbability_measurable β _ _ H (α/2)).comp
    (measurable_fst.snd.fst.prodMk (measurable_fst.prodMk measurable_snd))

theorem sourceCapHitProbability_eq_integral_fibre {N : ℕ}
    (μ : FiniteMixture) (Q : ℝ) (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (α : ℝ) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ 2 χ) (β : ℝ) (H : ℝ≥0)
    (p : SourceParameters N μ) :
    sourceCapHitProbability μ Q hQ hnp α χ hχ β H p =
      ∫ x, sourceCapHitFibre μ Q hQ hnp α χ hχ β H (p,x) ∂sphereLaw N := rfl

theorem sourceCapHitFibre_mem_unit {N : ℕ} (μ : FiniteMixture)
    (Q : ℝ) (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (α : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (H : ℝ≥0) (z : SourceParameters N μ × Vector N) :
    sourceCapHitFibre μ Q hQ hnp α χ hχ β H z ∈ Set.Icc 0 1 :=
  capHitProbability_mem_unit β _ _ H (α/2) _

theorem sourceCapHitFibre_eq_actual {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (hnp : μ.minDegree < μ.maxDegree)
    (Q : ℝ) (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (α : ℝ) (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (H : ℝ≥0) (p : SourceParameters N μ)
    (hp : OnSphere p.2.1) (x : Vector N) :
    let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp
    sourceCapHitFibre μ Q hQ hnp α χ hχ β H (p,x) =
      (VectorBrownian.law N).real {ω | ∃ t : ℝ≥0, t ≤ H ∧
        α/2 ≤ |overlapValue p.2.1 (SmoothKilled.process D β x t ω)|} := by
  dsimp only
  let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp
  rw [sourceCapHitFibre,capHitProbability_eq_actual]
  apply measureReal_congr
  filter_upwards [SmoothKilled.process_ae_actual D β x] with ω he
  apply propext
  constructor <;> rintro ⟨t,ht,hh⟩ <;> refine ⟨t,ht,?_⟩
  · rw [he t,overlapValue_eq]
    exact hh
  · rw [he t,overlapValue_eq] at hh
    exact hh

end SlowEquilibration.ConditionedEntrance

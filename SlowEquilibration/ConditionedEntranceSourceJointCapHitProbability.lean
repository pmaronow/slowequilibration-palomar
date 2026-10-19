-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceJointUniformFiringResolvent
public import SlowEquilibration.SphericalSmoothParameterCapHit

/-! Measurable literal cap-hitting probabilities for the mixed source family
when the physical cap axis also indexes the conditioned source field. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
open SphericalAging HardSphereDynamics SmoothKilled PhysicalHitting FeynmanKac
open SphericalSmoothParameter SphericalOverlapExponential
open SphericalSmoothTensorStationarity
set_option autoImplicit false
set_option maxHeartbeats 900000

def sourceAxisCapHitProbability {N : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (J : Disorder N μ.maxDegree) (β α : ℝ) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ 2 χ) (e k : ℝ) (H : ℝ≥0)
    (u x : Vector N) : ℝ :=
  let g := jointSpatialGradient (fun z : Vector N × Vector N =>
    sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2)
  capHitProbability β g
    (mixedSourceAxisGradient_contDiff μ hQ hnp J α χ hχ e k)
    H (α / 2) (u,(u,x))

theorem sourceAxisCapHitProbability_measurable {N : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (J : Disorder N μ.maxDegree) (β α : ℝ) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ 2 χ) (e k : ℝ) (H : ℝ≥0) :
    Measurable (fun z : Vector N × Vector N =>
      sourceAxisCapHitProbability μ hQ hnp J β α χ hχ e k H z.1 z.2) := by
  unfold sourceAxisCapHitProbability
  exact (capHitProbability_measurable β _
    (mixedSourceAxisGradient_contDiff μ hQ hnp J α χ hχ e k)
    H (α / 2)).comp (by fun_prop)

theorem sourceAxisCapHitProbability_mem_unit {N : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (J : Disorder N μ.maxDegree) (β α : ℝ) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ 2 χ) (e k : ℝ) (H : ℝ≥0)
    (u x : Vector N) :
    sourceAxisCapHitProbability μ hQ hnp J β α χ hχ e k H u x ∈ Set.Icc 0 1 := by
  unfold sourceAxisCapHitProbability
  exact capHitProbability_mem_unit β _
    (mixedSourceAxisGradient_contDiff μ hQ hnp J α χ hχ e k)
    H (α / 2) (u,(u,x))

/-- At each sphere axis, the measurable cap-hitting probability is the
literal Brownian probability for the actual source process. -/
theorem sourceAxisCapHitProbability_eq_actual {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (hnp : μ.minDegree < μ.maxDegree)
    (Q : ℝ) (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (α : ℝ) (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (J : Disorder N μ.maxDegree) (e k β : ℝ) (H : ℝ≥0)
    (u : Vector N) (hu : OnSphere u) (x : Vector N) :
    sourceAxisCapHitProbability μ hQ hnp J β α χ hχ e k H u x =
      (VectorBrownian.law N).real {omega | ∃ t : ℝ≥0,t ≤ H ∧
        α / 2 ≤ |overlapValue u
          (SmoothKilled.process
            (SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ
              (J,(u,(e,k))) hu) β x t omega)|} := by
  let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ
    (J,(u,(e,k))) hu
  let g := jointSpatialGradient (fun z : Vector N × Vector N =>
    sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2)
  let hg := mixedSourceAxisGradient_contDiff μ hQ hnp J α χ hχ e k
  have hgEq : (fun y => g (u,y)) =
      smoothGradient D.hamiltonian D.hamiltonian_contDiff := rfl
  have hActual := capHitProbability_eq_actual β g hg H (α / 2) (u,(u,x))
  change capHitProbability β g hg H (α / 2) (u,(u,x)) =
    (VectorBrownian.law N).real {omega | ∃ t : ℝ≥0,t ≤ H ∧
      α / 2 ≤ |overlapValue u (SmoothKilled.process D β x t omega)|}
  rw [hActual]
  apply measureReal_congr
  filter_upwards [SmoothKilled.process_ae_actual D β x] with omega he
  apply propext
  constructor <;> rintro ⟨t,ht,hh⟩ <;> refine ⟨t,ht,?_⟩
  · simpa only [hgEq,overlapValue_eq,SphericalModel.overlap,he t] using hh
  · simpa only [hgEq,overlapValue_eq,SphericalModel.overlap,he t] using hh

end SlowEquilibration.ConditionedEntrance

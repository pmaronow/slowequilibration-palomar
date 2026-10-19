-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceGlobalTiltAeFibre
public import SlowEquilibration.ConditionedEntranceJointSignedReducedEnergy

/-! The physical source resolvent bounds on every Gibbs fibre are also
the a.e. bounds under the single globally normalized source tilt. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SphericalAging.HardSphereDynamics
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 400000

theorem source_joint_reference_globalTilt_bounds
    {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    (hnp : μ.minDegree < μ.maxDegree) (Q : ℝ) (hQ : 0 < Q)
    (α : ℝ) (χ : ℝ → ℝ) (hχ : Continuous χ)
    (β : ℝ) (J : Disorder N μ.maxDegree) (e k : ℝ)
    (F U : SourceParameters N μ × Vector N → ℝ)
    (hF : StronglyMeasurable F) (hU : StronglyMeasurable U)
    (hphys : ∀ v : Vector N, OnSphere v →
      ∀ᵐ x ∂gibbsLaw N β
        (sourceSmoothCutoffField μ Q hQ hnp J v e k α χ),
        1 ≤ F ((J,(v,(e,k))),x) ∧
        0 ≤ U ((J,(v,(e,k))),x) ∧ U ((J,(v,(e,k))),x) ≤ 1)
    (M : ℝ) :
    let H₀ := fieldOfMixture μ J
    let H : Vector N → Vector N → ℝ := fun v x =>
      sourceSmoothCutoffField μ Q hQ hnp J v e k α χ x
    let w : Vector N × Vector N → ℝ := fun z =>
      β*(H z.1 z.2-H₀ z.2)
    ∀ᵐ z ∂normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H₀)) w M,
      1 ≤ F ((J,(z.1,(e,k))),z.2) ∧
      0 ≤ U ((J,(z.1,(e,k))),z.2) ∧
        U ((J,(z.1,(e,k))),z.2) ≤ 1 := by
  dsimp only
  let H₀ := fieldOfMixture μ J
  let H : Vector N → Vector N → ℝ := fun v x =>
    sourceSmoothCutoffField μ Q hQ hnp J v e k α χ x
  let w : Vector N × Vector N → ℝ := fun z =>
    β*(H z.1 z.2-H₀ z.2)
  let P : Vector N × Vector N → Prop := fun z =>
    1 ≤ F ((J,(z.1,(e,k))),z.2) ∧
    0 ≤ U ((J,(z.1,(e,k))),z.2) ∧
      U ((J,(z.1,(e,k))),z.2) ≤ 1
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff μ J).continuous
  have hH : Continuous (fun z : Vector N × Vector N => H z.1 z.2) :=
    (sourceSmoothCutoffField_jointContinuous μ Q hQ hnp α χ hχ).comp
      (show Continuous (fun z : Vector N × Vector N =>
        (((J,(z.1,(e,k))),z.2) : SourceParameters N μ × Vector N)) by fun_prop)
  have hpair : Measurable (fun z : Vector N × Vector N =>
      (((J,(z.1,(e,k))),z.2) : SourceParameters N μ × Vector N)) := by fun_prop
  have hFm : Measurable (fun z : Vector N × Vector N =>
      F ((J,(z.1,(e,k))),z.2)) := (hF.comp_measurable hpair).measurable
  have hUm : Measurable (fun z : Vector N × Vector N =>
      U ((J,(z.1,(e,k))),z.2)) := (hU.comp_measurable hpair).measurable
  have hPm : MeasurableSet {z | P z} := by
    dsimp only [P]
    exact (measurableSet_le measurable_const hFm).inter
      ((measurableSet_le measurable_const hUm).inter
        (measurableSet_le hUm measurable_const))
  exact ae_globalTilt_of_gibbs_fibres hN β H₀ hH₀ H hH P hPm hphys w M

end SlowEquilibration.ConditionedEntrance

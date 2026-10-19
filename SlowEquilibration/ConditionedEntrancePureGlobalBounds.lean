-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceGlobalTiltAeFibre
public import SlowEquilibration.ConditionedEntrancePureJointSignedReducedEnergy

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

theorem pure_joint_reference_globalTilt_bounds
    {N : ℕ} (hN : 1 ≤ N) (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (α : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (J : Disorder N (FiniteMixture.pure d hd c hc).maxDegree) (e : ℝ)
    (F U : SourceParameters N (FiniteMixture.pure d hd c hc) × Vector N → ℝ)
    (hF : StronglyMeasurable F) (hU : StronglyMeasurable U)
    (hphys : ∀ v : Vector N, OnSphere v →
      ∀ᵐ x ∂gibbsLaw N β
        (pureSourceSmoothCutoffField d hd c hc Q J v e α χ),
        1 ≤ F ((J,(v,(e,0))),x) ∧
        0 ≤ U ((J,(v,(e,0))),x) ∧ U ((J,(v,(e,0))),x) ≤ 1)
    (M : ℝ) :
    let H₀ := fieldOfMixture (FiniteMixture.pure d hd c hc) J
    let H : Vector N → Vector N → ℝ := fun v x =>
      pureSourceSmoothCutoffField d hd c hc Q J v e α χ x
    let w : Vector N × Vector N → ℝ := fun z =>
      β*(H z.1 z.2-H₀ z.2)
    ∀ᵐ z ∂normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H₀)) w M,
      1 ≤ F ((J,(z.1,(e,0))),z.2) ∧
      0 ≤ U ((J,(z.1,(e,0))),z.2) ∧
        U ((J,(z.1,(e,0))),z.2) ≤ 1 := by
  dsimp only
  let H₀ := fieldOfMixture (FiniteMixture.pure d hd c hc) J
  let H : Vector N → Vector N → ℝ := fun v x =>
    pureSourceSmoothCutoffField d hd c hc Q J v e α χ x
  let w : Vector N × Vector N → ℝ := fun z =>
    β*(H z.1 z.2-H₀ z.2)
  let P : Vector N × Vector N → Prop := fun z =>
    1 ≤ F ((J,(z.1,(e,0))),z.2) ∧
    0 ≤ U ((J,(z.1,(e,0))),z.2) ∧
      U ((J,(z.1,(e,0))),z.2) ≤ 1
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff (FiniteMixture.pure d hd c hc) J).continuous
  have hH : Continuous (fun z : Vector N × Vector N => H z.1 z.2) := by
    have hMap : Continuous (fun z : Vector N × Vector N =>
        ((J,(z.1,(e,(0 : ℝ)))),z.2)) := by fun_prop
    exact (pureSourceJointHamiltonian_contDiff d hd c hc Q α χ hχ).continuous.comp hMap
  have hpair : Measurable (fun z : Vector N × Vector N =>
      (((J,(z.1,(e,0))),z.2) : SourceParameters N (FiniteMixture.pure d hd c hc) × Vector N)) := by fun_prop
  have hFm : Measurable (fun z : Vector N × Vector N =>
      F ((J,(z.1,(e,0))),z.2)) := (hF.comp_measurable hpair).measurable
  have hUm : Measurable (fun z : Vector N × Vector N =>
      U ((J,(z.1,(e,0))),z.2)) := (hU.comp_measurable hpair).measurable
  have hPm : MeasurableSet {z | P z} := by
    dsimp only [P]
    exact (measurableSet_le measurable_const hFm).inter
      ((measurableSet_le measurable_const hUm).inter
        (measurableSet_le hUm measurable_const))
  exact ae_globalTilt_of_gibbs_fibres hN β H₀ hH₀ H hH P hPm hphys w M

end SlowEquilibration.ConditionedEntrance

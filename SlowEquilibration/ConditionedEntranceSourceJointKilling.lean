-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceJointHamiltonian
public import SlowEquilibration.ConditionedEntrancePhysicalHittingSource
public import SlowEquilibration.SphericalJointKilledVariational

/-! Literal source parameter data, actual jointly continuous cap killing,
and the common spherical variational solution for the true source fields. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SphericalOverlapExponential
open SphericalAging.HardSphereDynamics
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

theorem capKilling_jointContinuous (α : ℝ) :
    Continuous (fun z : Vector N×Vector N => PhysicalHitting.capKilling α z.1 z.2) := by
  have hr : Continuous (fun z : Vector N×Vector N => overlapValue z.1 z.2) := by
    simpa only [overlapValue_eq] using
      (continuous_inner (𝕜:=ℝ) (E:=Vector N)).div_const (N : ℝ)
  exact ((SphericalCapCutoff.cutoff_contDiff _ _).continuous.comp hr).add
    ((SphericalCapCutoff.cutoff_contDiff _ _).continuous.comp hr.neg)

def sourceJointHamiltonian (μ : FiniteMixture) (Q : ℝ) (hQ : 0<Q)
    (hnp : μ.minDegree<μ.maxDegree) (α : ℝ) (χ : ℝ→ℝ) : SourceParameters N μ×Vector N→ℝ :=
  fun z => sourceSmoothCutoffField μ Q hQ hnp z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 α χ z.2

theorem sourceJointHamiltonian_continuous (μ : FiniteMixture) (Q : ℝ) (hQ : 0<Q)
    (hnp : μ.minDegree<μ.maxDegree) (α : ℝ) (χ : ℝ→ℝ) (hχ : Continuous χ) :
    Continuous (sourceJointHamiltonian (N:=N) μ Q hQ hnp α χ) :=
  sourceSmoothCutoffField_jointContinuous μ Q hQ hnp α χ hχ

def sourceJointCapKilling (μ : FiniteMixture) (α : ℝ) : SourceParameters N μ×Vector N→ℝ :=
  fun z => PhysicalHitting.capKilling α z.1.2.1 z.2

theorem sourceJointCapKilling_continuous (μ : FiniteMixture) (α : ℝ) :
    Continuous (sourceJointCapKilling (N:=N) μ α) := by
  have hm : Continuous (fun z : SourceParameters N μ×Vector N => (z.1.2.1,z.2)) :=
    continuous_fst.snd.fst.prodMk continuous_snd
  have hc := (capKilling_jointContinuous α).comp hm
  exact hc

theorem sourceJointCapKilling_nonnegative (μ : FiniteMixture) (α : ℝ)
    (z : SourceParameters N μ×Vector N) : 0 ≤ sourceJointCapKilling μ α z :=
  PhysicalHitting.capKilling_nonneg α z.1.2.1 z.2

def sourceJointKilledSolution (hN : 1≤N) (μ : FiniteMixture) (Q : ℝ) (hQ : 0<Q)
    (hnp : μ.minDegree<μ.maxDegree) (α : ℝ) (χ : ℝ→ℝ) (hχ : Continuous χ) (β θ : ℝ)
    (p : SourceParameters N μ) : sphericalSobolevGraph hN 0 (fun _ => 0) continuous_const :=
  jointKilledSolution hN β θ (sourceJointHamiltonian μ Q hQ hnp α χ) (sourceJointCapKilling μ α)
    (sourceJointHamiltonian_continuous μ Q hQ hnp α χ hχ) (sourceJointCapKilling_continuous μ α) p

theorem sourceJointKilledSolution_continuous (hN : 1≤N) (μ : FiniteMixture) (Q : ℝ) (hQ : 0<Q)
    (hnp : μ.minDegree<μ.maxDegree) (α : ℝ) (χ : ℝ→ℝ) (hχ : Continuous χ) (β θ : ℝ) (hθ : 0<θ) :
    Continuous (sourceJointKilledSolution hN μ Q hQ hnp α χ hχ β θ) :=
  jointKilledSolution_continuous hN β θ hθ _ _
    (sourceJointHamiltonian_continuous μ Q hQ hnp α χ hχ) (sourceJointCapKilling_continuous μ α)
    (sourceJointCapKilling_nonnegative μ α)

def SmoothKilled.SourceData.atSourceParameters (hN : 1≤N) (μ : FiniteMixture)
    (hnp : μ.minDegree<μ.maxDegree) (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≤1)
    (α : ℝ) (hα : 0<α) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (p : SourceParameters N μ) (hp : OnSphere p.2.1) : SmoothKilled.SourceData N where
  dimension_ge_one := hN
  mixture := μ
  nonpure := hnp
  Q := Q
  Q_pos := hQ
  Q_le_one := hQ1
  disorder := p.1
  axis := p.2.1
  axis_onSphere := hp
  energyMark := p.2.2.1
  radialMark := p.2.2.2
  cutoffScale := α
  cutoffScale_pos := hα
  cutoff := χ
  cutoff_smooth := hχ

end SlowEquilibration.ConditionedEntrance

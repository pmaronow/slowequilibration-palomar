-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceJointCapHitProbability
public import SlowEquilibration.ConditionedEntrancePhysicalHittingSourceCutoff

/-! The literal regular-source hit event is controlled by the same joint
physical cap-firing random variable used in the uniform resolvent bound. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalOverlapExponential
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
open SphericalAging HardSphereDynamics SmoothKilled PhysicalHitting FeynmanKac
set_option autoImplicit false
set_option maxHeartbeats 900000

theorem source_axis_cap_hit_exposure_le_joint_firing
    {N : ℕ} (hN : 1≤N) (μ : FiniteMixture)
    (hnp : μ.minDegree<μ.maxDegree) (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≤1)
    (α : ℝ) (hα : 0<α) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (hβ : 0≤β) (θ : ℝ≥0) (J : Disorder N μ.maxDegree)
    (hJ : J ∈ regularDisorder)
    (e k : ℝ) (u₀ : Vector N) (hu₀ : OnSphere u₀)
    (u x : Vector N) (hu : OnSphere u) (hx : OnSphere x)
    (H T : ℝ≥0) (hT : 0<T)
    (hsmall : 4 * (1 + β * sourceGradientConstant μ Q e k α χ hχ) * (T : ℝ) ≤ α / 12) :
    let D₀ := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ
      (J,(u₀,(e,k))) hu₀
    let κ : Vector N×Vector N→ℝ := fun z => capKilling α z.1 z.2
    let Y := sourceData_axisJointProcess D₀ β
    exposureFactor (θ : ℝ) H T *
      (sourceAxisCapHitProbability μ hQ hnp J β α χ hχ e k H u x -
        (gridSize H T : ℝ) *
          (2 * Real.exp (-(N : ℝ) * (α / 12)^2 / (16 * (T : ℝ))))) ≤
      ∫ omega,finiteDiscountedMass κ Y (θ : ℝ) (H+T) ((u,x),omega)
        ∂VectorBrownian.law N := by
  dsimp only
  let D₀ := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ
    (J,(u₀,(e,k))) hu₀
  let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ
    (J,(u,(e,k))) hu
  let κ : Vector N×Vector N→ℝ := fun z => capKilling α z.1 z.2
  let Y := sourceData_axisJointProcess D₀ β
  have hPhysical := regular_source_hitting_discounted_mass D hJ hβ x hx hα
    θ.coe_nonneg H T hT hsmall
  rw [← source_finiteDiscountedMass_expectation_eq D β (capKilling α D.axis)
    (capKilling_contDiff α D.axis).continuous (capKilling_nonneg α D.axis)
    (capKilling_le_one hα D.axis) θ.coe_nonneg (H+T) x] at hPhysical
  have hHit := sourceAxisCapHitProbability_eq_actual hN μ hnp Q hQ hQ1 α hα
    χ hχ J e k β H u hu x
  change sourceAxisCapHitProbability μ hQ hnp J β α χ hχ e k H u x =
    (VectorBrownian.law N).real {omega | ∃ t : ℝ≥0,t ≤ H ∧
      α / 2 ≤ |overlapValue D.axis (SmoothKilled.process D β x t omega)|} at hHit
  rw [← hHit] at hPhysical
  have hFire :
      (∫ omega,finiteDiscountedMass κ Y (θ : ℝ) (H+T) ((u,x),omega)
        ∂VectorBrownian.law N) =
      (∫ omega,finiteDiscountedMass (capKilling α D.axis)
        (SmoothKilled.process D β x) (θ : ℝ) (H+T) omega
        ∂VectorBrownian.law N) := by
    apply integral_congr_ae
    change (fun omega => finiteDiscountedMass
      (fun z : Vector N×Vector N => capKilling D.cutoffScale z.1 z.2)
      (sourceData_axisJointProcess D β) (θ : ℝ) (H+T) ((D.axis,x),omega))
      =ᵐ[VectorBrownian.law N]
      fun omega => finiteDiscountedMass (capKilling D.cutoffScale D.axis)
        (SmoothKilled.process D β x) (θ : ℝ) (H+T) omega
    exact sourceData_axisJoint_finiteDiscountedMass_ae_actual D β (θ : ℝ) (H+T) x
  rw [hFire]
  simpa only [D,SourceData.atSourceParameters] using hPhysical

end SlowEquilibration.ConditionedEntrance

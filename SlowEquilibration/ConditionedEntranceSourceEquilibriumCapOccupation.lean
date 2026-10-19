-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePhysicalHittingSource
public import SlowEquilibration.ConditionedEntranceSmoothKilledSemigroup

/-! One-time physical cap occupation under the actual stationary source
Gibbs law is controlled by its initial cap mass. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 500000

/-- The actual killed source process cannot increase the Gibbs mean of
the literal physical cap killing at any fixed time. -/
theorem sourceGibbs_capKilling_expectation_mean_le
    {N : ℕ} (D : SmoothKilled.SourceData N) (β : ℝ)
    {α : ℝ} (hα : 0 < α) (t : ℝ≥0) :
    (∫ x, SmoothKilled.expectation D β
        (PhysicalHitting.capKilling α D.axis) t
        (PhysicalHitting.capKilling α D.axis) x
      ∂gibbsLaw N β D.hamiltonian) ≤
      ∫ x, PhysicalHitting.capKilling α D.axis x
        ∂gibbsLaw N β D.hamiltonian := by
  let π := gibbsLaw N β D.hamiltonian
  let κ := PhysicalHitting.capKilling α D.axis
  have hκ : Continuous κ := (PhysicalHitting.capKilling_contDiff α D.axis).continuous
  have hκ0 : ∀ x, 0 ≤ κ x := PhysicalHitting.capKilling_nonneg α D.axis
  have hκ1 : ∀ x, κ x ≤ 1 := PhysicalHitting.capKilling_le_one hα D.axis
  let K := SmoothKilled.kernel D β κ hκ t
  let : IsProbabilityMeasure π :=
    gibbsLaw_probability D.dimension_ge_one β D.hamiltonian_contDiff.continuous
  let : IsFiniteKernel K := SmoothKilled.kernel_finite D β κ hκ hκ0 t
  have hsub : K ∘ₘ π ≤ π := SmoothKilled.kernel_gibbs_subinvariant D β κ hκ hκ0 t
  have hiκ : Integrable κ π := by
    apply Integrable.of_bound hκ.aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro x
    change ‖κ x‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (hκ0 x)]
    exact hκ1 x
  have hiκK : Integrable κ (K ∘ₘ π) := hiκ.mono_measure hsub
  have he (x : Vector N) : SmoothKilled.expectation D β κ t κ x =
      ∫ y, κ y ∂K x :=
    (SmoothKilled.kernel_integral_actual D β κ hκ t κ hκ.stronglyMeasurable x).symm
  change (∫ x, SmoothKilled.expectation D β κ t κ x ∂π) ≤ ∫ x, κ x ∂π
  calc
    (∫ x, SmoothKilled.expectation D β κ t κ x ∂π) =
        ∫ x, KilledL2.average K κ x ∂π := by
          apply integral_congr_ae
          exact .of_forall (fun x => by exact (he x).trans rfl)
    _ = ∫ y, κ y ∂(K ∘ₘ π) := KilledL2.integral_average π K hiκK
    _ ≤ ∫ y, κ y ∂π := integral_mono_measure hsub (.of_forall hκ0) hiκ

end SlowEquilibration.ConditionedEntrance

-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePhysicalHittingLaplace
public import SlowEquilibration.ConditionedEntranceSmoothKilledUniformStart
public import SlowEquilibration.SphericalCapCutoff

/-! Literal smooth two-sided source killing and the original source
Brownian representative of the finite physical firing mass. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance.PhysicalHitting
open MeasureTheory Set Filter
open SphericalModel SphericalAging HardSphereDynamics SphericalDynamics
open SphericalOverlapExponential SphericalSmoothTensorStationarity
open scoped NNReal ENNReal ContDiff InnerProductSpace
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

/-- A genuine smooth killing function, zero on the inner cap collar and
one on either outer cap. -/
def capKilling (α : ℝ) (u : Vector N) (x : Vector N) : ℝ :=
  SphericalCapCutoff.cutoff (α / 4) (α / 3) (overlapValue u x) +
    SphericalCapCutoff.cutoff (α / 4) (α / 3) (-overlapValue u x)

theorem capKilling_contDiff (α : ℝ) (u : Vector N) : ContDiff ℝ ∞ (capKilling α u) :=
  ((SphericalCapCutoff.cutoff_contDiff _ _).comp (overlapLinear u).contDiff).add
    ((SphericalCapCutoff.cutoff_contDiff _ _).comp (overlapLinear u).contDiff.neg)

theorem capKilling_nonneg (α : ℝ) (u x : Vector N) : 0 ≤ capKilling α u x :=
  add_nonneg (SphericalCapCutoff.cutoff_nonneg _ _ _) (SphericalCapCutoff.cutoff_nonneg _ _ _)

theorem capKilling_le_one {α : ℝ} (hα : 0 < α) (u x : Vector N) : capKilling α u x ≤ 1 := by
  have hq : α / 4 < α / 3 := by linarith
  unfold capKilling
  by_cases hr : overlapValue u x ≤ 0
  · rw [SphericalCapCutoff.cutoff_zero hq (by linarith : overlapValue u x ≤ α / 4),zero_add]
    exact SphericalCapCutoff.cutoff_le_one _ _ _
  · rw [SphericalCapCutoff.cutoff_zero hq (by linarith : -overlapValue u x ≤ α / 4),add_zero]
    exact SphericalCapCutoff.cutoff_le_one _ _ _

theorem capKilling_zero {α : ℝ} (hα : 0 < α) (u x : Vector N)
    (hx : |overlapValue u x| ≤ α / 4) : capKilling α u x = 0 := by
  have hq : α / 4 < α / 3 := by linarith
  have h := abs_le.mp hx
  simp only [capKilling,SphericalCapCutoff.cutoff_zero hq h.2,
    SphericalCapCutoff.cutoff_zero hq (by linarith : -overlapValue u x ≤ α / 4),add_zero]

theorem capKilling_one {α : ℝ} (hα : 0 < α) (u x : Vector N)
    (hx : α / 3 ≤ |overlapValue u x|) : capKilling α u x = 1 := by
  have hq : α / 4 < α / 3 := by linarith
  rcases le_abs.mp hx with hr | hr
  · simp only [capKilling,SphericalCapCutoff.cutoff_one hq hr,
      SphericalCapCutoff.cutoff_zero hq (by linarith : -overlapValue u x ≤ α / 4),add_zero]
  · simp only [capKilling,SphericalCapCutoff.cutoff_one hq hr,
      SphericalCapCutoff.cutoff_zero hq (by linarith : overlapValue u x ≤ α / 4),zero_add]

theorem source_process_eq_joint (D : SmoothKilled.SourceData N) (β : ℝ) (x : Vector N) :
    SmoothKilled.process D β x = jointPhysicalProcess β
      (smoothGradient D.hamiltonian D.hamiltonian_contDiff)
      (smoothGradient_contDiff D.hamiltonian D.hamiltonian_contDiff) x := rfl

/-- Actual original Brownian finite discounted firing mass equals the
finite source killed-semigroup Laplace integral, at each initial point. -/
theorem source_finiteDiscountedMass_expectation_eq (D : SmoothKilled.SourceData N)
    (β : ℝ) (κ : Vector N → ℝ) (hκ : Continuous κ)
    (hκ0 : ∀ y,0 ≤ κ y) (hκ1 : ∀ y,κ y ≤ 1) {θ : ℝ} (hθ : 0 ≤ θ) (L : ℝ≥0)
    (x : Vector N) :
    (∫ omega,finiteDiscountedMass κ (SmoothKilled.process D β x) θ L omega
      ∂VectorBrownian.law N) =
      ∫ t in (0 : ℝ)..(L : ℝ),Real.exp (-θ * t) * SmoothKilled.expectation D β κ t.toNNReal κ x :=
  finiteDiscountedMass_expectation_eq _ κ hκ.measurable hκ0 hκ1 _
    (SmoothKilled.process_measurable D β x) hθ L

/-- The concrete source process with its concrete smooth cap killing
satisfies the finite-grid physical hitting estimate. -/
theorem source_hitting_discounted_mass (D : SmoothKilled.SourceData N) {β C : ℝ}
    (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hgrad : ∀ y,OnSphere y → ‖gradient D.hamiltonian y‖ ≤ C * Real.sqrt (N : ℝ))
    (x : Vector N) (hx : OnSphere x) {α : ℝ} (hα : 0 < α)
    {θ : ℝ} (hθ : 0 ≤ θ) (H T : ℝ≥0) (hT : 0 < T)
    (hsmall : 4 * (1 + β * C) * (T : ℝ) ≤ α / 12) :
    exposureFactor θ H T *
      ((VectorBrownian.law N).real {omega | ∃ t : ℝ≥0,t ≤ H ∧
        α / 2 ≤ |overlapValue D.axis (SmoothKilled.process D β x t omega)|} -
          (gridSize H T : ℝ) * (2 * Real.exp (-(N : ℝ) * (α / 12)^2 / (16 * (T : ℝ))))) ≤
      ∫ t in (0 : ℝ)..((H + T : ℝ≥0) : ℝ),Real.exp (-θ * t) *
        SmoothKilled.expectation D β (capKilling α D.axis) t.toNNReal (capKilling α D.axis) x := by
  rw [← source_finiteDiscountedMass_expectation_eq D β _
    (capKilling_contDiff α D.axis).continuous (capKilling_nonneg α D.axis)
    (capKilling_le_one hα D.axis) hθ (H + T) x,source_process_eq_joint]
  simpa only [mul_assoc] using joint_physical_hitting_discounted_mass (by have := D.dimension_ge_one; omega)
    hβ hC _ (smoothGradient_contDiff D.hamiltonian D.hamiltonian_contDiff) hgrad D.axis x
    D.axis_onSphere hx hα _ (capKilling_contDiff α D.axis).continuous (capKilling_nonneg α D.axis)
    (capKilling_le_one hα D.axis) (fun y hy => (capKilling_one hα D.axis y hy).ge) hθ H T hT hsmall

end SlowEquilibration.ConditionedEntrance.PhysicalHitting

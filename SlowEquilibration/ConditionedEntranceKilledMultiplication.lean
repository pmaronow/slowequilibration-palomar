-- SPDX-License-Identifier: Apache-2.0
module
public import SphericalAging.BoundedItoMultiplier
public import SlowEquilibration.ConditionedEntranceKilledPerturbation

/-! The actual bounded killing multiplication on the reference Hilbert
space, including its genuine pointwise action, symmetry, and positivity. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.KilledOperator
open SphericalAging.BoundedItoMultiplier
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
  (κ : X → ℝ) (hκ : AEStronglyMeasurable κ μ) (K : ℝ≥0)
  (hK : ∀ᵐ x ∂μ, ‖κ x‖ ≤ K)

def multiplication : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := boundedMulCLM hκ K hK

theorem multiplication_ae (U : Lp ℝ 2 μ) :
    multiplication μ κ hκ K hK U =ᵐ[μ] fun x => κ x * U x :=
  boundedMulCLM_coe hκ K hK U

theorem multiplication_isSymmetric : (multiplication μ κ hκ K hK).IsSymmetric := by
  intro U V
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplication_ae μ κ hκ K hK U,multiplication_ae μ κ hκ K hK V] with x hU hV
  change inner ℝ (multiplication μ κ hκ K hK U x) (V x) =
    inner ℝ (U x) (multiplication μ κ hκ K hK V x)
  simp only [hU,hV,RCLike.inner_apply,conj_trivial]
  ring

theorem multiplication_nonnegative (hκ0 : ∀ᵐ x ∂μ, 0 ≤ κ x) (U : Lp ℝ 2 μ) :
    0 ≤ inner ℝ (multiplication μ κ hκ K hK U) U := by
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [multiplication_ae μ κ hκ K hK U,hκ0] with x hU h0
  change 0 ≤ inner ℝ (multiplication μ κ hκ K hK U x) (U x)
  simp only [hU,RCLike.inner_apply,conj_trivial]
  nlinarith [mul_nonneg h0 (sq_nonneg (U x))]

/-- Adding literal bounded killing preserves self-adjointness and the
original actual core, on the original operator domain. -/
theorem generator_with_killing_hasCore (A : Lp ℝ 2 μ →ₗ.[ℝ] Lp ℝ 2 μ)
    (hA : IsSelfAdjoint A) (C : Submodule ℝ (Lp ℝ 2 μ)) (hC : A.HasCore C) :
    (boundedPerturbation A (multiplication μ κ hκ K hK)).HasCore C :=
  boundedPerturbation_hasCore A hA _ (multiplication_isSymmetric μ κ hκ K hK) C hC

end SlowEquilibration.ConditionedEntrance.KilledOperator

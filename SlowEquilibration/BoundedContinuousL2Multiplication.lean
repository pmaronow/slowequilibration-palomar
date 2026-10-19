-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceKilledMultiplication
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! Literal L2 multiplication varies continuously in a bounded continuous
coefficient, including actual pointwise positivity and coercivity bounds. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped BoundedContinuousFunction NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.BoundedContinuousL2Multiplication
open ConditionedEntrance.KilledOperator
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

def operator (μ : Measure X) (f : X →ᵇ ℝ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  multiplication μ f f.continuous.aestronglyMeasurable ‖f‖₊ (.of_forall f.norm_coe_le_norm)

theorem operator_ae (μ : Measure X) (f : X →ᵇ ℝ) (U : Lp ℝ 2 μ) :
    operator μ f U=ᵐ[μ] fun x => f x*U x :=
  multiplication_ae _ _ _ _ _ _

theorem operator_difference_norm_le (μ : Measure X) (f g : X →ᵇ ℝ) :
    ‖operator μ f-operator μ g‖ ≤ ‖f-g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro U
  change ‖operator μ f U-operator μ g U‖ ≤ ‖f-g‖*‖U‖
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [operator_ae μ f U,operator_ae μ g U,
    Lp.coeFn_sub (operator μ f U) (operator μ g U)] with x hfx hgx hs
  rw [hs]
  simp only [Pi.sub_apply,hfx,hgx]
  rw [← sub_mul,norm_mul]
  have hb : ‖f x-g x‖ ≤ ‖f-g‖ := (f-g).norm_coe_le_norm x
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

theorem operator_lipschitz (μ : Measure X) : LipschitzWith 1 (operator μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using operator_difference_norm_le μ f g

/-- The positive pointwise coefficient gives a genuine lower Hilbert
quadratic bound, without a supplied operator coercivity conclusion. -/
theorem operator_inner_lower_bound (μ : Measure X) (f : X →ᵇ ℝ) (l : ℝ)
    (hl : ∀ᵐ x ∂μ,l ≤ f x) (U : Lp ℝ 2 μ) :
    l*‖U‖^2 ≤ inner ℝ (operator μ f U) U := by
  have hn : 0 ≤ inner ℝ (operator μ f U-l • U) U := by
    rw [L2.inner_def]
    apply integral_nonneg_of_ae
    filter_upwards [hl,operator_ae μ f U,Lp.coeFn_sub (operator μ f U) (l • U),Lp.coeFn_smul l U]
      with x hx hf hs hsm
    simp only [RCLike.inner_apply,conj_trivial,hs,Pi.sub_apply,hf,hsm,Pi.smul_apply,smul_eq_mul]
    have hp := mul_nonneg (sub_nonneg.mpr hx) (sq_nonneg (U x))
    change 0 ≤ U x*(f x*U x-l*U x)
    exact hp.trans_eq (by ring)
  rw [inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq] at hn
  linarith

end SlowEquilibration.BoundedContinuousL2Multiplication

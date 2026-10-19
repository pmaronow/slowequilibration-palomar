-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SemigroupLaplaceRate

/-! Original-time scalar pairings of the genuine positive-rate Hilbert
Laplace integral. -/
@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal InnerProductSpace
namespace SlowEquilibration.SemigroupLaplace.Data
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (S : SlowEquilibration.SemigroupLaplace.Data E)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem inner_rateOperator_left (θ : ℝ≥0) (hθ : 0 < θ) (x y : E) :
    inner ℝ (S.rateOperator θ x) y =
      ∫ t : ℝ in Ioi 0,Real.exp (-(θ : ℝ)*t)*inner ℝ (S.P t.toNNReal x) y := by
  let g : ℝ → ℝ := fun t => Real.exp (-(θ : ℝ)*t)*inner ℝ (S.P t.toNNReal x) y
  have hi := integral_comp_mul_right_Ioi' g 0 (inv_pos.mpr (show 0 < (θ : ℝ) from hθ))
  change (θ : ℝ)⁻¹ * (∫ t : ℝ in Ioi 0,g (t*(θ : ℝ)⁻¹)) =
    ∫ t : ℝ in Ioi (0*(θ : ℝ)⁻¹),g t at hi
  rw [zero_mul] at hi
  change inner ℝ ((θ : ℝ)⁻¹ • (S.timeRescale θ).operator x) y = _
  rw [real_inner_smul_left,(S.timeRescale θ).inner_operator_left,← hi]
  congr 1
  apply integral_congr_ae
  exact .of_forall (fun t => by
    change inner ℝ (Real.exp (-t) • S.P (t.toNNReal/θ) x) y = _
    rw [real_inner_smul_left]
    dsimp only [g]
    rw [show -(θ : ℝ)*(t*(θ : ℝ)⁻¹) = -t by field_simp]
    rw [← div_eq_mul_inv,Real.toNNReal_div' θ.coe_nonneg,Real.toNNReal_coe])

end SlowEquilibration.SemigroupLaplace.Data

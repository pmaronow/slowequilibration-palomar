-- SPDX-License-Identifier: Apache-2.0
module
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Continuous weighted-coordinate Hilbert forms, built from actual
adjoints and bounded coefficient multiplication operators. -/
@[expose] public section
noncomputable section
open scoped InnerProductSpace BigOperators
namespace SlowEquilibration.WeightedCoordinateOperator
set_option maxHeartbeats 300000
variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [Fintype ι]

def operator (G : ι → E →L[ℝ] F) (V : E →L[ℝ] F) (R S : F →L[ℝ] F) : E →L[ℝ] E :=
  (∑ i,(G i).adjoint.comp (R.comp (G i)))+V.adjoint.comp (S.comp V)

theorem operator_inner (G : ι → E →L[ℝ] F) (V : E →L[ℝ] F) (R S : F →L[ℝ] F)
    (u v : E) : inner ℝ (operator G V R S u) v=
      (∑ i,inner ℝ (R (G i u)) (G i v))+inner ℝ (S (V u)) (V v) := by
  simp only [operator,add_apply,sum_apply,ContinuousLinearMap.comp_apply,inner_add_left,sum_inner,
    ContinuousLinearMap.adjoint_inner_left]

theorem operator_continuous {Θ : Type*} [TopologicalSpace Θ]
    (G : ι → E →L[ℝ] F) (V : E →L[ℝ] F) (R S : Θ → F →L[ℝ] F)
    (hR : Continuous R) (hS : Continuous S) :
    Continuous (fun p => operator G V (R p) (S p)) := by
  unfold operator
  apply Continuous.add
  · apply continuous_finsetSum
    intro i _
    exact continuous_const.clm_comp (hR.clm_comp continuous_const)
  · exact continuous_const.clm_comp (hS.clm_comp continuous_const)

end SlowEquilibration.WeightedCoordinateOperator

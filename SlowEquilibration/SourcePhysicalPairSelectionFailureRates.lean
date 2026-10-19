-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairSelectionFailureProbability

/-! The actual posterior selection-error and determinant-weight error
vanish. All exponential rates are literal functions of the fixed source
parameters and the mesh cardinality chosen before dimension. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open Filter SphericalModel SphericalGaussianJet
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 500000

lemma source_dimension_exp_tail_tendsto (a:ℕ) {c:ℝ} (hc:0<c) :
    Tendsto (fun n:ℕ=>Real.exp (-((n+a:ℕ):ℝ)*c)) atTop (𝓝 0):=by
  have hN:Tendsto (fun n:ℕ=>((n+a:ℕ):ℝ)) atTop atTop:=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat a)
  have hh:=Real.tendsto_exp_atBot.comp (hN.const_mul_atTop_of_neg (r:=-c) (neg_neg_of_pos hc))
  convert hh using 1
  funext n
  congr 1
  ring

lemma sourceSelectionFailureRate_nonneg (μ:FiniteMixture) (Q G g:ℝ) (grid n:ℕ) :
    0 ≤ sourceSelectionFailureRate μ Q G g grid n:=by
  unfold sourceSelectionFailureRate
  positivity

theorem sourceSelectionFailureRate_tendsto (μ:FiniteMixture) {Q G g:ℝ}
    (hQ:0<Q) (hG:0<G) (hg:0<g) (grid:ℕ) :
    Tendsto (sourceSelectionFailureRate μ Q G g grid) atTop (𝓝 0):=by
  have hb:0<Q^2*μ.xi2 Q:=mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hcH:0<((g/2)/Real.sqrt (Q^2*μ.xi2 Q))^2/(16*Real.pi^2):=by positivity
  have hcB:0<(G/8)^2/(2*μ.xi Q):=by have hξ:=μ.xi_pos hQ;positivity
  have hR:=source_dimension_exp_tail_tendsto 2 (c:=1/2) (by norm_num)
  have hH:=source_dimension_exp_tail_tendsto 1 hcH
  have hB:=source_dimension_exp_tail_tendsto 2 hcB
  have H:=((hR.const_mul (2*(Fintype.card (Degree μ.maxDegree):ℝ))).add hH).add
    (hB.const_mul ((grid+1:ℕ):ℝ))
  simp only [mul_zero,add_zero] at H
  convert H using 1
  funext n
  unfold sourceSelectionFailureRate
  push_cast
  congr 2 <;> congr 1 <;> ring

def sourceSelectionWeightError (C:ℝ) (μ:FiniteMixture) (Q G g:ℝ) (grid n:ℕ):ℝ:=
  Real.sqrt C*Real.sqrt (sourceSelectionFailureRate μ Q G g grid n)

lemma sourceSelectionWeightError_nonneg (C:ℝ) (μ:FiniteMixture) (Q G g:ℝ) (grid n:ℕ) :
    0 ≤ sourceSelectionWeightError C μ Q G g grid n:=by
  unfold sourceSelectionWeightError
  positivity

theorem sourceSelectionWeightError_tendsto (C:ℝ) (μ:FiniteMixture) {Q G g:ℝ}
    (hQ:0<Q) (hG:0<G) (hg:0<g) (grid:ℕ) :
    Tendsto (sourceSelectionWeightError C μ Q G g grid) atTop (𝓝 0):=by
  have H:=((Real.continuous_sqrt.tendsto 0).comp
    (sourceSelectionFailureRate_tendsto μ hQ hG hg grid)).const_mul (Real.sqrt C)
  simp only [Function.comp_def,Real.sqrt_zero,mul_zero] at H
  convert H using 1
  funext n
  rfl

end
end SlowEquilibration.PairConditionalDeterminantMoments

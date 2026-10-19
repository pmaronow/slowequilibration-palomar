-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEClippedDeterminants

/-! Explicit inverse-dimension control of the genuine GOE edge-event square
root probability, derived from its actual exponential tail. -/
@[expose] public section
namespace SlowEquilibration.GOEEdgePolynomialRate
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open GOEAsymptotics GOEClippedDeterminants
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma sqrt_exp_eq (x : ℝ) : Real.sqrt (Real.exp x)=Real.exp (x/2) := by
  apply (Real.sqrt_eq_iff_eq_sq (Real.exp_nonneg x) (Real.exp_nonneg (x/2))).mpr
  rw [← Real.exp_nat_mul]
  congr 1
  norm_num
  ring

theorem gapBad_sqrt_inverse_dimension_eventually {g : ℝ} (hg : 0 < g) :
    ∀ᶠ n : ℕ in atTop,
      Real.sqrt ((stdGaussian (GOEAsymptotics.GaussianMatrix (n+1))).real (gapBad n g)) ≤
        (32*Real.pi^2/g^2)/(n+1:ℝ) := by
  filter_upwards [gapBad_exponential_eventually hg] with n hn
  have hN : 0 < (n+1:ℝ):=by positivity
  let c:=g^2/(32*Real.pi^2)
  have hc : 0 < c:=by dsimp [c];positivity [Real.pi_pos]
  have hExp : Real.sqrt (Real.exp (-(n+1:ℝ)*g^2/(16*Real.pi^2)))=
      Real.exp (-(c*(n+1:ℝ))) := by
    rw [sqrt_exp_eq]
    congr 1
    dsimp only [c]
    ring
  have hh:=Real.mul_exp_neg_le_exp_neg_one (c*(n+1:ℝ))
  have hOne : Real.exp (-1:ℝ)≤1:=by simpa using Real.exp_le_exp.mpr (by norm_num : (-1:ℝ)≤0)
  have hBound : Real.exp (-(c*(n+1:ℝ)))≤c⁻¹/(n+1:ℝ) := by
    apply (le_div_iff₀ hN).mpr
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hc).mpr
    nlinarith [hh.trans hOne]
  calc
    _ ≤ Real.sqrt (Real.exp (-(n+1:ℝ)*g^2/(16*Real.pi^2))) := Real.sqrt_le_sqrt hn
    _ = _ := hExp
    _ ≤ _ := hBound
    _ = _ := by dsimp only [c];field_simp

end
end SlowEquilibration.GOEEdgePolynomialRate

-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianQuadraticExponential

/-! A dimension-uniform normalized exponential bound for actual weighted
Gaussian square fluctuations, with either sign of every spectral weight. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
open Function MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def quadraticFluctuationScale (m : ℕ) (L : ℝ) : ℝ := 4*L*Real.sqrt (m:ℝ)

lemma quadraticFluctuationScale_pos {m : ℕ} {L : ℝ} (hm : 0 < m) (hL : 0 < L) :
    0 < quadraticFluctuationScale m L := by unfold quadraticFluctuationScale;positivity

/-- The actual quadratic fluctuations have bounded normalized positive
and negative exponential moments; no Gaussian concentration conclusion is assumed. -/
theorem diagonalQuadratic_normalized_exp (w : ι → ℝ) {L : ℝ} (hL : 0 < L)
    (hm : 0 < Fintype.card ι) (hw : ∀ i,|w i| ≤ L) :
    let a:=quadraticFluctuationScale (Fintype.card ι) L
    Integrable (fun x=>Real.exp (diagonalQuadratic w x/a)) (γpi ι) ∧
    Integrable (fun x=>Real.exp (-diagonalQuadratic w x/a)) (γpi ι) ∧
    (∫ x,Real.exp (diagonalQuadratic w x/a) ∂γpi ι) ≤ Real.exp (1/4:ℝ) ∧
    (∫ x,Real.exp (-diagonalQuadratic w x/a) ∂γpi ι) ≤ Real.exp (1/4:ℝ) := by
  dsimp only
  let m:=Fintype.card ι
  let a:=quadraticFluctuationScale m L
  have hmp : 0 < (m:ℝ):=Nat.cast_pos.mpr hm
  have hap : 0 < a:=quadraticFluctuationScale_pos hm hL
  have hRoot : 1 ≤ Real.sqrt (m:ℝ) := by
    exact (Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)).mpr (by norm_cast)
  have hSmall (i:ι) : |a⁻¹*w i| ≤ 1/4 := by
    rw [abs_mul,abs_of_pos (inv_pos.mpr hap)]
    calc
      _ ≤ a⁻¹*L:=mul_le_mul_of_nonneg_left (hw i) (inv_nonneg.mpr hap.le)
      _ ≤ (1/4:ℝ) := by
        rw [show a⁻¹*L=L/a by ring]
        apply (div_le_iff₀ hap).mpr
        dsimp only [a,quadraticFluctuationScale]
        nlinarith [mul_le_mul_of_nonneg_left hRoot hL.le]
  have hSmallNeg (i:ι) : |(-a⁻¹)*w i| ≤ 1/4 := by simpa only [neg_mul,abs_neg] using hSmall i
  have hSum : (∑ i,w i^2) ≤ (m:ℝ)*L^2 := by
    calc
      _ ≤ ∑ _i:ι,L^2 := Finset.sum_le_sum (fun i hi=>by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hw i) 2)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,m]
  have hBudget : 4*a⁻¹^2*(∑ i,w i^2) ≤ (1/4:ℝ) := by
    calc
      _ ≤ 4*a⁻¹^2*((m:ℝ)*L^2):=mul_le_mul_of_nonneg_left hSum (by positivity)
      _=(1/4:ℝ) := by
        dsimp only [a,quadraticFluctuationScale]
        rw [inv_pow,mul_pow,mul_pow,Real.sq_sqrt hmp.le]
        field_simp
  have hPos:=diagonalQuadratic_exp_integral_le w a⁻¹ hSmall
  have hNeg:=diagonalQuadratic_exp_integral_le w (-a⁻¹) hSmallNeg
  have hePos (x) : a⁻¹*diagonalQuadratic w x=diagonalQuadratic w x/a:=by ring
  have heNeg (x) : -a⁻¹*diagonalQuadratic w x=-diagonalQuadratic w x/a:=by ring
  simp only [hePos] at hPos
  simp only [heNeg,neg_sq] at hNeg
  exact ⟨hPos.1,hNeg.1,hPos.2.trans (Real.exp_le_exp.mpr hBudget),hNeg.2.trans (Real.exp_le_exp.mpr hBudget)⟩

end
end SlowEquilibration.GaussianQuadraticVariance

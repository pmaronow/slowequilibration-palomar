-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConditionedEntranceRegressionOrders

/-! True lowest-degree energy control for the literal source regression
polynomials under the two actual cutoff support bounds. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 300000

theorem regression_scalar_small_overlap (μ : FiniteMixture) (Q n M R α r g X Y : ℝ)
    (hn : 0 ≤ n) (hM : 0 ≤ M) (hR : 0 ≤ R) (hα : 0 ≤ α)
    (hr : |r| ≤ 1) (hrα : |r| ≤ R*α) (hg : |g| ≤ n*(R*α))
    (hX : |X| ≤ M*n) (hY : |Y| ≤ M*n) :
    |valueTheta μ Q r*X+radialTheta μ Q r*Y-tangentTheta μ Q r*g| ≤
      regressionOrderConstant μ Q*(M+1)*n*(R*α)^μ.minDegree := by
  let C := regressionOrderConstant μ Q
  have hC : 0 ≤ C := (regressionOrderConstant_pos μ Q).le
  have hRa : 0 ≤ R*α := mul_nonneg hR hα
  have hp := mixed_regression_orders μ Q hr
  have ht : |tangentTheta μ Q r| ≤ C*|r|^(μ.minDegree-1) := by
    have hv := hp.2.1
    change _ ≤ C*|r|^(μ.minDegree-1) at hv
    linarith [abs_nonneg (valueThetaDerivative μ Q r),abs_nonneg (radialThetaDerivative μ Q r)]
  have hv : |valueTheta μ Q r|+|radialTheta μ Q r| ≤ C*(R*α)^μ.minDegree :=
    hp.1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg r) hrα _) hC)
  have ht' : |tangentTheta μ Q r| ≤ C*(R*α)^(μ.minDegree-1) :=
    ht.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg r) hrα _) hC)
  have he : (R*α)^(μ.minDegree-1)*(R*α)=(R*α)^μ.minDegree := by
    rw [←pow_succ,Nat.sub_add_cancel (μ.minDegree_ge_two.trans' (by norm_num))]
  calc
    _ ≤ |valueTheta μ Q r*X+radialTheta μ Q r*Y| + |tangentTheta μ Q r*g| := by
      simpa only [sub_zero,zero_sub,abs_neg] using
        abs_sub_le (valueTheta μ Q r*X+radialTheta μ Q r*Y) 0 (tangentTheta μ Q r*g)
    _ ≤ (|valueTheta μ Q r*X|+|radialTheta μ Q r*Y|)+|tangentTheta μ Q r*g| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ = |valueTheta μ Q r| * |X|+|radialTheta μ Q r| * |Y|+|tangentTheta μ Q r| * |g| := by
      rw [abs_mul,abs_mul,abs_mul]
    _ ≤ (|valueTheta μ Q r|+|radialTheta μ Q r|)*(M*n)+
        |tangentTheta μ Q r| * |g| := by
      rw [add_mul]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hX (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hY (abs_nonneg _))) le_rfl
    _ ≤ (C*(R*α)^μ.minDegree)*(M*n)+(C*(R*α)^(μ.minDegree-1))*(n*(R*α)) :=
      add_le_add (mul_le_mul_of_nonneg_right hv (mul_nonneg hM hn))
        (mul_le_mul ht' hg (abs_nonneg _) (mul_nonneg hC (pow_nonneg hRa _)))
    _ = _ := by
      calc
        _=C*(M*n)*(R*α)^μ.minDegree+C*n*((R*α)^(μ.minDegree-1)*(R*α)) := by ring
        _=_ := by rw [he];ring

theorem cutoff_support_argument_bound (χ : ℝ → ℝ) {R t : ℝ}
    (hχ : ∀ s, R < |s| → χ s=0) (h : χ t ≠ 0) : |t| ≤ R := by
  exact le_of_not_gt (fun ht => h (hχ t ht))

def cutoffEnergyConstant (μ : FiniteMixture) (Q M B R : ℝ) : ℝ :=
  B^2*regressionOrderConstant μ Q*(M+1)*R^μ.minDegree

theorem cutoffEnergyConstant_nonneg (μ : FiniteMixture) (Q M B R : ℝ)
    (hM : 0 ≤ M) (hR : 0 ≤ R) : 0 ≤ cutoffEnergyConstant μ Q M B R := by
  unfold cutoffEnergyConstant
  have hC := (regressionOrderConstant_pos μ Q).le
  positivity

theorem cutoff_regression_energy_bound (μ : FiniteMixture) (Q n M R α r g X Y : ℝ)
    (hn : 0 < n) (hM : 0 ≤ M) (hR : 0 ≤ R) (hα : 0 < α)
    (hr : |r| ≤ 1) (hX : |X| ≤ M*n) (hY : |Y| ≤ M*n)
    (χ : ℝ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hχB : ∀ s,|χ s| ≤ B) (hχR : ∀ s,R < |s| → χ s=0) :
    |χ (r/α)*χ (g/(n*α))*(valueTheta μ Q r*X+radialTheta μ Q r*Y-
      tangentTheta μ Q r*g)| ≤ cutoffEnergyConstant μ Q M B R*n*α^μ.minDegree := by
  have hC := cutoffEnergyConstant_nonneg μ Q M B R hM hR
  by_cases h1 : χ (r/α)=0
  · rw [h1,zero_mul,zero_mul,abs_zero]
    exact mul_nonneg (mul_nonneg hC hn.le) (pow_nonneg hα.le _)
  by_cases h2 : χ (g/(n*α))=0
  · rw [h2,mul_zero,zero_mul,abs_zero]
    exact mul_nonneg (mul_nonneg hC hn.le) (pow_nonneg hα.le _)
  have hrα : |r| ≤ R*α := by
    have H := cutoff_support_argument_bound χ hχR h1
    rw [abs_div,abs_of_pos hα] at H
    exact (div_le_iff₀ hα).mp H
  have hgα : |g| ≤ n*(R*α) := by
    have H := cutoff_support_argument_bound χ hχR h2
    rw [abs_div,abs_of_pos (mul_pos hn hα)] at H
    have H' := (div_le_iff₀ (mul_pos hn hα)).mp H
    nlinarith [H']
  have hreg := regression_scalar_small_overlap μ Q n M R α r g X Y
    hn.le hM hR hα.le hr hrα hgα hX hY
  rw [abs_mul,abs_mul]
  calc
    _ ≤ (B*B)*(regressionOrderConstant μ Q*(M+1)*n*(R*α)^μ.minDegree) :=
      mul_le_mul (mul_le_mul (hχB _) (hχB _) (abs_nonneg _) hB) hreg
        (abs_nonneg _) (mul_nonneg hB hB)
    _ = _ := by unfold cutoffEnergyConstant;rw [mul_pow];ring

end SlowEquilibration.ConditionedEntrance

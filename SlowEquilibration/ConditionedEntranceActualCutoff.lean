-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalCapCutoff

/-! The actual smooth scalar entrance cutoff, equal to one on [-1,1]
and zero outside [-2,2], with values in [0,1]. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open SphericalCapCutoff
open scoped ContDiff
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

def sourceScalarCutoff (s : ℝ) : ℝ := (1-cutoff 1 2 s)*(1-cutoff 1 2 (-s))

theorem sourceScalarCutoff_contDiff : ContDiff ℝ ∞ sourceScalarCutoff :=
  (contDiff_const.sub (cutoff_contDiff 1 2)).mul
    (contDiff_const.sub ((cutoff_contDiff 1 2).comp contDiff_id.neg))

theorem sourceScalarCutoff_contDiff_two : ContDiff ℝ 2 sourceScalarCutoff :=
  sourceScalarCutoff_contDiff.of_le (by simp)

theorem sourceScalarCutoff_nonneg (s : ℝ) : 0 ≤ sourceScalarCutoff s :=
  mul_nonneg (sub_nonneg.mpr (cutoff_le_one 1 2 s))
    (sub_nonneg.mpr (cutoff_le_one 1 2 (-s)))

theorem sourceScalarCutoff_le_one (s : ℝ) : sourceScalarCutoff s ≤ 1 := by
  have h₁ : 1-cutoff 1 2 s ≤ 1 := by linarith [cutoff_nonneg 1 2 s]
  have h₂ : 1-cutoff 1 2 (-s) ≤ 1 := by linarith [cutoff_nonneg 1 2 (-s)]
  exact (mul_le_mul h₁ h₂ (sub_nonneg.mpr (cutoff_le_one 1 2 (-s))) zero_le_one).trans_eq (one_mul 1)

theorem sourceScalarCutoff_abs_le_one (s : ℝ) : |sourceScalarCutoff s| ≤ 1 := by
  rw [abs_of_nonneg (sourceScalarCutoff_nonneg s)]
  exact sourceScalarCutoff_le_one s

theorem sourceScalarCutoff_eq_one {s : ℝ} (hs : |s| ≤ 1) : sourceScalarCutoff s=1 := by
  have hp := (abs_le.mp hs).2
  have hm : -s ≤ 1 := by linarith [(abs_le.mp hs).1]
  simp only [sourceScalarCutoff,cutoff_zero (by norm_num : (1 : ℝ)<2) hp,
    cutoff_zero (by norm_num : (1 : ℝ)<2) hm,sub_zero,one_mul]

theorem sourceScalarCutoff_eq_zero {s : ℝ} (hs : 2 ≤ |s|) : sourceScalarCutoff s=0 := by
  by_cases h0 : 0 ≤ s
  · have hp : 2 ≤ s := by simpa only [abs_of_nonneg h0] using hs
    simp only [sourceScalarCutoff,cutoff_one (by norm_num : (1 : ℝ)<2) hp,sub_self,zero_mul]
  · have hm : 2 ≤ -s := by simpa only [abs_of_neg (lt_of_not_ge h0)] using hs
    simp only [sourceScalarCutoff,cutoff_one (by norm_num : (1 : ℝ)<2) hm,sub_self,mul_zero]

theorem sourceScalarCutoff_zero_of_two_lt_abs {s : ℝ} (hs : 2 < |s|) : sourceScalarCutoff s=0 :=
  sourceScalarCutoff_eq_zero hs.le

end SlowEquilibration.ConditionedEntrance

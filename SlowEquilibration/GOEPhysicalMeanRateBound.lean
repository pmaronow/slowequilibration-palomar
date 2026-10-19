-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEDimensionComparison
public import SlowEquilibration.GOEPhysicalNormalizedMoments

/-! Uniform bounded logarithmic errors for the genuine ordinary GOE mean. -/
@[expose] public section
namespace SlowEquilibration.GOEPhysicalPotential
open Set
open GOEPhysicalPrefactors GOEDimensionComparison GOEPhysicalNormalizedMoments GOEScaling
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma physicalRate_full_ambient (n : ℕ) (b k : ℝ) :
    physicalRate (n+1) 0 b k = (n+2 : ℕ) *
      (Real.log (Real.sqrt b) + SemicirclePotential.potential (k / Real.sqrt b)) := by
  unfold physicalRate scaleFactor
  simp only [Nat.cast_add, Nat.cast_one, add_zero]
  rw [mul_div_cancel_right₀ b (by positivity : (n:ℝ)+1+1 ≠ 0)]
  ring

/-- Uniform bounded error against the limiting semicircle exponent for the
actual ordinary determinant mean in dimension N−1 with variance b/N. -/
theorem physicalMean_log_error_bound {b g Z : ℝ} (hb : 0 < b) (hg : 0 < g) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ∀ k ∈ Icc (2 * Real.sqrt b + g) Z,
      |Real.log (physicalMean n (n+2) b k) - (n+2 : ℕ) *
        (Real.log (Real.sqrt b) + SemicirclePotential.potential (k / Real.sqrt b))| ≤ B := by
  obtain ⟨C,hC,hpref⟩ := physical_first_prefactors 1 (Z := Z) hb hg
  obtain ⟨B,hB,hchange⟩ := physicalRate_fixed_codimension_bound 1 (Z := Z) hb hg
  refine ⟨B + |Real.log C|, add_nonneg hB (abs_nonneg _), ?_⟩
  intro n k hk
  have hp := hpref n k hk.1 hk.2
  have hm := physicalMean_pos n 1 (k := k) hb (by linarith [hk.1])
  have hl := Real.log_le_log (Real.exp_pos _) hp.1
  have hu := Real.log_le_log hm hp.2
  rw [Real.log_exp] at hl
  rw [Real.log_mul hC.ne' (Real.exp_ne_zero _), Real.log_exp] at hu
  have hd := hchange n (n+1) 1 0 (by omega) (by omega) (by omega) k hk
  rw [Real.norm_eq_abs, physicalRate_full_ambient, abs_le] at hd
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log C), abs_nonneg (Real.log C)]

end
end SlowEquilibration.GOEPhysicalPotential

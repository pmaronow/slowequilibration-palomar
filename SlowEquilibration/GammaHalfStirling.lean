-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GammaLogAsymptotics

/-! Bounded Stirling remainders at the integer and half-integer arguments
which occur in the actual sphere area. -/
@[expose] public section
namespace SlowEquilibration.SphereAreaAsymptotics
open Set
noncomputable section

lemma log_stirlingSeq_abs_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, m ≠ 0 → |Real.log (Stirling.stirlingSeq m)| ≤ C := by
  refine ⟨|Real.log (Stirling.stirlingSeq 1)| + 1, by positivity, ?_⟩
  intro m hm
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  have hu := Stirling.log_stirlingSeq'_antitone (show 0 ≤ j by omega)
  have hl := Stirling.log_stirlingSeq_bounded_aux j
  simp only [Function.comp_def] at hu
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log (Stirling.stirlingSeq 1)),
    neg_le_abs (Real.log (Stirling.stirlingSeq 1))]

/-- The half-integer Stirling remainder is an exact ratio of the two
factorial Stirling sequences, plus a uniformly bounded logarithmic term. -/
lemma gamma_half_log_remainder (m : ℕ) (hm : m ≠ 0) :
    Real.log (Real.Gamma ((m : ℝ) + 1 / 2 + 1)) -
        ((m : ℝ) + 1) * Real.log ((m : ℝ) + 1 / 2) + ((m : ℝ) + 1 / 2) =
      Real.log (Stirling.stirlingSeq (2*m)) - Real.log (Stirling.stirlingSeq m) -
        (m : ℝ) * Real.log (((m : ℝ) + 1 / 2) / m) +
        Real.log 2 / 2 + Real.log Real.pi / 2 + 1 / 2 := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have ht : 0 < (m : ℝ) + 1 / 2 := by positivity
  have hd := Real.Gamma_mul_Gamma_add_half_of_pos ht
  rw [show (m : ℝ) + 1 / 2 + 1 / 2 = (m : ℝ)+1 by ring,
    show 2*((m : ℝ)+1/2) = ((2*m : ℕ):ℝ)+1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial] at hd
  have hdlog := congrArg Real.log hd
  rw [Real.log_mul (Real.Gamma_pos_of_pos ht).ne' (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by norm_num : (0:ℝ)<2), Real.log_sqrt Real.pi_pos.le] at hdlog
  rw [Real.Gamma_add_one ht.ne', Real.log_mul ht.ne' (Real.Gamma_pos_of_pos ht).ne',
    Real.log_div ht.ne' hm0.ne']
  have h1 := factorial_log_remainder m hm
  have h2 := factorial_log_remainder (2*m) (by omega)
  push_cast at h2 hdlog
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hm0.ne'] at h2
  linarith

lemma half_log_ratio_bound (m : ℕ) (hm : m ≠ 0) :
    0 ≤ (m : ℝ) * Real.log (((m : ℝ) + 1 / 2) / m) ∧
      (m : ℝ) * Real.log (((m : ℝ) + 1 / 2) / m) ≤ 1 / 2 := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  constructor
  · exact mul_nonneg hm0.le (Real.log_nonneg ((le_div_iff₀ hm0).mpr (by linarith)))
  · have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos
        (div_pos (by positivity : 0 < (m:ℝ)+1/2) hm0)) hm0.le
    convert h using 1
    field_simp
    ring

/-- Uniform bounded remainder for the exact Gamma factor in sphere areas.
The proof uses factorial Stirling and Legendre duplication, including both parities. -/
theorem gamma_half_integer_log_remainder_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 2 ≤ N →
      |Real.log (Real.Gamma ((N : ℝ)/2+1)) -
        ((N : ℝ)/2+1/2)*Real.log ((N : ℝ)/2) + (N : ℝ)/2| ≤ B := by
  obtain ⟨C,hC,hbound⟩ := log_stirlingSeq_abs_bound
  refine ⟨2*C + |Real.log 2| + |Real.log Real.pi| + 1, by positivity, ?_⟩
  intro N hN
  obtain ⟨m, hN | hN⟩ := Nat.even_or_odd' N
  · subst N
    have hm : m ≠ 0 := by omega
    have h := factorial_log_remainder m hm
    have hb := hbound m hm
    push_cast
    simp only [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0), Real.Gamma_nat_eq_factorial]
    rw [abs_le] at hb ⊢
    constructor <;> linarith [le_abs_self (Real.log 2), neg_le_abs (Real.log 2),
      abs_nonneg (Real.log Real.pi)]
  · subst N
    have hm : m ≠ 0 := by omega
    have h := gamma_half_log_remainder m hm
    have hb1 := hbound m hm
    have hb2 := hbound (2*m) (by omega)
    have ht := half_log_ratio_bound m hm
    push_cast
    rw [show ((2:ℝ)*m+1)/2 = (m:ℝ)+1/2 by ring]
    rw [show (m:ℝ)+1/2+1/2 = (m:ℝ)+1 by ring, h]
    rw [abs_le] at hb1 hb2 ⊢
    constructor <;> linarith [le_abs_self (Real.log 2), neg_le_abs (Real.log 2),
      le_abs_self (Real.log Real.pi), neg_le_abs (Real.log Real.pi)]

end
end SlowEquilibration.SphereAreaAsymptotics

-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-! First-order logarithmic Stirling asymptotics for the real Gamma function. -/
@[expose] public section
namespace SlowEquilibration.SphereAreaAsymptotics
open Filter Set
open scoped Topology
noncomputable section

lemma log_div_self_tendsto :
    Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
  simpa only [pow_one, one_mul, add_zero] using
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero

lemma factorial_log_remainder (n : ℕ) (hn : n ≠ 0) :
    Real.log (n.factorial : ℝ) - (n:ℝ)*Real.log n + n =
      Real.log (Stirling.stirlingSeq n) + Real.log 2 / 2 + Real.log n / 2 := by
  have hp : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [Stirling.stirlingSeq, Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_sqrt (by positivity),
    Real.log_mul (by norm_num) hp.ne', Real.log_pow,
    Real.log_div hp.ne' (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem factorial_log_remainder_tendsto :
    Tendsto (fun n : ℕ =>
      (Real.log (n.factorial : ℝ) - (n:ℝ)*Real.log n + n) / n) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi := tendsto_inv_atTop_zero.comp hn
  have hs := Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity : Real.sqrt Real.pi ≠ 0)
  have hl := log_div_self_tendsto.comp hn
  have h := ((hs.mul hi).add ((tendsto_const_nhds (x := Real.log 2 / 2)).mul hi)).add (hl.div_const 2)
  simp only [mul_zero, add_zero, zero_div] at h
  apply h.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  rw [factorial_log_remainder n hn]
  dsimp only [Function.comp_def]
  ring

lemma floor_log_error_tendsto :
    Tendsto (fun x : ℝ => (1 - (⌊x⌋₊ : ℝ)/x) * Real.log x) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    exact mul_nonneg (sub_nonneg.mpr ((div_le_one hx0).mpr (Nat.floor_le hx0.le)))
      (Real.log_nonneg hx)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hm : x - (⌊x⌋₊ : ℝ) ≤ 1 := by linarith [Nat.lt_floor_add_one x]
    calc
      (1 - (⌊x⌋₊ : ℝ)/x) * Real.log x =
          (x - (⌊x⌋₊ : ℝ))/x * Real.log x := by field_simp
      _ ≤ 1/x * Real.log x := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hm hx0.le) (Real.log_nonneg hx)
      _ = Real.log x/x := by ring
  · exact log_div_self_tendsto

theorem floor_factorial_log_rate :
    Tendsto (fun x : ℝ => Real.log ((⌊x⌋₊).factorial : ℝ)/x - Real.log x)
      atTop (𝓝 (-1)) := by
  have hf : Tendsto (fun x : ℝ => ⌊x⌋₊) atTop atTop := tendsto_nat_floor_atTop
  have hr : Tendsto (fun x : ℝ => (⌊x⌋₊ : ℝ)/x) atTop (𝓝 1) := tendsto_nat_floor_div_atTop
  have hS := (factorial_log_remainder_tendsto.comp hf).mul hr
  have hlog := hr.log one_ne_zero
  have h := (((hS.add (hr.mul hlog)).sub floor_log_error_tendsto).sub hr)
  simp only [zero_mul, Real.log_one, mul_zero, add_zero, sub_zero, zero_sub] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hm : (0 : ℝ) < ⌊x⌋₊ := by
    exact_mod_cast (show 0 < ⌊x⌋₊ by exact Nat.floor_pos.mpr (by linarith))
  dsimp only [Function.comp_def]
  rw [Real.log_div hm.ne' hx0.ne']
  field_simp
  ring

lemma log_add_one_div_tendsto :
    Tendsto (fun x : ℝ => Real.log (x+1)/x) atTop (𝓝 0) := by
  have ha : Tendsto (fun x : ℝ => x+1) atTop atTop :=
    tendsto_id.atTop_add (tendsto_const_nhds (x := (1:ℝ)))
  have hr : Tendsto (fun x : ℝ => 1+x⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have h := (log_div_self_tendsto.comp ha).mul hr
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hx1 : x+1 ≠ 0 := by linarith
  dsimp only [Function.comp_def]
  field_simp

/-- The real Gamma function has the genuine first-order Stirling rate.
The proof squeezes it between adjacent factorials using proven monotonicity. -/
theorem gamma_log_rate :
    Tendsto (fun x : ℝ => Real.log (Real.Gamma (x+1))/x - Real.log x)
      atTop (𝓝 (-1)) := by
  have hu := floor_factorial_log_rate.add log_add_one_div_tendsto
  simp only [add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' floor_factorial_log_rate hu
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hm : (1 : ℝ) ≤ ⌊x⌋₊ := by
      exact_mod_cast (show 1 ≤ ⌊x⌋₊ by exact Nat.floor_pos.mpr (by linarith))
    have hΓ := Real.Gamma_strictMonoOn_Ici.monotoneOn
      (show (⌊x⌋₊ : ℝ)+1 ∈ Ici 2 by change 2 ≤ _; linarith)
      (show x+1 ∈ Ici 2 by change 2 ≤ _; linarith)
      (show (⌊x⌋₊ : ℝ)+1 ≤ x+1 by linarith [Nat.floor_le hx0.le])
    rw [Real.Gamma_nat_eq_factorial] at hΓ
    exact sub_le_sub_right (div_le_div_of_nonneg_right
      (Real.log_le_log (by positivity) hΓ) hx0.le) _
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hm : (1 : ℝ) ≤ ⌊x⌋₊ := by
      exact_mod_cast (show 1 ≤ ⌊x⌋₊ by exact Nat.floor_pos.mpr (by linarith))
    have hΓ := Real.Gamma_strictMonoOn_Ici.monotoneOn
      (show x+1 ∈ Ici 2 by change 2 ≤ _; linarith)
      (show (⌊x⌋₊ : ℝ)+1+1 ∈ Ici 2 by change 2 ≤ _; linarith)
      (show x+1 ≤ (⌊x⌋₊ : ℝ)+1+1 by linarith [Nat.lt_floor_add_one x])
    rw [show (⌊x⌋₊ : ℝ)+1+1 = ((⌊x⌋₊+1 : ℕ):ℝ)+1 by push_cast; rfl,
      Real.Gamma_nat_eq_factorial, Nat.factorial_succ, Nat.cast_mul] at hΓ
    have hlog : Real.log (Real.Gamma (x+1)) ≤
        Real.log ((⌊x⌋₊).factorial : ℝ) + Real.log (x+1) := by
      have hΓlog := Real.log_le_log (Real.Gamma_pos_of_pos (by linarith : 0 < x+1)) hΓ
      rw [Real.log_mul (by positivity) (by positivity)] at hΓlog
      have hl : Real.log ((⌊x⌋₊+1 : ℕ):ℝ) ≤ Real.log (x+1) :=
        Real.log_le_log (by positivity) (by push_cast; linarith [Nat.floor_le hx0.le])
      linarith
    have hd := div_le_div_of_nonneg_right hlog hx0.le
    rw [add_div] at hd
    linarith

end
end SlowEquilibration.SphereAreaAsymptotics

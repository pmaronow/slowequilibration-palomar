-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureScalarStatic
public import SlowEquilibration.LogEnclosure

@[expose] public section

namespace SlowEquilibration.PureScalarStatic

noncomputable section
open Set
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

def pureLogMargin (m : ℝ) : ℝ :=
  Real.log (2*m+1)-2*m*(3*m+2)/((m+2)*(2*m+1))

theorem pureLogMargin_hasDerivAt {m : ℝ} (hm : 1 < m) :
    HasDerivAt pureLogMargin
      (4*m^2*(m-1)/((m+2)^2*(2*m+1)^2)) m := by
  have hlin := ((hasDerivAt_id m).const_mul 2).add_const 1
  have hnum := ((hasDerivAt_id m).const_mul 2).mul
    (((hasDerivAt_id m).const_mul 3).add_const 2)
  have hden := ((hasDerivAt_id m).add_const 2).mul hlin
  have hn₁ : 2*m+1 ≠ 0 := by linarith
  have hn₂ : m+2 ≠ 0 := by linarith
  convert (hlin.log hn₁).sub (hnum.div hden (mul_ne_zero hn₂ hn₁)) using 1
  · ext x
    rfl
  · dsimp
    field_simp [hn₁, hn₂]
    ring

/-- Exact finite logarithm series gives the strict base inequality; no
decimal or numerical approximation is used. -/
theorem log_five_gt_eight_fifths : (8/5 : ℝ) < Real.log 5 := by
  have h := Real.sum_range_le_log_div (x := (2/3 : ℝ))
    (by norm_num) (by norm_num) 4
  have harg : (1+(2/3 : ℝ))/(1-(2/3 : ℝ)) = 5 := by norm_num
  rw [harg] at h
  have hrat : (8/5 : ℝ) <
      2*(∑ i ∈ Finset.range 4, (2/3 : ℝ)^(2*i+1)/(2*i+1)) := by
    norm_num [Finset.sum_range_succ]
  linarith

theorem pureLogMargin_pos {m : ℝ} (hm : 2 ≤ m) : 0 < pureLogMargin m := by
  have hmono : MonotoneOn pureLogMargin (Ici (2 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 2)
    · intro x hx
      have hx2 : 2 ≤ x := hx
      exact (pureLogMargin_hasDerivAt (by linarith : 1 < x)).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : 2 < x := by simpa only [interior_Ici, mem_Ioi] using hx
      exact (pureLogMargin_hasDerivAt (by linarith : 1 < x)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : 2 < x := by simpa only [interior_Ici, mem_Ioi] using hx
      rw [(pureLogMargin_hasDerivAt (by linarith : 1 < x)).deriv]
      have hx0 : 0 < x := by linarith
      have hx1 : 0 ≤ x-1 := by linarith
      positivity
  have hbase : 0 < pureLogMargin 2 := by
    norm_num [pureLogMargin]
    exact log_five_gt_eight_fifths
  exact hbase.trans_le (hmono (by norm_num) hm hm)

/-- The actual integral at twice the shifted degree lies strictly above
the pure-root target. -/
theorem upsilon_twice_shifted_gt {m : ℝ} (hm : 2 ≤ m) :
    1/(m+2) < upsilon (2*m) := by
  have hm0 : 0 < m := by linarith
  have hmargin := pureLogMargin_pos hm
  unfold pureLogMargin at hmargin
  have hden : 0 < (m+2)*(2*m+1) := by positivity
  have hlog : 2*m*(3*m+2) < Real.log (2*m+1)*((m+2)*(2*m+1)) :=
    (div_lt_iff₀ hden).mp (by linarith [hmargin])
  rw [upsilon_eq (by positivity : 0 < 2*m)]
  apply (div_lt_div_iff₀ (by positivity : 0 < m+2) (by positivity : 0 < (2*m)^2)).mpr
  have hlogarg : 1+2*m = 2*m+1 := by ring
  rw [hlogarg]
  nlinarith

/-- The manuscript's quantitative pure-root location bound, obtained from
the genuine integral root and exact logarithmic comparison. -/
theorem zParameter_gt_twice_shifted (p : ℕ) (hp : 4 ≤ p) :
    2*((p : ℝ)-2) < zParameter p (by omega) := by
  have hpR : (4 : ℝ) ≤ p := by exact_mod_cast hp
  have hm : 2 ≤ (p : ℝ)-2 := by linarith
  have ht := upsilon_twice_shifted_gt hm
  have hs := zParameter_spec p (by omega)
  have htarget : (p : ℝ)-2+2 = p := by ring
  rw [htarget] at ht
  by_contra hn
  have hle : zParameter p (by omega) ≤ 2*((p : ℝ)-2) := le_of_not_gt hn
  have hu := strictAntiOn_upsilon.antitoneOn hs.1.le (by linarith : 0 ≤ 2*((p : ℝ)-2)) hle
  rw [hs.2] at hu
  exact (not_lt_of_ge hu) ht

end

end SlowEquilibration.PureScalarStatic

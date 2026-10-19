-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiLabeledCovariance
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-! Actual all-parity polynomial tangent gaps for the labeled spherical
comparison. The entire negative-overlap covariance error is bounded by the
literal original coefficient budget and an actual overlap-event indicator.
No replica positivity or pressure estimate is assumed. -/

namespace SlowEquilibration.SphericalParisiLabeledBregman

noncomputable section
open Set SphericalParisiLabeledCovariance
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {σ : Type*} [Fintype σ]

def covarianceBudget (c : σ → ℝ) : ℝ := ∑ i,c i

theorem covarianceBudget_nonnegative (c : σ → ℝ) (hc : ∀ i,0 ≤ c i) :
    0 ≤ covarianceBudget c := Finset.sum_nonneg (fun i _ => hc i)

theorem hasDerivAt_xi (d : σ → ℕ) (c : σ → ℝ) (r : ℝ) :
    HasDerivAt (xi d c) (xi1 d c r) r := by
  unfold xi xi1
  convert HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) =>
    (hasDerivAt_pow (d i) r).const_mul (c i)) using 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem xi_convex_positive (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i,0 ≤ c i) :
    ConvexOn ℝ (Ici 0) (xi d c) := by
  refine ⟨convex_Ici 0,?_⟩
  intro x hx y hy a b ha hb hab
  unfold xi
  simp only [smul_eq_mul]
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hh := (convexOn_pow (𝕜 := ℝ) (d i)).2 hx hy ha hb hab
  have h := mul_le_mul_of_nonneg_left hh (hc i)
  simpa only [smul_eq_mul] using h.trans_eq (by ring)

theorem bregmanGap_nonnegative_positive (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0 ≤ c i) {r q : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) :
    0 ≤ bregmanGap d c r q := by
  have hconv := xi_convex_positive d c hc
  have hder := hasDerivAt_xi d c q
  have hs : xi d c q+xi1 d c q*(r-q) ≤ xi d c r := by
    rcases lt_trichotomy q r with hlt | heq | hgt
    · have h := hconv.le_slope_of_hasDerivAt hq hr hlt hder
      rw [slope_def_field] at h
      have hh := (le_div_iff₀ (sub_pos.mpr hlt)).mp h
      linarith
    · subst r
      simp
    · have h := hconv.slope_le_of_hasDerivAt hr hq hgt hder
      rw [slope_def_field] at h
      have hh := (div_le_iff₀ (sub_pos.mpr hgt)).mp h
      nlinarith
  unfold bregmanGap
  linarith

theorem theta_nonnegative (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0 ≤ c i) (hd : ∀ i,1 ≤ d i) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ theta d c q := by
  rw [theta_eq_positive_polynomial d c hd]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg
    (mul_nonneg (hc i) (Nat.cast_nonneg _)) (pow_nonneg hq _))

/-- True signed-overlap covariance control uses the original positive
degree coefficients, including every odd term. -/
theorem abs_xi_le_budget_mul_abs (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0 ≤ c i) (hd : ∀ i,1 ≤ d i) {r : ℝ} (hr : |r| ≤ 1) :
    |xi d c r| ≤ covarianceBudget c*|r| := by
  unfold xi covarianceBudget
  calc
    _ ≤ ∑ i,|c i*r^(d i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,c i*|r| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul,abs_of_nonneg (hc i),abs_pow]
      have hp : |r|^(d i) ≤ |r| := by
        rw [← Nat.sub_add_cancel (hd i),pow_succ]
        exact (mul_le_mul_of_nonneg_right
          (pow_le_one₀ (n := d i-1) (abs_nonneg _) hr) (abs_nonneg r)).trans_eq (one_mul _)
      exact mul_le_mul_of_nonneg_left hp (hc i)
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem negative_bregmanGap_le_budget_mul_abs (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0 ≤ c i) (hd : ∀ i,1 ≤ d i) {r q : ℝ}
    (hr : |r| ≤ 1) (hr0 : r ≤ 0) (hq : 0 ≤ q) :
    -bregmanGap d c r q ≤ covarianceBudget c*|r| := by
  have hxi := (abs_le.mp (abs_xi_le_budget_mul_abs d c hc hd hr)).1
  have htheta := theta_nonnegative d c hc hd hq
  have hterm := mul_nonneg (neg_nonneg.mpr hr0) (xi1_nonnegative d c hc hq)
  have he : bregmanGap d c r q=xi d c r-r*xi1 d c q+theta d c q := by
    unfold bregmanGap theta
    ring
  rw [he]
  linarith

/-- The actual covariance defect is an arbitrarily small near-zero error
plus a coefficient-budget multiple of the genuine negative-overlap event. -/
theorem negative_bregmanGap_indicator_bound (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0 ≤ c i) (hd : ∀ i,1 ≤ d i) {r q ε : ℝ}
    (hr : |r| ≤ 1) (hq : 0 ≤ q) (hε : 0 ≤ ε) :
    -bregmanGap d c r q ≤ covarianceBudget c*ε+
      covarianceBudget c*(if r ≤ -ε then (1 : ℝ) else 0) := by
  have hC := covarianceBudget_nonnegative c hc
  by_cases hbad : r ≤ -ε
  · rw [ite_eq_left hbad,mul_one]
    have hh := negative_bregmanGap_le_budget_mul_abs d c hc hd hr (by linarith) hq
    have hb := mul_le_mul_of_nonneg_left hr hC
    nlinarith [mul_nonneg hC hε]
  · rw [ite_eq_right hbad,mul_zero,add_zero]
    by_cases hr0 : 0 ≤ r
    · have hh := bregmanGap_nonnegative_positive d c hc hr0 hq
      nlinarith [mul_nonneg hC hε]
    · have hrneg : r ≤ 0 := le_of_not_ge hr0
      have hh := negative_bregmanGap_le_budget_mul_abs d c hc hd hr hrneg hq
      have ha : |r| ≤ ε := by rw [abs_of_nonpos hrneg];linarith
      exact hh.trans (mul_le_mul_of_nonneg_left ha hC)

end
end SlowEquilibration.SphericalParisiLabeledBregman

-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalConvexRSLower
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

@[expose] public section

/-! # Genuine nonnegative finite-mixture Taylor residual

The covariance remaining after constant and linear latitude conditioning is
represented by literal binomial tensor coefficients, with no degrees below two.
-/

namespace SlowEquilibration.FiniteMixture
noncomputable section
open Set
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

/-- Actual second-and-higher-order coefficients of ξ(r+s t). -/
def taylorResidualCoefficients (μ : FiniteMixture) (r s : ℝ) : ℕ →₀ ℝ :=
  ∑ p ∈ μ.coeff.support, ∑ k ∈ Finset.range (p+1),
    if 2 ≤ k then Finsupp.single k
      (μ.coeff p * (p.choose k : ℝ) * r^(p-k) * s^k) else 0

lemma taylorResidualCoefficients_apply (μ : FiniteMixture) (r s : ℝ) (k : ℕ) :
    taylorResidualCoefficients μ r s k =
      if 2 ≤ k then ∑ p ∈ μ.coeff.support,
        μ.coeff p * (p.choose k : ℝ) * r^(p-k) * s^k else 0 := by
  classical
  unfold taylorResidualCoefficients
  simp only [Finsupp.finsetSum_apply]
  by_cases hk : 2 ≤ k
  · rw [ite_eq_left hk]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro j hj hjk
      by_cases hj2 : 2 ≤ j <;> simp [hj2, Ne.symm hjk]
    · intro hknot
      have hpk : p < k := by have h := hknot; simp only [Finset.mem_range, not_lt] at h; omega
      simp [hk, Nat.choose_eq_zero_of_lt hpk]
  · rw [ite_eq_right hk]
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hjk : j = k
    · subst j; simp [hk]
    · by_cases hj2 : 2 ≤ j <;> simp [hj2, Ne.symm hjk]

lemma taylorResidualCoefficients_nonneg (μ : FiniteMixture) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (k : ℕ) : 0 ≤ taylorResidualCoefficients μ r s k := by
  rw [taylorResidualCoefficients_apply]
  split_ifs
  · exact Finset.sum_nonneg fun p _ => mul_nonneg (mul_nonneg (mul_nonneg (μ.nonneg p) (Nat.cast_nonneg _)) (pow_nonneg hr _)) (pow_nonneg hs _)
  · exact le_rfl

lemma taylorResidualCoefficients_zero_below_two (μ : FiniteMixture) (r s : ℝ)
    {k : ℕ} (hk : k < 2) : taylorResidualCoefficients μ r s k = 0 := by
  rw [taylorResidualCoefficients_apply, ite_eq_right (by omega)]

lemma taylorResidualCoefficients_two_pos (μ : FiniteMixture) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) : 0 < taylorResidualCoefficients μ r s 2 := by
  rw [taylorResidualCoefficients_apply, ite_eq_left (by omega)]
  apply Finset.sum_pos _ μ.support_nonempty
  intro p hp
  have hc := μ.coeff_pos hp
  have hchoose : 0 < (p.choose 2 : ℝ) := by exact_mod_cast Nat.choose_pos (μ.degree_ge_two hp)
  positivity

/-- The actual nonzero finite covariance remaining after the first two jets. -/
def taylorResidual (μ : FiniteMixture) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) : FiniteMixture where
  coeff := taylorResidualCoefficients μ r s
  nonneg := taylorResidualCoefficients_nonneg μ hr.le hs.le
  zero_below_two := fun k hk => taylorResidualCoefficients_zero_below_two μ r s hk
  nonzero := by
    intro hzero
    have hh := congrArg (fun f : ℕ →₀ ℝ => f 2) hzero
    simp only [Finsupp.zero_apply] at hh
    exact (taylorResidualCoefficients_two_pos μ hr hs).ne' hh


lemma sum_binomial_residual (p : ℕ) (hp : 2 ≤ p) (c r s t : ℝ) :
    (∑ k ∈ Finset.range (p+1), if 2 ≤ k then
      (c * (p.choose k : ℝ) * r^(p-k) * s^k) * t^k else 0) =
      c*(r+s*t)^p-c*r^p-c*(p : ℝ)*r^(p-1)*s*t := by
  classical
  let f : ℕ → ℝ := fun k => (c * (p.choose k : ℝ) * r^(p-k) * s^k) * t^k
  have hall : (∑ k ∈ Finset.range (p+1), f k) = c*(r+s*t)^p := by
    rw [add_comm r (s*t),add_pow,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [f]
    rw [mul_pow]
    ring
  have hsplit : (∑ k ∈ Finset.range (p+1), if 2 ≤ k then f k else 0) =
      (∑ k ∈ Finset.range (p+1), f k)-f 0-f 1 := by
    have hpEq : p+1=2+(p-1) := by omega
    rw [hpEq,Finset.sum_range_add,Finset.sum_range_add]
    have hsmall : (∑ k ∈ Finset.range 2, if 2 ≤ k then f k else 0)=0 := by
      norm_num [Finset.sum_range_succ]
    rw [hsmall]
    simp only [zero_add]
    have htail : (∑ k ∈ Finset.range (p-1), if 2 ≤ 2+k then f (2+k) else 0)=
        ∑ k ∈ Finset.range (p-1), f (2+k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [ite_eq_left (by omega)]
    rw [htail]
    norm_num [Finset.sum_range_succ]
    ring
  rw [hsplit,hall]
  simp only [f, Nat.sub_zero,Nat.choose_zero_right,Nat.cast_one,pow_zero,
    mul_one,Nat.choose_one_right,pow_one]

/-- Literal covariance identity for the actual constructed finite residual. -/
theorem taylorResidual_xi (μ : FiniteMixture) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (t : ℝ) :
    (taylorResidual μ hr hs).xi t = μ.xi (r+s*t)-μ.xi r-s*μ.xi1 r*t := by
  classical
  change (taylorResidualCoefficients μ r s).sum (fun k a => a*t^k) = _
  unfold taylorResidualCoefficients
  rw [← Finsupp.sum_finsetSum_index (h := fun k (a : ℝ) => a*t^k) (fun k => by simp)
    (fun k a b => by ring)]
  simp_rw [← Finsupp.sum_finsetSum_index (h := fun k (a : ℝ) => a*t^k) (fun k => by simp)
    (fun k a b => by ring)]
  have hterm (p : ℕ) (hp : p ∈ μ.coeff.support) :
      (∑ k ∈ Finset.range (p+1),
        (if 2 ≤ k then Finsupp.single k
          (μ.coeff p * (p.choose k : ℝ) * r^(p-k) * s^k) else 0).sum
            (fun k a => a*t^k)) =
        μ.coeff p*(r+s*t)^p-μ.coeff p*r^p-μ.coeff p*(p : ℝ)*r^(p-1)*s*t := by
    convert sum_binomial_residual p (μ.degree_ge_two hp) (μ.coeff p) r s t using 1
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs
    · exact Finsupp.sum_single_index (by ring)
    · rfl
  unfold FiniteMixture.xi FiniteMixture.xi1
  rw [Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hterm p hp]
  ring


/-- Removing a constant and a linear term preserves actual convexity on
all admissible signed residual overlaps. -/
theorem taylorResidual_convexOn (μ : FiniteMixture) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s)
    (hright : r+s ≤ 1)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) :
    ConvexOn ℝ (Icc (-1 : ℝ) 1) (taylorResidual μ hr hs).xi := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy a b ha hb hab
  have harg (z : ℝ) (hz : z ∈ Icc (-1 : ℝ) 1) : r+s*z ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> nlinarith [mul_nonneg hs.le (by linarith [hz.1] : 0 ≤ z+1),
      mul_nonneg hs.le (by linarith [hz.2] : 0 ≤ 1-z)]
  have hh := hconv.2 (harg x hx) (harg y hy) ha hb hab
  simp only [smul_eq_mul] at hh ⊢
  have heq : a*(r+s*x)+b*(r+s*y)=r+s*(a*x+b*y) := by
    linear_combination r*hab
  rw [heq] at hh
  rw [taylorResidual_xi,taylorResidual_xi,taylorResidual_xi]
  have hzero : μ.xi r*(a+b-1)=0 := by rw [hab];ring
  nlinarith

/-- The proved physical zero-field RS theorem applies to this actual
finite residual whenever its own static-threshold condition holds. -/
theorem taylorResidual_quenchedPressure_tendsto_annealed (μ : FiniteMixture) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hright : r+s ≤ 1)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β : ℝ} (hβ : 0 ≤ β)
    (hstatic : β ≤ Thresholds.staticThreshold (taylorResidual μ hr hs).xi) :
    Filter.Tendsto (fun N : ℕ => SphericalModel.quenchedPressure N (taylorResidual μ hr hs) β)
      Filter.atTop (nhds (β^2*(taylorResidual μ hr hs).xi 1/2)) :=
  SphericalModel.convex_quenchedPressure_tendsto_annealed_le_static _
    (taylorResidual_convexOn μ hr hs hright hconv) hβ hstatic


/-- Once the affine covariance range is nonnegative, original odd degrees
also give genuine convexity on every signed residual overlap. -/
theorem taylorResidual_convexOn_of_nonnegative_range (μ : FiniteMixture) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hsr : s ≤ r) :
    ConvexOn ℝ (Icc (-1 : ℝ) 1) (taylorResidual μ hr hs).xi := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy a b ha hb hab
  have harg (z : ℝ) (hz : z ∈ Icc (-1 : ℝ) 1) : r+s*z ∈ Ici (0 : ℝ) := by
    change 0 ≤ r+s*z
    nlinarith [mul_nonneg hs.le (by linarith [hz.1] : 0 ≤ z+1)]
  have hh := μ.convexOn_xi_Ici.2 (harg x hx) (harg y hy) ha hb hab
  simp only [smul_eq_mul] at hh ⊢
  have heq : a*(r+s*x)+b*(r+s*y)=r+s*(a*x+b*y) := by
    linear_combination r*hab
  rw [heq] at hh
  rw [taylorResidual_xi,taylorResidual_xi,taylorResidual_xi]
  have hzero : μ.xi r*(a+b-1)=0 := by rw [hab];ring
  nlinarith

/-- Genuine physical RS pressure for the actual arbitrary-parity residual
when its affine covariance range is nonnegative. -/
theorem taylorResidual_quenchedPressure_tendsto_of_nonnegative_range (μ : FiniteMixture)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hsr : s ≤ r)
    {β : ℝ} (hβ : 0 ≤ β)
    (hstatic : β ≤ Thresholds.staticThreshold (taylorResidual μ hr hs).xi) :
    Filter.Tendsto (fun N : ℕ => SphericalModel.quenchedPressure N (taylorResidual μ hr hs) β)
      Filter.atTop (nhds (β^2*(taylorResidual μ hr hs).xi 1/2)) :=
  SphericalModel.convex_quenchedPressure_tendsto_annealed_le_static _
    (taylorResidual_convexOn_of_nonnegative_range μ hr hs hsr) hβ hstatic

end
end SlowEquilibration.FiniteMixture

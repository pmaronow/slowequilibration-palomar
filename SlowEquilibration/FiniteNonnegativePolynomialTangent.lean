-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeCovariance

@[expose] public section

/-! # Tangent support for nonnegative finite polynomials with linear terms

Constant and linear terms are retained exactly. Every higher monomial
supports its tangent at a nonnegative atom on the whole interval [-atom,∞).
-/
namespace SlowEquilibration.FiniteNonnegativePolynomial
noncomputable section
open Set
open scoped BigOperators
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι : Type*} [Fintype ι]

def covariance (degree : ι → ℕ) (coefficient : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i,coefficient i*t^(degree i)

def firstDerivative (degree : ι → ℕ) (coefficient : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i,coefficient i*(degree i : ℝ)*t^(degree i-1)

theorem covariance_hasDerivAt (degree : ι → ℕ) (coefficient : ι → ℝ) (t : ℝ) :
    HasDerivAt (covariance degree coefficient) (firstDerivative degree coefficient t) t := by
  have hd := HasDerivAt.fun_sum (fun i (_ : i∈Finset.univ) => ((hasDerivAt_id t).pow (degree i)).const_mul (coefficient i))
  convert hd using 1
  · rfl
  · unfold firstDerivative
    apply Finset.sum_congr rfl
    intro i _
    simp only [id_eq]
    ring

theorem covariance_convexOn_Ici (degree : ι → ℕ) (coefficient : ι → ℝ)
    (hc : ∀ i,0≤coefficient i) : ConvexOn ℝ (Ici 0) (covariance degree coefficient) := by
  classical
  have hsum : ∀ s : Finset ι,ConvexOn ℝ (Ici 0) (fun t : ℝ => ∑ i∈s,coefficient i*t^(degree i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using convexOn_const (0 : ℝ) (convex_Ici (0 : ℝ))
    | @insert i s hi ih =>
        have hpow : ConvexOn ℝ (Ici 0) (fun t : ℝ => coefficient i*t^(degree i)) := by
          simpa only [smul_eq_mul] using ConvexOn.smul (hc i) (convexOn_pow (𝕜 := ℝ) (degree i))
        exact (hpow.add ih).congr (fun t _ => by simp only [Pi.add_apply,Finset.sum_insert hi])
  exact hsum Finset.univ

theorem covariance_tangent_le_of_nonneg (degree : ι → ℕ) (coefficient : ι → ℝ)
    (hc : ∀ i,0≤coefficient i) {t r : ℝ} (ht : 0≤t) (hr : 0≤r) :
    covariance degree coefficient t+firstDerivative degree coefficient t*(r-t)≤covariance degree coefficient r := by
  have hconv := covariance_convexOn_Ici degree coefficient hc
  have hd := covariance_hasDerivAt degree coefficient t
  by_cases htr : t<r
  · have hs := hconv.le_slope_of_hasDerivAt ht hr htr hd
    rw [slope_def_field] at hs
    have hh := (le_div_iff₀ (sub_pos.mpr htr)).mp hs
    linarith
  · by_cases hrt : r<t
    · have hs := hconv.slope_le_of_hasDerivAt hr ht hrt hd
      rw [slope_def_field] at hs
      have hh := (div_le_iff₀ (sub_pos.mpr hrt)).mp hs
      nlinarith
    · have he : r=t := le_antisymm (le_of_not_gt htr) (le_of_not_gt hrt)
      simp [he]

/-- Exact monomial supporting line on the negative interval, including
constant and linear degrees rather than requiring their absence. -/
theorem monomial_tangent_le_negative (k : ℕ) {t r : ℝ} (ht : 0≤t) (hr : r∈Icc (-t) 0) :
    t^k+(k : ℝ)*t^(k-1)*(r-t)≤r^k := by
  by_cases hk0 : k=0
  · subst k; simp
  by_cases hk1 : k=1
  · subst k; simp
  have hk2 : 2≤k := by omega
  have hkR : (2 : ℝ)≤k := by exact_mod_cast hk2
  have habs : |r|≤t := abs_le.mpr ⟨hr.1,hr.2.trans ht⟩
  have hpowabs : |r^k|≤t^k := by rw [abs_pow];exact pow_le_pow_left₀ (abs_nonneg _) habs k
  have hl : -t^k≤r^k := (neg_le_neg hpowabs).trans (neg_abs_le _)
  have hpow : t^k=t^(k-1)*t := by rw [← pow_succ];congr 1;omega
  have htpk : 0≤t^k := pow_nonneg ht k
  have hkr := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (Nat.cast_nonneg k) (pow_nonneg ht (k-1))) hr.2
  have hdegree := mul_le_mul_of_nonneg_right hkR htpk
  rw [hpow] at hdegree hl ⊢
  nlinarith

/-- Every nonnegative finite polynomial, including degrees zero and one,
obeys its actual supporting line on [-atom,∞). -/
theorem covariance_tangent_le (degree : ι → ℕ) (coefficient : ι → ℝ)
    (hc : ∀ i,0≤coefficient i) {t r : ℝ} (ht : 0≤t) (hr : -t≤r) :
    covariance degree coefficient t+firstDerivative degree coefficient t*(r-t)≤covariance degree coefficient r := by
  by_cases hr0 : 0≤r
  · exact covariance_tangent_le_of_nonneg degree coefficient hc ht hr0
  · unfold covariance firstDerivative
    rw [Finset.sum_mul,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hh := mul_le_mul_of_nonneg_left
      (monomial_tangent_le_negative (degree i) ht ⟨hr,(lt_of_not_ge hr0).le⟩) (hc i)
    nlinarith

theorem firstDerivative_nonneg (degree : ι → ℕ) (coefficient : ι → ℝ)
    (hc : ∀ i,0≤coefficient i) {t : ℝ} (ht : 0≤t) :
    0≤firstDerivative degree coefficient t := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (hc i) (Nat.cast_nonneg _)) (pow_nonneg ht _)

end
end SlowEquilibration.FiniteNonnegativePolynomial

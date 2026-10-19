-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalEvenCovariance
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-!
# Tangent support for finite covariances on spherical latitudes

Odd degrees are allowed. On negative overlaps the coefficient degree lower
bound, together with the absolute monomial estimate, replaces global
convexity. All inequalities concern the actual finite covariance polynomial.
-/

namespace SlowEquilibration.FiniteMixture

noncomputable section
open Set
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every nonnegative finite mixture is convex on nonnegative overlaps,
regardless of the parities of its supported degrees. -/
theorem convexOn_xi_Ici (μ : FiniteMixture) : ConvexOn ℝ (Ici 0) μ.xi := by
  have hsum : ∀ s : Finset ℕ,
      ConvexOn ℝ (Ici 0) (fun r : ℝ => ∑ p ∈ s, μ.coeff p*r^p) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simpa using convexOn_const (0 : ℝ) (convex_Ici (0 : ℝ))
    | @insert p s hp ih =>
      have hpow : ConvexOn ℝ (Ici 0) (fun r : ℝ => μ.coeff p*r^p) := by
        simpa only [smul_eq_mul] using
          ConvexOn.smul (μ.nonneg p) (convexOn_pow (𝕜 := ℝ) p)
      exact (hpow.add ih).congr (fun r _ => by
        simp only [Pi.add_apply, Finset.sum_insert hp])
  exact hsum μ.coeff.support

/-- The actual covariance derivative is nonnegative on nonnegative overlaps. -/
theorem xi1_nonneg (μ : FiniteMixture) {q : ℝ} (hq : 0 ≤ q) : 0 ≤ μ.xi1 q := by
  unfold xi1
  exact Finset.sum_nonneg (fun p _ =>
    mul_nonneg (mul_nonneg (μ.nonneg p) (Nat.cast_nonneg p)) (pow_nonneg hq _))

/-- The absence of degrees below two implies the actual degree lower-bound
inequality at every nonnegative overlap. -/
theorem xi_degree_lower_bound (μ : FiniteMixture) {q : ℝ} (hq : 0 ≤ q) :
    2*μ.xi q ≤ q*μ.xi1 q := by
  unfold xi xi1
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hp2 := μ.degree_ge_two hp
  have hpcast : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hpow : q^p = q^(p-1)*q := by
    rw [← pow_succ]
    congr 1
    omega
  calc
    2*(μ.coeff p*q^p) ≤ (p : ℝ)*(μ.coeff p*q^p) :=
      mul_le_mul_of_nonneg_right hpcast (mul_nonneg (μ.nonneg p) (pow_nonneg hq p))
    _ = q*(μ.coeff p*(p : ℝ)*q^(p-1)) := by rw [hpow]; ring

/-- Negative overlaps of magnitude at most `q` cannot make the actual
covariance smaller than `-ξ(q)`, including odd-degree mixtures. -/
theorem neg_xi_le_xi (μ : FiniteMixture) {q r : ℝ} (hq : 0 ≤ q)
    (hr : r ∈ Icc (-q) 0) : -μ.xi q ≤ μ.xi r := by
  have habs : |r| ≤ q := abs_le.mpr ⟨hr.1, hr.2.trans hq⟩
  unfold xi
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hpow : |r^p| ≤ q^p := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg r) habs p
  calc
    -(μ.coeff p*q^p) ≤ -(μ.coeff p*|r^p|) :=
      neg_le_neg (mul_le_mul_of_nonneg_left hpow (μ.nonneg p))
    _ = -|μ.coeff p*r^p| := by rw [abs_mul, abs_of_nonneg (μ.nonneg p)]
    _ ≤ μ.coeff p*r^p := neg_abs_le _

/-- The genuine tangent-line inequality on nonnegative overlaps. -/
theorem xi_tangent_le_of_nonneg (μ : FiniteMixture) {q r : ℝ}
    (hq : 0 ≤ q) (hr : 0 ≤ r) :
    μ.xi q+μ.xi1 q*(r-q) ≤ μ.xi r := by
  by_cases hqr : q < r
  · have hs := μ.convexOn_xi_Ici.le_slope_of_hasDerivAt hq hr hqr (μ.hasDerivAt_xi q)
    rw [slope_def_field] at hs
    have hb := (le_div_iff₀ (sub_pos.mpr hqr)).mp hs
    linarith
  · by_cases hrq : r < q
    · have hs := μ.convexOn_xi_Ici.slope_le_of_hasDerivAt hr hq hrq (μ.hasDerivAt_xi q)
      rw [slope_def_field] at hs
      have hb := (div_le_iff₀ (sub_pos.mpr hrq)).mp hs
      nlinarith
    · have heq : r = q := le_antisymm (le_of_not_gt hqr) (le_of_not_gt hrq)
      simp [heq]

/-- A finite nonnegative covariance with degrees at least two lies above
its tangent at `q` on the entire interval `[-q,1]`. This remains valid with
odd supported degrees and does not assume global convexity. -/
theorem xi_tangent_le (μ : FiniteMixture) {q r : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) (hr : r ∈ Icc (-q) 1) :
    μ.xi q+μ.xi1 q*(r-q) ≤ μ.xi r := by
  by_cases hr0 : 0 ≤ r
  · exact μ.xi_tangent_le_of_nonneg hq.1 hr0
  · have hrneg : r ∈ Icc (-q) 0 := ⟨hr.1, (lt_of_not_ge hr0).le⟩
    have hneg := μ.neg_xi_le_xi hq.1 hrneg
    have hdegree := μ.xi_degree_lower_bound hq.1
    have hprod := mul_nonpos_of_nonneg_of_nonpos (μ.xi1_nonneg hq.1) hrneg.2
    nlinarith

/-- Literal latitude overlaps lie in the tangent-support interval whenever
the latitude is at least one half and the transverse overlap lies in `[-1,1]`. -/
theorem latitudeOverlap_mem_Icc {q t : ℝ} (hq : q ∈ Icc (1/2 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    q^2+(1-q^2)*t ∈ Icc (-q) 1 := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hc : 0 ≤ 1-q^2 := by nlinarith [hq.2]
  have hl := mul_le_mul_of_nonneg_left ht.1 hc
  have hu := mul_le_mul_of_nonneg_left ht.2 hc
  have hp := mul_nonneg (by linarith [hq.1] : 0 ≤ 2*q-1)
    (by linarith : 0 ≤ q+1)
  constructor <;> nlinarith

/-- Actual covariance tangent support at literal latitude overlaps. -/
theorem xi_latitude_tangent_le (μ : FiniteMixture) {q t : ℝ}
    (hq : q ∈ Icc (1/2 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1) :
    μ.xi q+μ.xi1 q*(q^2+(1-q^2)*t-q) ≤ μ.xi (q^2+(1-q^2)*t) :=
  μ.xi_tangent_le ⟨by linarith [hq.1], hq.2⟩ (latitudeOverlap_mem_Icc hq ht)

end

end SlowEquilibration.FiniteMixture

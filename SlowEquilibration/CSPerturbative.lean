-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSParisiMeasure
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.SMul

@[expose] public section

namespace SlowEquilibration.CSPerturbative

open Set CrisantiSommers CSParisiMeasure

/-- The coefficient-weighted second moment of the displacement from the
base degree. The base monomial has displacement zero. -/
noncomputable def spreadMass (μ : FiniteMixture) (d : ℕ) : ℝ :=
  ∑ p ∈ μ.coeff.support, μ.curvatureCoeff p * ((p - d : ℕ) : ℝ) ^ 2

theorem spreadMass_nonneg (μ : FiniteMixture) (d : ℕ) : 0 ≤ spreadMass μ d := by
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (μ.curvatureCoeff_pos hp).le (sq_nonneg _)

private theorem tiltedVariance_le_referenceMoment (μ : FiniteMixture)
    {r : ℝ} (hr : 0 < r) (n : ℝ) :
    μ.tiltedVariance r ≤
      ∑ p ∈ μ.coeff.support, μ.tiltedWeight r p * (((p - 2 : ℕ) : ℝ) - n) ^ 2 := by
  have hexpand : ∀ p : ℕ,
      μ.tiltedWeight r p * (((p - 2 : ℕ) : ℝ) - n) ^ 2 =
        μ.tiltedWeight r p * ((p - 2 : ℕ) : ℝ) ^ 2 -
          2 * n * (μ.tiltedWeight r p * ((p - 2 : ℕ) : ℝ)) +
          n ^ 2 * μ.tiltedWeight r p := by intro p; ring
  simp_rw [hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, μ.tiltedWeight_sum hr, μ.tiltedVariance_eq_second_sub_sq hr]
  change μ.tiltedSecondMoment r - μ.tiltedMean r ^ 2 ≤
    μ.tiltedSecondMoment r - 2*n*μ.tiltedMean r + n^2*1
  nlinarith [sq_nonneg (μ.tiltedMean r - n)]

/-- A quantitative actual tilted-variance bound. Higher-degree contributions
are uniformly controlled on `(0,1]` by their coefficient displacement moment. -/
theorem tiltedVariance_le_spreadMass (μ : FiniteMixture) {d : ℕ}
    (hd : 3 ≤ d) (hdegrees : ∀ p ∈ μ.coeff.support, d ≤ p)
    (hbase : 0 < μ.coeff d) {r : ℝ} (hr : r ∈ Ioc 0 1) :
    μ.tiltedVariance r ≤ spreadMass μ d / μ.curvatureCoeff d := by
  have hdmem : d ∈ μ.coeff.support := Finsupp.mem_support_iff.mpr hbase.ne'
  have hB : 0 < μ.curvatureCoeff d := μ.curvatureCoeff_pos hdmem
  have hV : μ.curvatureCoeff d * r^(d-2) ≤ μ.xi2 r := by
    unfold FiniteMixture.xi2
    exact Finset.single_le_sum (f := fun p => μ.curvatureCoeff p * r^(p-2)) (fun p hp =>
      mul_nonneg (μ.curvatureCoeff_pos hp).le (pow_nonneg hr.1.le _)) hdmem
  have hN : (∑ p ∈ μ.coeff.support,
      μ.rawWeight r p * ((p-d : ℕ) : ℝ)^2) ≤ spreadMass μ d * r^(d-2) := by
    unfold spreadMass
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro p hp
    unfold FiniteMixture.rawWeight
    have hpw : r^(p-2) ≤ r^(d-2) :=
      pow_le_pow_of_le_one hr.1.le hr.2 (by have := hdegrees p hp; omega)
    have hc : 0 ≤ μ.curvatureCoeff p * ((p-d : ℕ) : ℝ)^2 :=
      mul_nonneg (μ.curvatureCoeff_pos hp).le (sq_nonneg _)
    convert mul_le_mul_of_nonneg_left hpw hc using 1
    ring
  have hratio : (∑ p ∈ μ.coeff.support,
      μ.rawWeight r p * ((p-d : ℕ) : ℝ)^2) / μ.xi2 r ≤
        spreadMass μ d / μ.curvatureCoeff d := by
    apply (div_le_div_iff₀ (μ.xi2_pos hr.1) hB).mpr
    calc
      _ ≤ (spreadMass μ d * r^(d-2)) * μ.curvatureCoeff d :=
        mul_le_mul_of_nonneg_right hN hB.le
      _ = spreadMass μ d * (μ.curvatureCoeff d * r^(d-2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hV (spreadMass_nonneg μ d)
  have href := tiltedVariance_le_referenceMoment μ hr.1 ((d:ℝ)-2)
  have hterm : ∀ p ∈ μ.coeff.support,
      (((p-2 : ℕ):ℝ)-((d:ℝ)-2)) = ((p-d : ℕ):ℝ) := by
    intro p hp
    have hpD := hdegrees p hp
    rw [Nat.cast_sub (by omega : 2≤p), Nat.cast_sub hpD]
    simp only [Nat.cast_ofNat]
    ring
  have hRefEq : (∑ p ∈ μ.coeff.support,
      μ.tiltedWeight r p * (((p-2 : ℕ):ℝ)-((d:ℝ)-2))^2) =
      ∑ p ∈ μ.coeff.support, μ.tiltedWeight r p * ((p-d : ℕ):ℝ)^2 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hterm p hp]
  rw [hRefEq] at href
  unfold FiniteMixture.tiltedWeight at href
  simp_rw [div_mul_eq_mul_div] at href
  rw [← Finset.sum_div] at href
  exact href.trans hratio

private theorem tiltedMean_ge_baseDegree (μ : FiniteMixture) {d : ℕ}
    (hd : 3 ≤ d) (hdegrees : ∀ p ∈ μ.coeff.support, d ≤ p)
    {r : ℝ} (hr : 0 < r) : (d:ℝ)-2 ≤ μ.tiltedMean r := by
  have hsum : (∑ p ∈ μ.coeff.support, μ.tiltedWeight r p * ((d:ℝ)-2)) ≤
      ∑ p ∈ μ.coeff.support, μ.tiltedWeight r p * ((p-2 : ℕ):ℝ) := by
    apply Finset.sum_le_sum
    intro p hp
    have hpD := hdegrees p hp
    apply mul_le_mul_of_nonneg_left _ (μ.tiltedWeight_nonneg hr p)
    rw [Nat.cast_sub (by omega : 2≤p)]
    push_cast
    exact sub_le_sub_right (Nat.cast_le.mpr hpD) 2
  simpa only [← Finset.sum_mul, μ.tiltedWeight_sum hr, one_mul,
    FiniteMixture.tiltedMean] using hsum

/-- A direct coefficient sufficient condition for the positive curvature
numerator of the genuine covariance second derivative. -/
theorem curvature_positive_of_spreadMass (μ : FiniteMixture) {d : ℕ}
    (hd : 3 ≤ d) (hdegrees : ∀ p ∈ μ.coeff.support, d ≤ p)
    (hbase : 0 < μ.coeff d)
    (hsmall : 2*spreadMass μ d < μ.curvatureCoeff d * (d:ℝ) * ((d:ℝ)-2))
    {r : ℝ} (hr : r ∈ Ioc 0 1) :
    0 < 3 * μ.v1 r ^ 2 - 2 * μ.xi2 r * μ.v2 r := by
  have hB := μ.curvatureCoeff_pos (Finsupp.mem_support_iff.mpr hbase.ne')
  have hv := tiltedVariance_le_spreadMass μ hd hdegrees hbase hr
  have hm := tiltedMean_ge_baseDegree μ hd hdegrees hr.1
  have hdR : (3:ℝ) ≤ d := by exact_mod_cast hd
  have hvar : 2*μ.tiltedVariance r < (d:ℝ)*((d:ℝ)-2) := by
    have hsmall' : spreadMass μ d / μ.curvatureCoeff d < (d:ℝ)*((d:ℝ)-2)/2 := by
      apply (div_lt_iff₀ hB).mpr
      nlinarith
    linarith
  have hmcurv : (d:ℝ)*((d:ℝ)-2) ≤ μ.tiltedMean r ^ 2 + 2*μ.tiltedMean r := by
    nlinarith [sq_nonneg (μ.tiltedMean r - ((d:ℝ)-2))]
  have hscaled : 0 < r^2 / μ.xi2 r^2 *
      (3*μ.v1 r^2-2*μ.xi2 r*μ.v2 r) := by
    rw [μ.curvature_identity hr.1]
    linarith
  exact pos_of_mul_pos_right hscaled (div_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The quantitative coefficient criterion also gives the genuine positive
second derivative of the inverse-square-root function at every required radius. -/
theorem inverseSqrt_second_derivative_pos_of_spreadMass (μ : FiniteMixture) {d : ℕ}
    (hd : 3 ≤ d) (hdegrees : ∀ p ∈ μ.coeff.support, d ≤ p)
    (hbase : 0 < μ.coeff d)
    (hsmall : 2*spreadMass μ d < μ.curvatureCoeff d * (d:ℝ) * ((d:ℝ)-2))
    {r : ℝ} (hr : r ∈ Ioc 0 1) :
    0 < deriv (deriv (InverseSqrtCalculus.inverseSqrt (deriv (deriv μ.xi)))) r := by
  rw [μ.deriv_deriv_xi]
  apply InverseSqrtCalculus.deriv2_inverseSqrt_pos (s := Ioi 0) isOpen_Ioi
    (fun t ht => μ.xi2_pos ht) (fun t _ => (μ.hasDerivAt_xi2 t).differentiableAt)
    hr.1 (μ.differentiableAt_deriv_xi2 r)
  rw [(μ.hasDerivAt_xi2 r).deriv, congrFun μ.deriv_deriv_xi2 r]
  exact curvature_positive_of_spreadMass μ hd hdegrees hbase hsmall hr

/-- The coefficient criterion proves strict convexity of the genuine
inverse square root on the full required interval, including radius one. -/
theorem strictConvexOn_inverseSqrt_of_spreadMass (μ : FiniteMixture) {d : ℕ}
    (hd : 3 ≤ d) (hdegrees : ∀ p ∈ μ.coeff.support, d ≤ p)
    (hbase : 0 < μ.coeff d)
    (hsmall : 2*spreadMass μ d < μ.curvatureCoeff d * (d:ℝ) * ((d:ℝ)-2)) :
    StrictConvexOn ℝ (Ioc 0 1)
      (InverseSqrtCalculus.inverseSqrt (deriv (deriv μ.xi))) := by
  rw [μ.deriv_deriv_xi]
  apply InverseSqrtCalculus.strictConvexOn_inverseSqrt (convex_Ioc 0 1)
  · intro r hr
    exact (μ.hasDerivAt_xi2 r).continuousAt.continuousWithinAt
  · intro r hr
    exact μ.xi2_pos hr.1
  · intro r hr
    exact (μ.hasDerivAt_xi2 r).differentiableAt
  · intro r hr
    exact μ.differentiableAt_deriv_xi2 r
  · intro r hr
    rw [(μ.hasDerivAt_xi2 r).deriv, congrFun μ.deriv_deriv_xi2 r]
    exact curvature_positive_of_spreadMass μ hd hdegrees hbase hsmall (interior_subset hr)

/-- A finite family of nonnegative even perturbing coefficients, supported
strictly above `d` and at most `P`, with total mass at most one. -/
structure EvenPerturbation (d P : ℕ) where
  coeff : ℕ →₀ ℝ
  nonneg : ∀ p, 0 ≤ coeff p
  zero_of_le : ∀ p, p ≤ d → coeff p = 0
  zero_of_gt : ∀ p, P < p → coeff p = 0
  even_supported : ∀ p ∈ coeff.support, Even p
  total_le_one : coeff.sum (fun _ c => c) ≤ 1

namespace EvenPerturbation

variable {d P : ℕ} (b : EvenPerturbation d P)

/-- The actual finite covariance `r^d + ε ∑ b_p r^p`. Zero perturbation
coefficients and `ε=0` remain allowed. -/
noncomputable def covariance (hd : 3 ≤ d) (ε : ℝ) (hε : 0 ≤ ε) : FiniteMixture where
  coeff := Finsupp.single d 1 + ε • b.coeff
  nonneg := by
    intro p
    apply add_nonneg
    · by_cases hp : p=d
      · simp [hp]
      · simp [hp]
    · exact mul_nonneg hε (b.nonneg p)
  zero_below_two := by
    intro p hp
    have hpd : p≠d := by omega
    simp [hpd, b.zero_of_le p (by omega)]
  nonzero := by
    intro hz
    have h := congrArg (fun f : ℕ →₀ ℝ => f d) hz
    simp [b.zero_of_le d le_rfl] at h

@[simp] theorem covariance_coeff (hd : 3 ≤ d) (ε : ℝ) (hε : 0 ≤ ε) (p : ℕ) :
    (b.covariance hd ε hε).coeff p = Finsupp.single d 1 p + ε*b.coeff p := rfl

@[simp] theorem covariance_base_coeff (hd : 3 ≤ d) (ε : ℝ) (hε : 0 ≤ ε) :
    (b.covariance hd ε hε).coeff d = 1 := by
  simp [b.zero_of_le d le_rfl]

theorem covariance_degrees (hd : 3 ≤ d) (ε : ℝ) (hε : 0 ≤ ε)
    {p : ℕ} (hp : p ∈ (b.covariance hd ε hε).coeff.support) : d ≤ p := by
  by_contra hnot
  have hpd : p < d := lt_of_not_ge hnot
  exact (Finsupp.mem_support_iff.mp hp) (by
    simp [ne_of_lt hpd, b.zero_of_le p hpd.le])

/-- The genuine minimum degree remains exactly the base degree. -/
theorem covariance_minDegree (hd : 3 ≤ d) (ε : ℝ) (hε : 0 ≤ ε) :
    (b.covariance hd ε hε).minDegree = d := by
  have hdmem : d ∈ (b.covariance hd ε hε).coeff.support :=
    Finsupp.mem_support_iff.mpr (by rw [b.covariance_base_coeff]; norm_num)
  apply le_antisymm ((b.covariance hd ε hε).degree_bounds hdmem).1
  exact b.covariance_degrees hd ε hε (Finset.min'_mem _ _)

/-- No degree above the specified finite cutoff can be introduced. -/
theorem covariance_maxDegree_le (hd : 3 ≤ d) (hdP : d ≤ P)
    (ε : ℝ) (hε : 0 ≤ ε) : (b.covariance hd ε hε).maxDegree ≤ P := by
  let p := (b.covariance hd ε hε).maxDegree
  have hp : p ∈ (b.covariance hd ε hε).coeff.support := Finset.max'_mem _ _
  by_contra hn
  have hPp : P < p := lt_of_not_ge hn
  have hpd : p ≠ d := by omega
  exact (Finsupp.mem_support_iff.mp hp) (by simp [hpd, b.zero_of_gt p hPp])

/-- The parity conditions are preserved by the actual coefficient constructor. -/
theorem covariance_even_supported (hd : 3 ≤ d) (hdEven : Even d)
    (ε : ℝ) (hε : 0 ≤ ε) {p : ℕ}
    (hp : p ∈ (b.covariance hd ε hε).coeff.support) : Even p := by
  by_cases hpd : p=d
  · simpa [hpd] using hdEven
  · apply b.even_supported
    apply Finsupp.mem_support_iff.mpr
    intro hb0
    exact (Finsupp.mem_support_iff.mp hp) (by simp [hpd, hb0])

/-- The constructor has the exact genuine covariance required in the statement. -/
theorem covariance_xi (hd : 3 ≤ d) (ε : ℝ) (hε : 0 ≤ ε) (r : ℝ) :
    (b.covariance hd ε hε).xi r = r^d + ε*(∑ p ∈ b.coeff.support, b.coeff p*r^p) := by
  change (Finsupp.single d 1 + ε • b.coeff).sum (fun p c => c*r^p) = _
  rw [Finsupp.sum_add_index' (by intro p; simp) (by intro p a c; ring),
    Finsupp.sum_single_index (by simp), Finsupp.sum_smul_index (by intro p; simp)]
  simp only [one_mul, Finsupp.sum]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- The displacement moment is linear in the actual perturbation amplitude. -/
theorem covariance_spreadMass (hd : 3 ≤ d) (ε : ℝ) (hε : 0 ≤ ε) :
    spreadMass (b.covariance hd ε hε) d = ε*
      ∑ p ∈ b.coeff.support,
        b.coeff p*(p:ℝ)*((p-1 : ℕ):ℝ)*((p-d : ℕ):ℝ)^2 := by
  change (Finsupp.single d 1 + ε • b.coeff).sum
    (fun p c => c*(p:ℝ)*((p-1 : ℕ):ℝ)*((p-d : ℕ):ℝ)^2) = _
  rw [Finsupp.sum_add_index' (by intro p; simp) (by intro p a c; ring),
    Finsupp.sum_single_index (by simp), Finsupp.sum_smul_index (by intro p; simp)]
  simp only [Nat.sub_self, Nat.cast_zero, zero_pow (by norm_num : (2:ℕ)≠0),
    mul_zero, zero_add, Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- A uniform coefficient moment bound over all allowed perturbing families. -/
theorem coefficient_spreadMass_le :
    (∑ p ∈ b.coeff.support,
      b.coeff p*(p:ℝ)*((p-1 : ℕ):ℝ)*((p-d : ℕ):ℝ)^2) ≤ (P:ℝ)^4 := by
  have hsum : (∑ p ∈ b.coeff.support,
      b.coeff p*(p:ℝ)*((p-1 : ℕ):ℝ)*((p-d : ℕ):ℝ)^2) ≤
      (∑ p ∈ b.coeff.support, b.coeff p)*(P:ℝ)^4 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro p hp
    have hpP : p≤P := by
      by_contra hn
      exact (Finsupp.mem_support_iff.mp hp) (b.zero_of_gt p (lt_of_not_ge hn))
    have hpR : (p:ℝ)≤P := by exact_mod_cast hpP
    have hp1R : ((p-1 : ℕ):ℝ)≤P := by exact_mod_cast (show p-1≤P by omega)
    have hpdR : ((p-d : ℕ):ℝ)≤P := by exact_mod_cast (show p-d≤P by omega)
    have hpow : ((p-d : ℕ):ℝ)^2 ≤ (P:ℝ)^2 := by
      exact sq_le_sq₀ (by positivity) (by positivity) |>.mpr hpdR
    have hproduct : (p:ℝ)*((p-1 : ℕ):ℝ)*((p-d : ℕ):ℝ)^2 ≤ (P:ℝ)^4 := by
      calc
        _ ≤ (P:ℝ)*P*P^2 := by gcongr
        _ = _ := by ring
    convert mul_le_mul_of_nonneg_left hproduct (b.nonneg p) using 1
    ring
  have htotal : (∑ p ∈ b.coeff.support, b.coeff p) ≤ 1 := b.total_le_one
  exact hsum.trans (by simpa using mul_le_mul_of_nonneg_right htotal (by positivity : 0≤(P:ℝ)^4))

/-- An explicit positive perturbation radius, uniform over all permitted
coefficient families. This sufficient bound is deliberately conservative. -/
noncomputable def epsilonBound (P : ℕ) : ℝ := 1/(1+2*(P:ℝ)^4)

theorem epsilonBound_pos : 0 < epsilonBound P := by unfold epsilonBound; positivity

/-- Every permitted sufficiently small actual perturbation satisfies the
strict curvature criterion. -/
theorem covariance_small_spreadMass (hd : 3 ≤ d) {ε : ℝ}
    (hε : 0 ≤ ε) (hsmall : ε < epsilonBound P) :
    2*spreadMass (b.covariance hd ε hε) d <
      (b.covariance hd ε hε).curvatureCoeff d*(d:ℝ)*((d:ℝ)-2) := by
  have hmass := mul_le_mul_of_nonneg_left b.coefficient_spreadMass_le hε
  rw [← b.covariance_spreadMass hd ε hε] at hmass
  have heps : ε*(1+2*(P:ℝ)^4)<1 := by
    exact (lt_div_iff₀ (by positivity)).mp hsmall
  have hdR : (3:ℝ)≤d := by exact_mod_cast hd
  have hcurv : (b.covariance hd ε hε).curvatureCoeff d = (d:ℝ)*((d:ℝ)-1) := by
    unfold FiniteMixture.curvatureCoeff
    rw [b.covariance_base_coeff, Nat.cast_sub (by omega : 1≤d)]
    norm_num
  rw [hcurv]
  have hd0 : 0 ≤ (d:ℝ) := Nat.cast_nonneg d
  have hd1 : 0 ≤ (d:ℝ)-1 := by linarith
  have hd2 : 0 ≤ (d:ℝ)-2 := by linarith
  have hbase : 1 < (d:ℝ)*((d:ℝ)-1)*(d:ℝ)*((d:ℝ)-2) := by
    have hprod : (3:ℝ)*2*3*1 ≤ (d:ℝ)*((d:ℝ)-1)*(d:ℝ)*((d:ℝ)-2) := by
      gcongr <;> first | positivity | linarith
    linarith
  nlinarith

/-- A quantitative uniform curvature theorem for actual finite even
perturbations of pure even models; the analytical proof also permits odd
degrees. No curvature or convexity conclusion is assumed. -/
theorem covariance_inverseSqrt_strictConvexOn (hd : 3 ≤ d) {ε : ℝ}
    (hε : 0 ≤ ε) (hsmall : ε < epsilonBound P) :
    StrictConvexOn ℝ (Ioc 0 1) (InverseSqrtCalculus.inverseSqrt
      (deriv (deriv (b.covariance hd ε hε).xi))) :=
  strictConvexOn_inverseSqrt_of_spreadMass _ hd
    (fun p hp => b.covariance_degrees hd ε hε hp)
    (by rw [b.covariance_base_coeff]; norm_num)
    (b.covariance_small_spreadMass hd hε hsmall)

/-- Adding a nonnegative higher-degree perturbation cannot leave the
condensed scalar range at a temperature above the pure static threshold. -/
theorem covariance_gt_staticThreshold (hd : 3 ≤ d) {ε β : ℝ} (hε : 0 ≤ ε)
    (hgt : Thresholds.staticThreshold (FiniteMixture.pure d (by omega) 1 (by norm_num)).xi < β) :
    Thresholds.staticThreshold (b.covariance hd ε hε).xi < β := by
  let pure := FiniteMixture.pure d (by omega) 1 (by norm_num)
  have hβ : 0 ≤ β := (lt_trans pure.staticThreshold_pos hgt).le
  obtain ⟨r, hr, hpos⟩ :=
    CSReplicaSymmetric.exists_firstVariation_diracZero_pos_of_gt_staticThreshold pure hβ hgt
  rw [CSReplicaSymmetric.firstVariation_diracZero pure β ⟨hr.1.le, hr.2⟩] at hpos
  have hxi : pure.xi r ≤ (b.covariance hd ε hε).xi r := by
    rw [b.covariance_xi]
    have hpure : pure.xi r = r^d := by
      simpa only [one_mul] using FiniteMixture.pure_xi d (by omega) 1 (by norm_num) r
    rw [hpure]
    have hsum : 0 ≤ ∑ p ∈ b.coeff.support, b.coeff p*r^p :=
      Finset.sum_nonneg (fun p _ => mul_nonneg (b.nonneg p) (pow_nonneg hr.1.le _))
    exact le_add_of_nonneg_right (mul_nonneg hε hsum)
  have hPhi : Thresholds.Phi pure.xi β r ≤ Thresholds.Phi (b.covariance hd ε hε).xi β r := by
    unfold Thresholds.Phi
    have hmul := mul_le_mul_of_nonneg_left hxi (sq_nonneg β)
    linarith
  by_contra hn
  have hle : β ≤ Thresholds.staticThreshold (b.covariance hd ε hε).xi := le_of_not_gt hn
  have hnonpos := ((b.covariance hd ε hε).Phi_nonpos_iff_le_staticThreshold hβ).mpr hle r hr
  exact (not_lt_of_ge hnonpos) (hpos.trans_le hPhi)

/-- The actual sufficiently small even perturbation has even supported
degrees and the unique actual minimizer is a strict one-step probability law
with a nondegenerate contact. The perturbation radius is uniform over all
allowed coefficient families and inverse temperatures above the pure static
threshold. This theorem does not claim convergence of the contact parameters. -/
theorem small_even_perturbation_strict_oneStep (hd : 4 ≤ d) (hdEven : Even d)
    {ε β : ℝ} (hε : 0 ≤ ε) (hsmall : ε < epsilonBound P)
    (hgt : Thresholds.staticThreshold (FiniteMixture.pure d (by omega) 1 (by norm_num)).xi < β) :
    (∀ p ∈ (b.covariance (by omega) ε hε).coeff.support, Even p) ∧
    ∃ x ∈ Ioo 0 1, ∃ Q ∈ Ioo 0 1,
      (canonicalMinimizer (b.covariance (by omega) ε hε) β).law = twoAtom x Q ∧
      CSStructure.potential (b.covariance (by omega) ε hε) β
        (canonicalMinimizer (b.covariance (by omega) ε hε) β).law Q = 0 ∧
      deriv (CSStructure.potential (b.covariance (by omega) ε hε) β
        (canonicalMinimizer (b.covariance (by omega) ε hε) β).law) Q = 0 ∧
      0 < deriv (deriv (CSStructure.potential (b.covariance (by omega) ε hε) β
        (canonicalMinimizer (b.covariance (by omega) ε hε) β).law)) Q ∧
      ∀ r ∈ Ioo 0 1, r ≠ Q → 0 <
        CSStructure.potential (b.covariance (by omega) ε hε) β
          (canonicalMinimizer (b.covariance (by omega) ε hε) β).law r := by
  refine ⟨fun p hp => b.covariance_even_supported (by omega) hdEven ε hε hp, ?_⟩
  apply canonicalMinimizer_strict_oneStep _ _ (b.covariance_gt_staticThreshold (by omega) hε hgt)
    (b.covariance_inverseSqrt_strictConvexOn (by omega) hε hsmall)
  exact le_trans (by omega : 3≤d)
    (b.covariance_degrees (by omega) ε hε (Finset.min'_mem _ _))

end EvenPerturbation

end SlowEquilibration.CSPerturbative

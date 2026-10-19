-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.DegreeWindow
public import SlowEquilibration.InverseSqrtCalculus
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Tactic

@[expose] public section

/-!
# Actual finite mixtures and degree-window curvature

A mixture is a finitely supported, nonzero, nonnegative coefficient sequence,
with coefficients below degree two equal to zero. Its covariance is an actual
finite polynomial. The tilted degree weights below form an actual probability
mass function, and all moment and curvature identities are derived from that
polynomial.
-/

namespace SlowEquilibration

/-- A canonical finite spin covariance, allowing either parity and zero
coefficients, with no constant or linear term. -/
structure FiniteMixture where
  coeff : ℕ →₀ ℝ
  nonneg : ∀ p, 0 ≤ coeff p
  zero_below_two : ∀ p, p < 2 → coeff p = 0
  nonzero : coeff ≠ 0

namespace FiniteMixture

variable (μ : FiniteMixture)

/-- The supported degree set is nonempty. -/
theorem support_nonempty : μ.coeff.support.Nonempty :=
  Finsupp.support_nonempty_iff.mpr μ.nonzero

/-- The smallest supported degree. -/
noncomputable def minDegree : ℕ := μ.coeff.support.min' μ.support_nonempty

/-- The largest supported degree. -/
noncomputable def maxDegree : ℕ := μ.coeff.support.max' μ.support_nonempty

/-- Every supported coefficient is strictly positive. -/
theorem coeff_pos {p : ℕ} (hp : p ∈ μ.coeff.support) : 0 < μ.coeff p :=
  lt_of_le_of_ne (μ.nonneg p) (Ne.symm (Finsupp.mem_support_iff.mp hp))

/-- Every supported degree is at least two. -/
theorem degree_ge_two {p : ℕ} (hp : p ∈ μ.coeff.support) : 2 ≤ p := by
  by_contra h
  exact (Finsupp.mem_support_iff.mp hp) (μ.zero_below_two p (by omega))

/-- Every supported degree lies between the genuine extreme degrees. -/
theorem degree_bounds {p : ℕ} (hp : p ∈ μ.coeff.support) :
    μ.minDegree ≤ p ∧ p ≤ μ.maxDegree :=
  ⟨Finset.min'_le _ _ hp, Finset.le_max' _ _ hp⟩

/-- The minimum degree obeys the model's lower degree condition. -/
theorem minDegree_ge_two : 2 ≤ μ.minDegree :=
  μ.degree_ge_two (Finset.min'_mem _ _)

/-- The covariance polynomial represented by the canonical coefficients. -/
noncomputable def xi (r : ℝ) : ℝ := ∑ p ∈ μ.coeff.support, μ.coeff p * r ^ p

/-- Its first polynomial derivative. -/
noncomputable def xi1 (r : ℝ) : ℝ :=
  ∑ p ∈ μ.coeff.support, μ.coeff p * (p : ℝ) * r ^ (p - 1)

/-- Coefficient of the shifted monomial in the second derivative. -/
noncomputable def curvatureCoeff (p : ℕ) : ℝ :=
  μ.coeff p * (p : ℝ) * ((p - 1 : ℕ) : ℝ)

/-- Its second polynomial derivative, denoted `v` in the manuscript. -/
noncomputable def xi2 (r : ℝ) : ℝ :=
  ∑ p ∈ μ.coeff.support, μ.curvatureCoeff p * r ^ (p - 2)

/-- The first derivative of the polynomial `v`. -/
noncomputable def v1 (r : ℝ) : ℝ :=
  ∑ p ∈ μ.coeff.support,
    μ.curvatureCoeff p * ((p - 2 : ℕ) : ℝ) * r ^ ((p - 2) - 1)

/-- The second derivative of the polynomial `v`. -/
noncomputable def v2 (r : ℝ) : ℝ :=
  ∑ p ∈ μ.coeff.support,
    μ.curvatureCoeff p * ((p - 2 : ℕ) : ℝ) * (((p - 2) - 1 : ℕ) : ℝ) *
      r ^ ((p - 2) - 2)

/-- Termwise differentiation of the actual covariance. -/
theorem hasDerivAt_xi (r : ℝ) : HasDerivAt μ.xi (μ.xi1 r) r := by
  unfold xi xi1
  convert HasDerivAt.fun_sum (fun p (_ : p ∈ μ.coeff.support) =>
    (hasDerivAt_pow p r).const_mul (μ.coeff p)) using 1
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Termwise differentiation of the actual first derivative. -/
theorem hasDerivAt_xi1 (r : ℝ) : HasDerivAt μ.xi1 (μ.xi2 r) r := by
  unfold xi1 xi2 curvatureCoeff
  convert HasDerivAt.fun_sum (fun p (_ : p ∈ μ.coeff.support) =>
    (hasDerivAt_pow (p - 1) r).const_mul (μ.coeff p * (p : ℝ))) using 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [show p - 1 - 1 = p - 2 by omega]
  ring

/-- The named polynomial is the genuine second derivative of the covariance. -/
theorem deriv_deriv_xi : deriv (deriv μ.xi) = μ.xi2 := by
  have h1 : deriv μ.xi = μ.xi1 := funext (fun r => (μ.hasDerivAt_xi r).deriv)
  rw [h1]
  exact funext (fun r => (μ.hasDerivAt_xi1 r).deriv)

/-- First derivative of the actual second-derivative polynomial. -/
theorem hasDerivAt_xi2 (r : ℝ) : HasDerivAt μ.xi2 (μ.v1 r) r := by
  unfold xi2 v1
  convert HasDerivAt.fun_sum (fun p (_ : p ∈ μ.coeff.support) =>
    (hasDerivAt_pow (p - 2) r).const_mul (μ.curvatureCoeff p)) using 1
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Second derivative of the actual second-derivative polynomial. -/
theorem hasDerivAt_v1 (r : ℝ) : HasDerivAt μ.v1 (μ.v2 r) r := by
  unfold v1 v2
  convert HasDerivAt.fun_sum (fun p (_ : p ∈ μ.coeff.support) =>
    (hasDerivAt_pow ((p - 2) - 1) r).const_mul
      (μ.curvatureCoeff p * ((p - 2 : ℕ) : ℝ))) using 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [show p - 2 - 1 - 1 = p - 2 - 2 by omega]
  ring

/-- Identification of the second derivative of `v` with its differentiated
polynomial, without taking any moment identity as an assumption. -/
theorem deriv_deriv_xi2 : deriv (deriv μ.xi2) = μ.v2 := by
  have h1 : deriv μ.xi2 = μ.v1 := funext (fun r => (μ.hasDerivAt_xi2 r).deriv)
  rw [h1]
  exact funext (fun r => (μ.hasDerivAt_v1 r).deriv)

/-- All supported coefficients of `v` are positive. -/
theorem curvatureCoeff_pos {p : ℕ} (hp : p ∈ μ.coeff.support) :
    0 < μ.curvatureCoeff p := by
  have hp2 := μ.degree_ge_two hp
  unfold curvatureCoeff
  apply mul_pos (mul_pos (μ.coeff_pos hp) (Nat.cast_pos.mpr (by omega)))
  exact Nat.cast_pos.mpr (by omega)

/-- The actual second derivative is strictly positive for every `r > 0`. -/
theorem xi2_pos {r : ℝ} (hr : 0 < r) : 0 < μ.xi2 r := by
  unfold xi2
  apply Finset.sum_pos
  · intro p hp
    exact mul_pos (μ.curvatureCoeff_pos hp) (pow_pos hr _)
  · exact μ.support_nonempty

/-- Unnormalized mass of supported shifted degree `p-2`. -/
noncomputable def rawWeight (r : ℝ) (p : ℕ) : ℝ :=
  μ.curvatureCoeff p * r ^ (p - 2)

/-- Tilted mass of degree `p`, whose shifted value is `p-2`. -/
noncomputable def tiltedWeight (r : ℝ) (p : ℕ) : ℝ := μ.rawWeight r p / μ.xi2 r

/-- Every tilted mass is nonnegative at a positive radius. -/
theorem tiltedWeight_nonneg {r : ℝ} (hr : 0 < r) (p : ℕ) :
    0 ≤ μ.tiltedWeight r p := by
  unfold tiltedWeight rawWeight curvatureCoeff
  apply div_nonneg
  · exact mul_nonneg (mul_nonneg (mul_nonneg (μ.nonneg p) (Nat.cast_nonneg p))
      (Nat.cast_nonneg _)) (pow_nonneg hr.le _)
  · exact (μ.xi2_pos hr).le

/-- The tilted masses sum to one on the actual supported degrees. -/
theorem tiltedWeight_sum {r : ℝ} (hr : 0 < r) :
    ∑ p ∈ μ.coeff.support, μ.tiltedWeight r p = 1 := by
  unfold tiltedWeight
  rw [← Finset.sum_div]
  change μ.xi2 r / μ.xi2 r = 1
  exact div_self (μ.xi2_pos hr).ne'

/-- Unsupported degrees have zero tilted mass. -/
theorem tiltedWeight_eq_zero {r : ℝ} {p : ℕ} (hp : p ∉ μ.coeff.support) :
    μ.tiltedWeight r p = 0 := by
  have hc : μ.coeff p = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hp
  simp [tiltedWeight, rawWeight, curvatureCoeff, hc]

/-- An actual Mathlib probability mass function of the tilted (unshifted)
degrees. Moments below evaluate the random variable `p ↦ p-2`. -/
noncomputable def tiltedDegreeLaw (r : ℝ) (hr : 0 < r) : PMF ℕ :=
  PMF.ofFinset (fun p => ENNReal.ofReal (μ.tiltedWeight r p)) μ.coeff.support
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => μ.tiltedWeight_nonneg hr p),
        μ.tiltedWeight_sum hr]
      simp)
    (by intro p hp; rw [μ.tiltedWeight_eq_zero hp]; simp)

/-- The real probability of an individual degree under the constructed law. -/
theorem tiltedDegreeLaw_toReal {r : ℝ} (hr : 0 < r) (p : ℕ) :
    (μ.tiltedDegreeLaw r hr p).toReal = μ.tiltedWeight r p := by
  exact ENNReal.toReal_ofReal (μ.tiltedWeight_nonneg hr p)

/-- The same tilted law on the finite subtype of genuinely supported degrees. -/
noncomputable def tiltedSupportedLaw (r : ℝ) (hr : 0 < r) : PMF μ.coeff.support :=
  PMF.ofFintype (fun p => ENNReal.ofReal (μ.tiltedWeight r p.val))
    (by
      rw [Finset.sum_coe_sort μ.coeff.support
        (fun p : ℕ => ENNReal.ofReal (μ.tiltedWeight r p)), ← ENNReal.ofReal_sum_of_nonneg
        (fun p _ => μ.tiltedWeight_nonneg hr p), μ.tiltedWeight_sum hr]
      simp)

/-- Integration under the actual finite probability measure equals its
weighted finite sum. -/
theorem tiltedSupportedLaw_integral {r : ℝ} (hr : 0 < r) (f : ℕ → ℝ) :
    (∫ p : μ.coeff.support, f p.val ∂(μ.tiltedSupportedLaw r hr).toMeasure) =
      ∑ p ∈ μ.coeff.support, μ.tiltedWeight r p * f p := by
  rw [PMF.integral_eq_sum]
  change (∑ p : μ.coeff.support,
    (ENNReal.ofReal (μ.tiltedWeight r p.val)).toReal • f p.val) = _
  simp only [ENNReal.toReal_ofReal (μ.tiltedWeight_nonneg hr _), smul_eq_mul]
  exact Finset.sum_coe_sort μ.coeff.support (fun p : ℕ => μ.tiltedWeight r p * f p)

/-- Mean shifted degree under the explicitly constructed finite law. -/
noncomputable def tiltedMean (r : ℝ) : ℝ :=
  ∑ p ∈ μ.coeff.support, μ.tiltedWeight r p * ((p - 2 : ℕ) : ℝ)

/-- Second moment of the shifted degree. -/
noncomputable def tiltedSecondMoment (r : ℝ) : ℝ :=
  ∑ p ∈ μ.coeff.support, μ.tiltedWeight r p * ((p - 2 : ℕ) : ℝ) ^ 2

/-- Variance of the shifted degree, defined by its finite centered-square sum. -/
noncomputable def tiltedVariance (r : ℝ) : ℝ :=
  ∑ p ∈ μ.coeff.support,
    μ.tiltedWeight r p * (((p - 2 : ℕ) : ℝ) - μ.tiltedMean r) ^ 2

private theorem euler_monomial (n : ℕ) (r : ℝ) :
    r * ((n : ℝ) * r ^ (n - 1)) = (n : ℝ) * r ^ n := by
  cases n with
  | zero => simp
  | succ n => simp [pow_succ]; ring

private theorem euler2_monomial (n : ℕ) (r : ℝ) :
    r ^ 2 * ((n : ℝ) * ((n - 1 : ℕ) : ℝ) * r ^ (n - 2)) =
      (n : ℝ) * ((n : ℝ) - 1) * r ^ n := by
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp
    | succ n => simp [pow_succ]; ring

/-- Euler identity for the genuine first derivative of `v=ξ''`. -/
theorem scaled_v1 (r : ℝ) :
    r * μ.v1 r =
      ∑ p ∈ μ.coeff.support, μ.rawWeight r p * ((p - 2 : ℕ) : ℝ) := by
  unfold v1 rawWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  calc
    _ = μ.curvatureCoeff p * (r * (((p - 2 : ℕ) : ℝ) * r ^ (p - 2 - 1))) := by ring
    _ = _ := by rw [euler_monomial]; ring

/-- Euler identity for the genuine second derivative of `v=ξ''`. -/
theorem scaled_v2 (r : ℝ) :
    r ^ 2 * μ.v2 r =
      ∑ p ∈ μ.coeff.support,
        μ.rawWeight r p * ((p - 2 : ℕ) : ℝ) * (((p - 2 : ℕ) : ℝ) - 1) := by
  unfold v2 rawWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  calc
    _ = μ.curvatureCoeff p * (r ^ 2 * (((p - 2 : ℕ) : ℝ) *
      (((p - 2) - 1 : ℕ) : ℝ) * r ^ (p - 2 - 2))) := by ring
    _ = _ := by rw [euler2_monomial]; ring

/-- First moment identity derived by differentiating the actual polynomial. -/
theorem tiltedMean_eq (r : ℝ) : μ.tiltedMean r = r * μ.v1 r / μ.xi2 r := by
  unfold tiltedMean tiltedWeight
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, ← μ.scaled_v1 r]

/-- Variance expansion for the actual tilted masses. -/
theorem tiltedVariance_eq_second_sub_sq {r : ℝ} (hr : 0 < r) :
    μ.tiltedVariance r = μ.tiltedSecondMoment r - μ.tiltedMean r ^ 2 := by
  unfold tiltedVariance
  have hexpand : ∀ p : ℕ,
      μ.tiltedWeight r p * (((p - 2 : ℕ) : ℝ) - μ.tiltedMean r) ^ 2 =
      μ.tiltedWeight r p * ((p - 2 : ℕ) : ℝ) ^ 2 -
        2 * μ.tiltedMean r * (μ.tiltedWeight r p * ((p - 2 : ℕ) : ℝ)) +
        μ.tiltedMean r ^ 2 * μ.tiltedWeight r p := by intro p; ring
  simp_rw [hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, μ.tiltedWeight_sum hr]
  change μ.tiltedSecondMoment r - 2 * μ.tiltedMean r * μ.tiltedMean r +
    μ.tiltedMean r ^ 2 * 1 = _
  ring

/-- Second moment identity, including the factorial-moment correction. -/
theorem tiltedSecondMoment_eq (r : ℝ) :
    μ.tiltedSecondMoment r = r ^ 2 * μ.v2 r / μ.xi2 r + μ.tiltedMean r := by
  have hterm : ∀ p : ℕ,
      μ.tiltedWeight r p * ((p - 2 : ℕ) : ℝ) ^ 2 =
      (μ.rawWeight r p * ((p - 2 : ℕ) : ℝ) * (((p - 2 : ℕ) : ℝ) - 1)) /
        μ.xi2 r + μ.tiltedWeight r p * ((p - 2 : ℕ) : ℝ) := by
    intro p
    unfold tiltedWeight
    ring
  unfold tiltedSecondMoment
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← μ.scaled_v2 r]
  rfl

/-- The variance is identified from the actual first two derivatives of `v`. -/
theorem tiltedVariance_eq {r : ℝ} (hr : 0 < r) :
    μ.tiltedVariance r = r ^ 2 * μ.v2 r / μ.xi2 r + μ.tiltedMean r -
      μ.tiltedMean r ^ 2 := by
  rw [μ.tiltedVariance_eq_second_sub_sq hr, μ.tiltedSecondMoment_eq]

/-- The finite-sum mean is the Bochner expectation of the shifted degree
under the actual tilted probability measure. -/
theorem tiltedMean_eq_integral {r : ℝ} (hr : 0 < r) :
    μ.tiltedMean r =
      ∫ p : μ.coeff.support, ((p.val - 2 : ℕ) : ℝ) ∂(μ.tiltedSupportedLaw r hr).toMeasure :=
  (μ.tiltedSupportedLaw_integral hr (fun p => ((p - 2 : ℕ) : ℝ))).symm

/-- The finite centered-square variance is exactly Mathlib's variance of the
shifted degree under the actual tilted probability measure. -/
theorem tiltedVariance_eq_probabilityVariance {r : ℝ} (hr : 0 < r) :
    μ.tiltedVariance r = ProbabilityTheory.variance
      (fun p : μ.coeff.support => ((p.val - 2 : ℕ) : ℝ))
      (μ.tiltedSupportedLaw r hr).toMeasure := by
  rw [ProbabilityTheory.variance_eq_integral (by fun_prop), ← μ.tiltedMean_eq_integral hr]
  exact (μ.tiltedSupportedLaw_integral hr
    (fun p => (((p - 2 : ℕ) : ℝ) - μ.tiltedMean r) ^ 2)).symm

/-- The shifted supported random variable is bounded by the actual shifted
extreme degrees; its parity is unrestricted. -/
theorem shiftedDegree_bounds {p : ℕ} (hp : p ∈ μ.coeff.support) :
    (μ.minDegree : ℝ) - 2 ≤ ((p - 2 : ℕ) : ℝ) ∧
      ((p - 2 : ℕ) : ℝ) ≤ (μ.maxDegree : ℝ) - 2 := by
  have hp2 := μ.degree_ge_two hp
  have hb := μ.degree_bounds hp
  simp only [Nat.cast_sub hp2, Nat.cast_ofNat]
  constructor
  · exact sub_le_sub_right (Nat.cast_le.mpr hb.1) 2
  · exact sub_le_sub_right (Nat.cast_le.mpr hb.2) 2

/-- Bhatia--Davis for the actual finite tilted degree law, proved by averaging
the pointwise nonnegative product over its probability masses. -/
theorem tiltedVariance_le {r : ℝ} (hr : 0 < r) :
    μ.tiltedVariance r ≤
      ((μ.maxDegree : ℝ) - 2 - μ.tiltedMean r) *
        (μ.tiltedMean r - ((μ.minDegree : ℝ) - 2)) := by
  let n : ℝ := (μ.minDegree : ℝ) - 2
  let M : ℝ := (μ.maxDegree : ℝ) - 2
  have hnonneg : 0 ≤ ∑ p ∈ μ.coeff.support,
      μ.tiltedWeight r p * (((p - 2 : ℕ) : ℝ) - n) * (M - ((p - 2 : ℕ) : ℝ)) := by
    apply Finset.sum_nonneg
    intro p hp
    have hb := μ.shiftedDegree_bounds hp
    exact mul_nonneg (mul_nonneg (μ.tiltedWeight_nonneg hr p)
      (sub_nonneg.mpr hb.1)) (sub_nonneg.mpr hb.2)
  have hexpand : ∀ p : ℕ,
      μ.tiltedWeight r p * (((p - 2 : ℕ) : ℝ) - n) * (M - ((p - 2 : ℕ) : ℝ)) =
      (M + n) * (μ.tiltedWeight r p * ((p - 2 : ℕ) : ℝ)) -
        μ.tiltedWeight r p * ((p - 2 : ℕ) : ℝ) ^ 2 -
        n * M * μ.tiltedWeight r p := by intro p; ring
  simp_rw [hexpand] at hnonneg
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, μ.tiltedWeight_sum hr] at hnonneg
  change 0 ≤ (M + n) * μ.tiltedMean r - μ.tiltedSecondMoment r - n * M * 1 at hnonneg
  rw [μ.tiltedVariance_eq_second_sub_sq hr]
  change μ.tiltedSecondMoment r - μ.tiltedMean r ^ 2 ≤
    (M - μ.tiltedMean r) * (μ.tiltedMean r - n)
  nlinarith

/-- The exact curvature identity `eq:th-curvature`, derived from the actual
polynomial and its finite tilted moments. -/
theorem curvature_identity {r : ℝ} (hr : 0 < r) :
    r ^ 2 / μ.xi2 r ^ 2 * (3 * μ.v1 r ^ 2 - 2 * μ.xi2 r * μ.v2 r) =
      μ.tiltedMean r ^ 2 + 2 * μ.tiltedMean r - 2 * μ.tiltedVariance r := by
  rw [μ.tiltedVariance_eq hr, μ.tiltedMean_eq]
  field_simp [(μ.xi2_pos hr).ne']
  ring

/-- The degree-window inequality forces the curvature numerator of the actual
second derivative to be positive at every positive radius. -/
theorem degree_window_curvature_positive {r : ℝ} (hr : 0 < r)
    (hwindow : ((μ.minDegree : ℝ) + μ.maxDegree - 5) ^ 2 <
      6 * ((μ.minDegree : ℝ) - 2) * ((μ.maxDegree : ℝ) - 2)) :
    0 < 3 * μ.v1 r ^ 2 - 2 * μ.xi2 r * μ.v2 r := by
  have hwindow' : (((μ.minDegree : ℝ) - 2) + ((μ.maxDegree : ℝ) - 2) - 1) ^ 2 <
      6 * ((μ.minDegree : ℝ) - 2) * ((μ.maxDegree : ℝ) - 2) := by
    convert hwindow using 1
    ring
  have hmoment := DegreeWindow.curvature_positive hwindow' (μ.tiltedVariance_le hr)
  have hscaled : 0 < r ^ 2 / μ.xi2 r ^ 2 *
      (3 * μ.v1 r ^ 2 - 2 * μ.xi2 r * μ.v2 r) := by
    rw [μ.curvature_identity hr]
    exact hmoment
  exact pos_of_mul_pos_right hscaled (div_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The same positivity statement expressed through genuine Lean derivatives. -/
theorem degree_window_derivative_curvature_positive {r : ℝ} (hr : 0 < r)
    (hwindow : ((μ.minDegree : ℝ) + μ.maxDegree - 5) ^ 2 <
      6 * ((μ.minDegree : ℝ) - 2) * ((μ.maxDegree : ℝ) - 2)) :
    0 < 3 * (deriv μ.xi2 r) ^ 2 - 2 * μ.xi2 r * deriv (deriv μ.xi2) r := by
  rw [(μ.hasDerivAt_xi2 r).deriv, congrFun μ.deriv_deriv_xi2 r]
  exact μ.degree_window_curvature_positive hr hwindow

/-- Twice differentiability of the actual second-derivative polynomial. -/
theorem differentiableAt_deriv_xi2 (r : ℝ) : DifferentiableAt ℝ (deriv μ.xi2) r := by
  have h1 : deriv μ.xi2 = μ.v1 := funext (fun x => (μ.hasDerivAt_xi2 x).deriv)
  rw [h1]
  exact (μ.hasDerivAt_v1 r).differentiableAt

/-- The degree-window result for the ordinary second derivative of the actual
function `(ξ'')^(-1/2)`, valid at every positive radius. -/
theorem degree_window_inverseSqrt_second_derivative_pos {r : ℝ} (hr : 0 < r)
    (hwindow : ((μ.minDegree : ℝ) + μ.maxDegree - 5) ^ 2 <
      6 * ((μ.minDegree : ℝ) - 2) * ((μ.maxDegree : ℝ) - 2)) :
    0 < deriv (deriv (InverseSqrtCalculus.inverseSqrt (deriv (deriv μ.xi)))) r := by
  rw [μ.deriv_deriv_xi]
  apply InverseSqrtCalculus.deriv2_inverseSqrt_pos (s := Set.Ioi 0) isOpen_Ioi
    (fun r hr => μ.xi2_pos hr) (fun r _ => (μ.hasDerivAt_xi2 r).differentiableAt)
    hr (μ.differentiableAt_deriv_xi2 r)
  exact μ.degree_window_derivative_curvature_positive hr hwindow

/-- The analytic conclusion of `prop:th-degree-window`: the inverse square
root of the genuine covariance second derivative is strictly convex on `(0,1]`.
This theorem does not assume a Parisi or 1RSB conclusion. -/
theorem degree_window_strictConvexOn
    (hwindow : ((μ.minDegree : ℝ) + μ.maxDegree - 5) ^ 2 <
      6 * ((μ.minDegree : ℝ) - 2) * ((μ.maxDegree : ℝ) - 2)) :
    StrictConvexOn ℝ (Set.Ioc 0 1)
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
    exact μ.degree_window_derivative_curvature_positive (interior_subset hr).1 hwindow

/-- The two advertised formulations of the degree-window condition are
equivalent for the actual extreme degrees when the minimum is at least four. -/
theorem degree_window_iff_spread_bound (hd : 4 ≤ μ.minDegree) :
    (((μ.minDegree : ℝ) + μ.maxDegree - 5) ^ 2 <
      6 * ((μ.minDegree : ℝ) - 2) * ((μ.maxDegree : ℝ) - 2)) ↔
    (μ.maxDegree : ℝ) - μ.minDegree < (μ.minDegree : ℝ) - 1 +
      Real.sqrt (3 * (μ.minDegree : ℝ) * ((μ.minDegree : ℝ) - 2)) := by
  let d : ℝ := μ.minDegree
  let P : ℝ := μ.maxDegree
  let B : ℝ := 3 * d * (d - 2)
  let x : ℝ := (P - d) - (d - 1)
  let s : ℝ := Real.sqrt B
  have hdR : 4 ≤ d := by
    change 4 ≤ (μ.minDegree : ℝ)
    exact_mod_cast hd
  have hPd : d ≤ P := by
    have hnat : μ.minDegree ≤ μ.maxDegree :=
      Finset.min'_le_max' μ.coeff.support μ.support_nonempty
    change (μ.minDegree : ℝ) ≤ (μ.maxDegree : ℝ)
    exact_mod_cast hnat
  have hBpos : 0 < B := by
    dsimp [B]
    apply mul_pos (mul_pos (by norm_num) (by linarith))
    linarith
  have hspos : 0 < s := Real.sqrt_pos.mpr hBpos
  have hsquare : s ^ 2 = B := Real.sq_sqrt hBpos.le
  have hBlarge : (d - 1) ^ 2 < B := by
    dsimp [B]
    nlinarith [mul_nonneg (show 0 ≤ d by linarith) (show 0 ≤ d - 4 by linarith)]
  have hslarge : d - 1 < s := by nlinarith
  have hxlower : -s < x := by dsimp [x]; linarith
  have hid := DegreeWindow.degree_window_margin_identity d P
  change (d + P - 5) ^ 2 < 6 * (d - 2) * (P - 2) ↔ P - d < d - 1 + s
  constructor
  · intro hwindow
    have hxsq : x ^ 2 < s ^ 2 := by dsimp [x]; nlinarith [hid]
    have hxupper : x < s := by nlinarith
    dsimp [x] at hxupper
    linarith
  · intro hspread
    have hxupper : x < s := by dsimp [x]; linarith
    have hprod : 0 < (s - x) * (s + x) :=
      mul_pos (sub_pos.mpr hxupper) (by linarith)
    have hxsq : x ^ 2 < B := by nlinarith [hsquare]
    dsimp [x] at hxsq
    nlinarith [hid]

/-- Every genuine finite mixture with all supported degrees between four and
eleven satisfies the strict convexity conclusion. -/
theorem strictConvexOn_of_supported_degrees_4_11
    (hdegrees : ∀ p ∈ μ.coeff.support, 4 ≤ p ∧ p ≤ 11) :
    StrictConvexOn ℝ (Set.Ioc 0 1)
      (InverseSqrtCalculus.inverseSqrt (deriv (deriv μ.xi))) := by
  apply μ.degree_window_strictConvexOn
  exact DegreeWindow.degree_window_4_11
    (hdegrees _ (Finset.min'_mem _ _)).1
    (Finset.min'_le_max' μ.coeff.support μ.support_nonempty)
    (hdegrees _ (Finset.max'_mem _ _)).2

/-- Every genuine finite mixture supported between six and eighteen satisfies
the strict convexity conclusion. -/
theorem strictConvexOn_of_supported_degrees_6_18
    (hdegrees : ∀ p ∈ μ.coeff.support, 6 ≤ p ∧ p ≤ 18) :
    StrictConvexOn ℝ (Set.Ioc 0 1)
      (InverseSqrtCalculus.inverseSqrt (deriv (deriv μ.xi))) := by
  apply μ.degree_window_strictConvexOn
  exact DegreeWindow.degree_window_6_18
    (hdegrees _ (Finset.min'_mem _ _)).1
    (Finset.min'_le_max' μ.coeff.support μ.support_nonempty)
    (hdegrees _ (Finset.max'_mem _ _)).2

/-- Every genuine finite mixture supported between eight and twenty-six
satisfies the strict convexity conclusion. -/
theorem strictConvexOn_of_supported_degrees_8_26
    (hdegrees : ∀ p ∈ μ.coeff.support, 8 ≤ p ∧ p ≤ 26) :
    StrictConvexOn ℝ (Set.Ioc 0 1)
      (InverseSqrtCalculus.inverseSqrt (deriv (deriv μ.xi))) := by
  apply μ.degree_window_strictConvexOn
  exact DegreeWindow.degree_window_8_26
    (hdegrees _ (Finset.min'_mem _ _)).1
    (Finset.min'_le_max' μ.coeff.support μ.support_nonempty)
    (hdegrees _ (Finset.max'_mem _ _)).2

/-- Canonical pure covariance with a strictly positive coefficient and any
allowed degree, including odd degrees and the quadratic model. -/
noncomputable def pure (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) : FiniteMixture where
  coeff := Finsupp.single p c
  nonneg := by
    intro q
    by_cases hq : q = p
    · subst q
      simpa using hc.le
    · simp [hq]
  zero_below_two := by
    intro q hq
    have hqp : q ≠ p := by omega
    simp [hqp]
  nonzero := by
    intro hzero
    have h := congrArg (fun f : ℕ →₀ ℝ => f p) hzero
    simp at h
    exact hc.ne' h

/-- The covariance of the canonical pure constructor is the actual monomial. -/
theorem pure_xi (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) (r : ℝ) :
    (pure p hp c hc).xi r = c * r ^ p := by
  simp [xi, pure, Finsupp.support_single p hc.ne']

end FiniteMixture
end SlowEquilibration

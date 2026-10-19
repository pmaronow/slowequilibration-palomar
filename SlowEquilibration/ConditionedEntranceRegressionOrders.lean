module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.ScoreCovariance
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# Exact polynomial orders of the cap-entrance regression correction

The functions below are the literal polynomials in `eq:ent-theta`. Their
coefficients are expanded from the covariance polynomial and the inverse of
the two-score covariance. All estimates hold uniformly on the closed unit
interval. These are deterministic prerequisites of `prop:ent-regression`,
not a proof of the cap-hitting theorem.
-/

namespace SlowEquilibration.ConditionedEntrance
noncomputable section
open scoped BigOperators
open Set

/-- A finite polynomial with arbitrary real coefficients and exponents. -/
def monomialSum {ι : Type*} (s : Finset ι) (b : ι → ℝ) (n : ι → ℕ)
    (r : ℝ) : ℝ := ∑ i ∈ s, b i * r ^ n i

/-- The absolute coefficient sum is a uniform constant, independent of `r`. -/
def coefficientBound {ι : Type*} (s : Finset ι) (b : ι → ℝ) : ℝ :=
  ∑ i ∈ s, |b i|

lemma coefficientBound_nonneg {ι : Type*} (s : Finset ι) (b : ι → ℝ) :
    0 ≤ coefficientBound s b := Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Lowest-degree vanishing survives arbitrary signed finite coefficients. -/
theorem monomialSum_abs_le {ι : Type*} (s : Finset ι) (b : ι → ℝ) (n : ι → ℕ)
    (d : ℕ) (hn : ∀ i ∈ s, d ≤ n i) {r : ℝ} (hr : |r| ≤ 1) :
    |monomialSum s b n r| ≤ coefficientBound s b * |r| ^ d := by
  unfold monomialSum coefficientBound
  calc
    |∑ i ∈ s, b i * r ^ n i| ≤ ∑ i ∈ s, |b i * r ^ n i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, |b i| * |r| ^ d := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (abs_nonneg r) hr (hn i hi)) (abs_nonneg _)
    _ = (∑ i ∈ s, |b i|) * |r| ^ d := (Finset.sum_mul _ _ _).symm

lemma monomialSum_hasDerivAt {ι : Type*} (s : Finset ι) (b : ι → ℝ)
    (n : ι → ℕ) (r : ℝ) :
    HasDerivAt (monomialSum s b n)
      (monomialSum s (fun i => b i * (n i : ℝ)) (fun i => n i - 1) r) r := by
  unfold monomialSum
  convert HasDerivAt.fun_sum (fun i (_ : i ∈ s) =>
    (hasDerivAt_pow (n i) r).const_mul (b i)) using 1
  apply Finset.sum_congr rfl
  intro i _
  ring

variable (μ : FiniteMixture) (Q : ℝ)

/-- The actual score covariance entry `a_Q`. -/
def aScore : ℝ := Q * μ.xi1 Q
/-- The actual score covariance entry `a_Q+b_Q`. -/
def secondScore : ℝ := Q * μ.xi1 Q + Q ^ 2 * μ.xi2 Q

/-- Coefficient of `r^p` in the first coordinate of the regression row. -/
def valueCoefficient (p : ℕ) : ℝ :=
  μ.coeff p * Real.sqrt Q ^ p *
    (secondScore μ Q - aScore μ Q * (p : ℝ)) / (μ.scoreCovariance Q).det

/-- Coefficient of `r^p` in the second coordinate of the regression row. -/
def radialCoefficient (p : ℕ) : ℝ :=
  μ.coeff p * Real.sqrt Q ^ p *
    (μ.xi Q * (p : ℝ) - aScore μ Q) / (μ.scoreCovariance Q).det

/-- Coefficient of `r^(p-1)` in the tangent-gradient regression multiplier. -/
def tangentCoefficient (p : ℕ) : ℝ :=
  μ.coeff p * (p : ℝ) * Real.sqrt Q ^ p / aScore μ Q

def valueTheta (r : ℝ) : ℝ :=
  monomialSum μ.coeff.support (valueCoefficient μ Q) id r

def radialTheta (r : ℝ) : ℝ :=
  monomialSum μ.coeff.support (radialCoefficient μ Q) id r

def tangentTheta (r : ℝ) : ℝ :=
  monomialSum μ.coeff.support (tangentCoefficient μ Q) (fun p => p - 1) r

def valueThetaDerivative (r : ℝ) : ℝ :=
  monomialSum μ.coeff.support (fun p => valueCoefficient μ Q p * (p : ℝ))
    (fun p => p - 1) r

def radialThetaDerivative (r : ℝ) : ℝ :=
  monomialSum μ.coeff.support (fun p => radialCoefficient μ Q p * (p : ℝ))
    (fun p => p - 1) r

def tangentThetaDerivative (r : ℝ) : ℝ :=
  monomialSum μ.coeff.support (fun p => tangentCoefficient μ Q p * ((p - 1 : ℕ) : ℝ))
    (fun p => p - 2) r

lemma valueTheta_hasDerivAt (r : ℝ) :
    HasDerivAt (valueTheta μ Q) (valueThetaDerivative μ Q r) r :=
  monomialSum_hasDerivAt _ _ _ _

lemma radialTheta_hasDerivAt (r : ℝ) :
    HasDerivAt (radialTheta μ Q) (radialThetaDerivative μ Q r) r :=
  monomialSum_hasDerivAt _ _ _ _

lemma tangentTheta_hasDerivAt (r : ℝ) :
    HasDerivAt (tangentTheta μ Q) (tangentThetaDerivative μ Q r) r := by
  change HasDerivAt (monomialSum μ.coeff.support (tangentCoefficient μ Q) (fun p => p - 1))
    (monomialSum μ.coeff.support (fun p => tangentCoefficient μ Q p * ((p - 1 : ℕ) : ℝ))
      (fun p => p - 2) r) r
  convert monomialSum_hasDerivAt μ.coeff.support (tangentCoefficient μ Q) (fun p => p - 1) r using 1

lemma xi_scaled_expansion (r : ℝ) :
    μ.xi (Real.sqrt Q * r) =
      ∑ p ∈ μ.coeff.support, μ.coeff p * Real.sqrt Q ^ p * r ^ p := by
  unfold FiniteMixture.xi
  apply Finset.sum_congr rfl
  intro p _
  rw [mul_pow]
  ring

lemma firstScore_scaled_expansion (r : ℝ) :
    Real.sqrt Q * r * μ.xi1 (Real.sqrt Q * r) =
      ∑ p ∈ μ.coeff.support, μ.coeff p * Real.sqrt Q ^ p * r ^ p * (p : ℝ) := by
  rw [μ.score_first_moment]
  apply Finset.sum_congr rfl
  intro p _
  rw [mul_pow]
  ring

/-- Equality to the ordinary two-by-two inverse formula, before estimating
any polynomial. Thus `valueTheta` is the literal first regression multiplier. -/
theorem valueTheta_eq (r : ℝ) :
    valueTheta μ Q r =
      (secondScore μ Q * μ.xi (Real.sqrt Q * r) -
        aScore μ Q * (Real.sqrt Q * r * μ.xi1 (Real.sqrt Q * r))) /
          (μ.scoreCovariance Q).det := by
  rw [xi_scaled_expansion, firstScore_scaled_expansion]
  unfold valueTheta monomialSum valueCoefficient
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  dsimp only [id]
  ring

/-- The second coordinate of the same literal inverse formula. -/
theorem radialTheta_eq (r : ℝ) :
    radialTheta μ Q r =
      (μ.xi Q * (Real.sqrt Q * r * μ.xi1 (Real.sqrt Q * r)) -
        aScore μ Q * μ.xi (Real.sqrt Q * r)) / (μ.scoreCovariance Q).det := by
  rw [xi_scaled_expansion, firstScore_scaled_expansion]
  unfold radialTheta monomialSum radialCoefficient
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  dsimp only [id]
  ring

/-- The coefficient row solves the literal source two-score covariance
system. Nondegeneracy comes from two distinct positive supported degrees. -/
theorem regression_score_row_correct {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (r : ℝ) :
    Matrix.vecMul ![valueTheta μ Q r, radialTheta μ Q r] (μ.scoreCovariance Q) =
      ![μ.xi (Real.sqrt Q * r), Real.sqrt Q * r * μ.xi1 (Real.sqrt Q * r)] := by
  have hdet := (μ.scoreCovariance_det_pos hQ hnp).ne'
  have hdetEq : (μ.scoreCovariance Q).det =
      μ.xi Q * secondScore μ Q - aScore μ Q ^ 2 := by
    rw [Matrix.det_fin_two]
    norm_num [FiniteMixture.scoreCovariance, secondScore, aScore]
    ring
  ext i
  fin_cases i <;>
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, FiniteMixture.scoreCovariance] <;>
    rw [valueTheta_eq, radialTheta_eq] <;>
    dsimp only [aScore, secondScore] at * <;>
    field_simp <;> rw [hdetEq] <;> ring

/-- Literal equality to `(xi(sqrt Q r), sqrt Q r xi'(sqrt Q r)) Sigma_Q⁻¹`. -/
theorem regression_score_row_inverse {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (r : ℝ) :
    ![valueTheta μ Q r, radialTheta μ Q r] =
      Matrix.vecMul ![μ.xi (Real.sqrt Q * r),
        Real.sqrt Q * r * μ.xi1 (Real.sqrt Q * r)] (μ.scoreCovariance Q)⁻¹ := by
  have hrow := regression_score_row_correct μ hQ hnp r
  have hh := congrArg (fun v => Matrix.vecMul v (μ.scoreCovariance Q)⁻¹) hrow
  rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (μ.scoreCovariance_det_pos hQ hnp).ne'), Matrix.vecMul_one] at hh
  exact hh

/-- Exact tangent-gradient multiplier from the actual center covariance. -/
theorem tangentTheta_eq (r : ℝ) :
    tangentTheta μ Q r = Real.sqrt Q * μ.xi1 (Real.sqrt Q * r) / aScore μ Q := by
  unfold tangentTheta monomialSum tangentCoefficient FiniteMixture.xi1
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  have hp1 : 1 ≤ p := (μ.degree_ge_two hp).trans' (by norm_num)
  have hs : Real.sqrt Q ^ p = Real.sqrt Q * Real.sqrt Q ^ (p - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hs, mul_pow]
  ring

/-- One deterministic constant for all three orders in the source statement. -/
def regressionOrderConstant : ℝ := 1 +
  coefficientBound μ.coeff.support (valueCoefficient μ Q) +
  coefficientBound μ.coeff.support (radialCoefficient μ Q) +
  coefficientBound μ.coeff.support (fun p => valueCoefficient μ Q p * (p : ℝ)) +
  coefficientBound μ.coeff.support (fun p => radialCoefficient μ Q p * (p : ℝ)) +
  coefficientBound μ.coeff.support (tangentCoefficient μ Q) +
  coefficientBound μ.coeff.support
    (fun p => tangentCoefficient μ Q p * ((p - 1 : ℕ) : ℝ))

lemma regressionOrderConstant_pos : 0 < regressionOrderConstant μ Q := by
  unfold regressionOrderConstant
  have h1 := coefficientBound_nonneg μ.coeff.support (valueCoefficient μ Q)
  have h2 := coefficientBound_nonneg μ.coeff.support (radialCoefficient μ Q)
  have h3 := coefficientBound_nonneg μ.coeff.support (fun p => valueCoefficient μ Q p * (p : ℝ))
  have h4 := coefficientBound_nonneg μ.coeff.support (fun p => radialCoefficient μ Q p * (p : ℝ))
  have h5 := coefficientBound_nonneg μ.coeff.support (tangentCoefficient μ Q)
  have h6 := coefficientBound_nonneg μ.coeff.support
    (fun p => tangentCoefficient μ Q p * ((p - 1 : ℕ) : ℝ))
  linarith

/-- All three source polynomial orders, with a single constant chosen before
`r` and with the genuine minimum supported degree. -/
theorem mixed_regression_orders {r : ℝ} (hr : |r| ≤ 1) :
    |valueTheta μ Q r| + |radialTheta μ Q r| ≤
      regressionOrderConstant μ Q * |r| ^ μ.minDegree ∧
    |valueThetaDerivative μ Q r| + |radialThetaDerivative μ Q r| +
      |tangentTheta μ Q r| ≤
      regressionOrderConstant μ Q * |r| ^ (μ.minDegree - 1) ∧
    |tangentThetaDerivative μ Q r| ≤
      regressionOrderConstant μ Q * |r| ^ (μ.minDegree - 2) := by
  have hd (p : ℕ) (hp : p ∈ μ.coeff.support) := (μ.degree_bounds hp).1
  have h1 := monomialSum_abs_le μ.coeff.support (valueCoefficient μ Q) id μ.minDegree hd hr
  have h2 := monomialSum_abs_le μ.coeff.support (radialCoefficient μ Q) id μ.minDegree hd hr
  have h3 := monomialSum_abs_le μ.coeff.support
    (fun p => valueCoefficient μ Q p * (p : ℝ)) (fun p => p - 1) (μ.minDegree - 1)
    (fun p hp => by have := hd p hp; omega) hr
  have h4 := monomialSum_abs_le μ.coeff.support
    (fun p => radialCoefficient μ Q p * (p : ℝ)) (fun p => p - 1) (μ.minDegree - 1)
    (fun p hp => by have := hd p hp; omega) hr
  have h5 := monomialSum_abs_le μ.coeff.support (tangentCoefficient μ Q) (fun p => p - 1)
    (μ.minDegree - 1) (fun p hp => by have := hd p hp; omega) hr
  have h6 := monomialSum_abs_le μ.coeff.support
    (fun p => tangentCoefficient μ Q p * ((p - 1 : ℕ) : ℝ)) (fun p => p - 2)
    (μ.minDegree - 2) (fun p hp => by have := hd p hp; omega) hr
  have hc1 := coefficientBound_nonneg μ.coeff.support (valueCoefficient μ Q)
  have hc2 := coefficientBound_nonneg μ.coeff.support (radialCoefficient μ Q)
  have hc3 := coefficientBound_nonneg μ.coeff.support (fun p => valueCoefficient μ Q p * (p : ℝ))
  have hc4 := coefficientBound_nonneg μ.coeff.support (fun p => radialCoefficient μ Q p * (p : ℝ))
  have hc5 := coefficientBound_nonneg μ.coeff.support (tangentCoefficient μ Q)
  have hc6 := coefficientBound_nonneg μ.coeff.support
    (fun p => tangentCoefficient μ Q p * ((p - 1 : ℕ) : ℝ))
  have hp1 := pow_nonneg (abs_nonneg r) μ.minDegree
  have hp2 := pow_nonneg (abs_nonneg r) (μ.minDegree - 1)
  have hp3 := pow_nonneg (abs_nonneg r) (μ.minDegree - 2)
  change _ at h1 h2 h3 h4 h5 h6
  dsimp only [valueTheta, radialTheta, valueThetaDerivative, radialThetaDerivative,
    tangentTheta, tangentThetaDerivative]
  unfold regressionOrderConstant
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

end
end SlowEquilibration.ConditionedEntrance

-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Tactic

@[expose] public section

/-!
# Degree-window curvature algebra

Formalizes the Bhatia--Davis and quadratic positivity steps of
`prop:th-degree-window`. This does not assert the Parisi/1RSB consequence:
constructing the tilted degree law and identifying derivatives of ξ remain
separate obligations.
-/
namespace SlowEquilibration.DegreeWindow

open MeasureTheory ProbabilityTheory

/-- Quadratic positivity used in the degree-window proof. The discriminant
condition is exactly `6 (d-2)(P-2) > (d+P-5)^2` after shifting degrees. -/
theorem quadratic_positive {n M m : ℝ}
    (hwindow : (n + M - 1)^2 < 6*n*M) :
    0 < m^2 + 2*m - 2*(m-n)*(M-m) := by
  nlinarith [sq_nonneg (3*m-(n+M-1))]

/-- If a variance obeys Bhatia--Davis, the curvature numerator is positive. -/
theorem curvature_positive {n M m variance : ℝ}
    (hwindow : (n + M - 1)^2 < 6*n*M)
    (hvariance : variance ≤ (M-m)*(m-n)) :
    0 < m^2 + 2*m - 2*variance := by
  have h := quadratic_positive (m := m) hwindow
  nlinarith

/-- The same curvature conclusion for an actual bounded random variable under
an actual Mathlib probability measure, using its Bochner expectation and variance. -/
theorem curvature_positive_of_bounded_random_variable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {n M : ℝ} (hX : AEMeasurable X μ)
    (hbound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc n M)
    (hwindow : (n + M - 1)^2 < 6*n*M) :
    0 < (∫ ω, X ω ∂μ)^2 + 2*(∫ ω, X ω ∂μ) -
      2*ProbabilityTheory.variance X μ := by
  exact curvature_positive hwindow (variance_le_sub_mul_sub hbound hX)

/-- Exact algebra relating the two forms of the degree-window margin. -/
theorem degree_window_margin_identity (d P : ℝ) :
    6*(d-2)*(P-2) - (d+P-5)^2 =
      3*d*(d-2) - ((P-d)-(d-1))^2 := by ring

/-- The three advertised extreme-degree pairs pass the strict window test. -/
theorem advertised_degree_windows :
    (6*(4-2)*(11-2) > (4+11-5)^2 : Prop) ∧
    (6*(6-2)*(18-2) > (6+18-5)^2 : Prop) ∧
    (6*(8-2)*(26-2) > (8+26-5)^2 : Prop) := by norm_num

/-- Every pair of supported degrees contained in {4,...,11} passes the test. -/
theorem degree_window_4_11 {d P : ℕ} (hd : 4 ≤ d) (hdP : d ≤ P) (hP : P ≤ 11) :
    ((d:ℝ)+P-5)^2 < 6*((d:ℝ)-2)*((P:ℝ)-2) := by
  have hdmax : d ≤ 11 := le_trans hdP hP
  have hPmin : 4 ≤ P := le_trans hd hdP
  interval_cases d <;> interval_cases P <;> norm_num at *

/-- Every pair of supported degrees contained in {6,...,18} passes the test. -/
theorem degree_window_6_18 {d P : ℕ} (hd : 6 ≤ d) (hdP : d ≤ P) (hP : P ≤ 18) :
    ((d:ℝ)+P-5)^2 < 6*((d:ℝ)-2)*((P:ℝ)-2) := by
  have hdmax : d ≤ 18 := le_trans hdP hP
  have hPmin : 6 ≤ P := le_trans hd hdP
  interval_cases d <;> interval_cases P <;> norm_num at *

/-- Every pair of supported degrees contained in {8,...,26} passes the test. -/
theorem degree_window_8_26 {d P : ℕ} (hd : 8 ≤ d) (hdP : d ≤ P) (hP : P ≤ 26) :
    ((d:ℝ)+P-5)^2 < 6*((d:ℝ)-2)*((P:ℝ)-2) := by
  have hdmax : d ≤ 26 := le_trans hdP hP
  have hPmin : 8 ≤ P := le_trans hd hdP
  interval_cases d <;> interval_cases P <;> norm_num at *

/-- The explicit counterexample's curvature numerator is negative. -/
theorem outside_window_negative_curvature :
    (11/3 : ℝ)^2 + 2*(11/3) - 2*(95/9) = -(1/3) := by norm_num

end SlowEquilibration.DegreeWindow

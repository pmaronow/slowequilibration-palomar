-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.FiniteMixtureActiveDegreeScaling

@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalActiveDegreeScaledField

open SphericalModel SphericalActiveDegreeKernel
open GaussianSpinInterpolation GaussianSpinComparison GaussianPerturbationParameter
open GaussianPerturbationSelfAveraging
open scoped Topology RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def scaleCoefficients {P : ℕ} (c : Degree P → ℝ)
    (p : Degree P) (s : ℝ) : Degree P → ℝ :=
  fun q => if q=p then c q*s^2 else c q

theorem scaleCoefficients_nonneg {P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ q, 0 ≤ c q) (p : Degree P) (s : ℝ) :
    ∀ q, 0 ≤ scaleCoefficients c p s q := by
  intro q
  simp only [scaleCoefficients]
  split_ifs
  · exact mul_nonneg (hc q) (sq_nonneg s)
  · exact hc q

theorem scaleCoefficients_feature {N P : ℕ}
    (c : Degree P → ℝ) (hc : ∀ q, 0 ≤ c q)
    (p : Degree P) (s : ℝ) (hs : 0 ≤ s)
    (x : Vector N) (i : Coordinate N P) :
    fieldFeature (scaleCoefficients c p s) x i =
      (if i.1=p then s else 1)*fieldFeature c x i := by
  unfold fieldFeature scaleCoefficients
  by_cases hi : i.1=p
  · simp only [hi, ite_true]
    rw [Real.sqrt_mul (hc p), Real.sqrt_sq_eq_abs, abs_of_nonneg hs]
    ring
  · simp only [hi, ite_false, one_mul]

theorem activeDegree_operator_coordinate {N P : ℕ}
    (p : Degree P) (s : ℝ) (g : EuclideanDisorder N P)
    (i : Coordinate N P) :
    parameterOperator (activeDegreeLabel p) s g i =
      (if i.1=p then s else 1)*g i := by
  by_cases hi : i.1=p
  · simp [parameterOperator,activeDegreeLabel,coordinateMask,diagonal_apply,hi]
  · simp [parameterOperator,activeDegreeLabel,coordinateMask,diagonal_apply,hi]

/-- Scaling a degree in the original Gaussian tensor bank is pointwise the
same field as scaling that mixture coefficient by the amplitude squared. -/
theorem activeDegree_parameterLinear_eq_scaled
    {N P : ℕ} (c : Degree P → ℝ) (hc : ∀ q, 0 ≤ c q)
    (β : ℝ) (p : Degree P) (s : ℝ) (hs : 0 ≤ s)
    (x : Vector N) (g : EuclideanDisorder N P) :
    parameterLinear (activeDegreeLinear c β) (activeDegreeLabel p) s x g =
      activeDegreeLinear (scaleCoefficients c p s) β x g := by
  unfold parameterLinear activeDegreeLinear scaledLinear
  simp only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul,
    sphereLinear,innerSL_apply_apply]
  rw [PiLp.inner_apply,PiLp.inner_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [activeDegree_operator_coordinate p s g i,
    scaleCoefficients_feature c hc p s hs x i]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

end SlowEquilibration.SphericalActiveDegreeScaledField

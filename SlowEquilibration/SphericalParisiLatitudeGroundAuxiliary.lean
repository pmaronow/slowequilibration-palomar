-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiGroundPrimalUpper
public import SlowEquilibration.SphericalCriticalLatitudeAuxiliaryLaw
public import SlowEquilibration.LatitudeGroundTrialSource

@[expose] public section

/-! The proved sharp physical one-step upper is applied to the actual
conditioned-latitude auxiliary tensor model, retaining its degree-zero
Gaussian and degree-one terms. The exact n+1 versus n normalization is
derived; neither an auxiliary maximum bound nor a latitude limit is supplied. -/

namespace SlowEquilibration.SphericalParisiLatitudeGroundAuxiliary
noncomputable section
open MeasureTheory Set Filter
open SphericalModel FiniteTensorMixtureMaximum PureTensorJetBounds
open SphericalParisiLabeledCovariance SphericalParisiGroundRSUpper
open SphericalParisiPositivePolynomialCalculus SphericalParisiGroundPrimalUpper
open SphericalCriticalLatitude SphericalParisiConditionedLatitudeCovariance LatitudeGroundTrial
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Exact derivative of the literal independently realized tau covariance. -/
theorem actual_source_auxiliary_first_eq (μ : FiniteMixture) {Q r : ℝ}
    (hQ : 0 < Q) (hr : r∈Ioo (0 : ℝ) 1) (t : ℝ) :
    xi1 (sourceAuxiliaryDegree μ Q r) (sourceAuxiliaryCoefficient μ Q r) t=
      centeredFirst μ Q r t := by
  classical
  have he : xi (sourceAuxiliaryDegree μ Q r) (sourceAuxiliaryCoefficient μ Q r)=
      (fun s => centeredCovariance μ Q r s+sourceTau μ Q r 0) := by
    funext s
    rw [show xi (sourceAuxiliaryDegree μ Q r) (sourceAuxiliaryCoefficient μ Q r) s=
      sourceTau μ Q r s from sourceAuxiliaryPolynomial_eq_tau μ hQ hr s]
    unfold centeredCovariance
    ring
  have hd := (centered_hasDerivAt μ Q r t).add_const (sourceTau μ Q r 0)
  rw [← he] at hd
  exact (xi_hasDerivAt _ _ t).unique hd

/-- The exact second derivative is the printed source centeredSecond. -/
theorem actual_source_auxiliary_second_eq (μ : FiniteMixture) {Q r : ℝ}
    (hQ : 0 < Q) (hr : r∈Ioo (0 : ℝ) 1) (t : ℝ) :
    xi2 (sourceAuxiliaryDegree μ Q r) (sourceAuxiliaryCoefficient μ Q r) t=
      centeredSecond μ Q r t := by
  classical
  have he : xi1 (sourceAuxiliaryDegree μ Q r) (sourceAuxiliaryCoefficient μ Q r)=
      centeredFirst μ Q r := funext (actual_source_auxiliary_first_eq μ hQ hr)
  have hd := centeredFirst_hasDerivAt μ Q r t
  rw [← he] at hd
  exact (xi1_hasDerivAt _ _ t).unique hd

/-- The sharp upper is for the actual iid auxiliary field with model and
coefficients fixed before dimension, including its random constant. -/
theorem eventual_actual_auxiliary_ground_upper (μ : FiniteMixture) {Q r : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (hr : r∈Ioo (0 : ℝ) 1)
    {L α s : ℝ} (hα : 0 ≤ α) (hs : s∈Icc (0 : ℝ) 1)
    (hb : 0 < L-α*(1-s)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (∫ g,actualMaximum (N := n) (sourceAuxiliaryDegree μ Q r) (sourceAuxiliaryCoefficient μ Q r) g
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate n (sourceAuxiliaryDegree μ Q r)))/(n : ℝ) ≤
        functional (centeredFirst μ Q r) (centeredSecond μ Q r) L α s+ε := by
  classical
  have H := eventual_actual_ground_functional_upper_all_degrees
    (sourceAuxiliaryDegree μ Q r) (sourceAuxiliaryCoefficient μ Q r)
    (sourceAuxiliaryCoefficient_nonneg μ hQ hnp hr) hα hs hb hε
  have hfirst := funext (actual_source_auxiliary_first_eq μ hQ hr)
  have hsecond := funext (actual_source_auxiliary_second_eq μ hQ hr)
  rw [hfirst,hsecond] at H
  exact H

theorem actual_source_functional_nonnegative (μ : FiniteMixture) {Q r : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (hr : r∈Ioo (0 : ℝ) 1)
    {L α s : ℝ} (hα : 0 ≤ α) (hs : s∈Icc (0 : ℝ) 1) (hb : 0 < L-α*(1-s)) :
    0 ≤ functional (centeredFirst μ Q r) (centeredSecond μ Q r) L α s := by
  classical
  have H := literal_functional_nonnegative (sourceAuxiliaryDegree μ Q r)
    (sourceAuxiliaryCoefficient μ Q r) (sourceAuxiliaryCoefficient_nonneg μ hQ hnp hr) hα hs hb
  rw [funext (actual_source_auxiliary_first_eq μ hQ hr),
    funext (actual_source_auxiliary_second_eq μ hQ hr)] at H
  exact H

/-- Exact physical compensation between the original n+1 sphere and its
n-dimensional tangent sphere; its factor is at most one. -/
theorem sqrt_ratio_normalization {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a/b)/a=Real.sqrt (b/a)/b := by
  rw [Real.sqrt_div ha.le,Real.sqrt_div hb.le]
  calc
    _=(Real.sqrt a/a)/Real.sqrt b := by ring
    _=(1/Real.sqrt a)/Real.sqrt b := by rw [Real.sqrt_div_self']
    _=(1/Real.sqrt b)/Real.sqrt a := by ring
    _=(Real.sqrt b/b)/Real.sqrt a := by rw [Real.sqrt_div_self']
    _=_ := by ring

def physicalAuxiliaryMaximum (μ : FiniteMixture) (Q r : ℝ) (n : ℕ)
    (g : EuclideanSpace ℝ (Coordinate n (sourceAuxiliaryDegree μ Q r))) : ℝ :=
  Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ))*
    actualMaximum (sourceAuxiliaryDegree μ Q r) (sourceAuxiliaryCoefficient μ Q r) g

/-- The literal physical n+1-conditioned auxiliary maximum has the sharp
source trial expected upper after its true sqrt((n+1)/n) scaling. -/
theorem eventual_actual_physical_auxiliary_ground_upper (μ : FiniteMixture) {Q r : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (hr : r∈Ioo (0 : ℝ) 1)
    {L α s : ℝ} (hα : 0 ≤ α) (hs : s∈Icc (0 : ℝ) 1)
    (hb : 0 < L-α*(1-s)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (∫ g,physicalAuxiliaryMaximum μ Q r n g
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate n (sourceAuxiliaryDegree μ Q r)))/
          ((n+1 : ℕ) : ℝ) ≤
        functional (centeredFirst μ Q r) (centeredSecond μ Q r) L α s+ε := by
  classical
  have H := eventual_actual_auxiliary_ground_upper μ hQ hnp hr hα hs hb hε
  have hR := actual_source_functional_nonnegative μ hQ hnp hr hα hs hb
  filter_upwards [H,eventually_gt_atTop (0 : ℕ)] with n hH hn
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hNr : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have hfactor : Real.sqrt ((n : ℝ)/((n+1 : ℕ) : ℝ)) ≤ 1 :=
    Real.sqrt_le_one.mpr ((div_le_one hNr).mpr (by exact_mod_cast Nat.le_succ n))
  have he : (∫ g,physicalAuxiliaryMaximum μ Q r n g
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate n (sourceAuxiliaryDegree μ Q r)))/
          ((n+1 : ℕ) : ℝ)=
      Real.sqrt ((n : ℝ)/((n+1 : ℕ) : ℝ))*
        ((∫ g,actualMaximum (N := n) (sourceAuxiliaryDegree μ Q r) (sourceAuxiliaryCoefficient μ Q r) g
          ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate n (sourceAuxiliaryDegree μ Q r)))/(n : ℝ)) := by
    unfold physicalAuxiliaryMaximum
    rw [integral_const_mul]
    calc
      _=(Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ))/((n+1 : ℕ) : ℝ))*
        (∫ g,actualMaximum (N := n) (sourceAuxiliaryDegree μ Q r) (sourceAuxiliaryCoefficient μ Q r) g
          ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate n (sourceAuxiliaryDegree μ Q r))) := by ring
      _=_ := by rw [sqrt_ratio_normalization hNr hnr];ring
  rw [he]
  exact (mul_le_mul_of_nonneg_left hH (Real.sqrt_nonneg _)).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor (add_nonneg hR hε.le))

end
end SlowEquilibration.SphericalParisiLatitudeGroundAuxiliary

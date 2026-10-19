-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalOnePointEnergyTilt
public import SlowEquilibration.SphericalMarkedComplexity
public import Mathlib.Analysis.Convex.Deriv

/-! Genuine radial geometry of the source mixed one-point complexity.
The semicircle contribution has nonpositive second derivative above the
spectral edge, while the literal score precision gives positive curvature. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open SphericalModel SphericalSequentialRegression Set MeasureTheory
open scoped Matrix
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

def sourceRadialCurvature (μ : FiniteMixture) (Q : ℝ) : ℝ :=
  ((μ.scoreCovariance Q)⁻¹) 1 1

def sourceRadialSlope (μ : FiniteMixture) (Q e k : ℝ) : ℝ :=
  (((μ.scoreCovariance Q)⁻¹) 0 1+((μ.scoreCovariance Q)⁻¹) 1 0)/2*e+
    sourceRadialCurvature μ Q*k

def sourceRadialProfile (μ : FiniteMixture) (Q e k : ℝ) : ℝ :=
  markedComplexity μ Q (scorePairEquiv (e,k))

theorem sourceRadialCurvature_eq (μ : FiniteMixture) (Q : ℝ) :
    sourceRadialCurvature μ Q = μ.xi Q/(μ.scoreCovariance Q).det := by
  simp only [sourceRadialCurvature,Matrix.inv_def,Ring.inverse_eq_inv,
    Matrix.adjugate_fin_two,Matrix.of_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.cons_val_one,Matrix.cons_val_fin_one]
  unfold FiniteMixture.scoreCovariance
  simp only [Fin.isValue,ite_true]
  ring

theorem sourceRadialSlope_eq (μ : FiniteMixture) (Q e k : ℝ) :
    sourceRadialSlope μ Q e k =
      (-Q*μ.xi1 Q*e+μ.xi Q*k)/(μ.scoreCovariance Q).det := by
  simp only [sourceRadialSlope,sourceRadialCurvature,Matrix.inv_def,Ring.inverse_eq_inv,
    Matrix.adjugate_fin_two,Matrix.of_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  unfold FiniteMixture.scoreCovariance
  simp only [Fin.isValue,Fin.reduceEq,ite_true,ite_false]
  ring

theorem source_scoreQuadratic_eq_slopes (μ : FiniteMixture) (Q e k : ℝ) :
    scoreQuadratic μ Q (scorePairEquiv (e,k)) =
      e*sourceEnergySlope μ Q e k+k*sourceRadialSlope μ Q e k := by
  simp only [scoreQuadratic,dotProduct,Matrix.mulVec,Fin.sum_univ_two]
  change e*(((μ.scoreCovariance Q)⁻¹) 0 0*e+((μ.scoreCovariance Q)⁻¹) 0 1*k)+
      k*(((μ.scoreCovariance Q)⁻¹) 1 0*e+((μ.scoreCovariance Q)⁻¹) 1 1*k) = _
  unfold sourceEnergySlope sourceEnergyCurvature sourceRadialSlope sourceRadialCurvature
  ring

private theorem contact_radial_slope_algebra {V a b z y : ℝ}
    (hy : y ≠ 0) (hD : V*(a+b)-a^2 ≠ 0) (hy2 : y^2=(1+z)*a) :
    (-a*((a+z*V)/y)+V*(y+b/y))/(V*(a+b)-a^2)=1/y := by
  apply (div_eq_iff hD).mpr
  field_simp [hy]
  rw [hy2]
  ring

theorem sourceRadialSlope_at_contact (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree) :
    sourceRadialSlope μ Q (TwoAtomStationarity.markE μ β x Q)
      (TwoAtomStationarity.markK μ β Q)=1/TwoAtomStationarity.markY β Q := by
  have hy := TwoAtomStationarity.markY_pos h.beta_pos h.overlap_range
  have hy2 := TwoAtomStationarity.markY_sq_from_contact μ h.beta_pos h.weight_range
    h.overlap_range h.contact_value h.contact_derivative
  have hD := (μ.scoreCovariance_det_pos h.overlap_range.1 hnp).ne'
  have hd : (μ.scoreCovariance Q).det = μ.xi Q*
      (TwoAtomStationarity.markA μ Q+TwoAtomStationarity.markB μ Q)-
        (TwoAtomStationarity.markA μ Q)^2 := by
    simp only [Matrix.det_fin_two,FiniteMixture.scoreCovariance,Fin.isValue,Fin.reduceEq,
      ite_true,ite_false,TwoAtomStationarity.markA,TwoAtomStationarity.markB]
    ring
  rw [sourceRadialSlope_eq,hd]
  rw [show -Q*μ.xi1 Q = -TwoAtomStationarity.markA μ Q by
    unfold TwoAtomStationarity.markA
    ring]
  change (-TwoAtomStationarity.markA μ Q*
      ((TwoAtomStationarity.markA μ Q+TwoAtomStationarity.markZ x Q*μ.xi Q)/
        TwoAtomStationarity.markY β Q)+μ.xi Q*
      (TwoAtomStationarity.markY β Q+TwoAtomStationarity.markB μ Q/
        TwoAtomStationarity.markY β Q)) /
      (μ.xi Q*(TwoAtomStationarity.markA μ Q+TwoAtomStationarity.markB μ Q)-
        (TwoAtomStationarity.markA μ Q)^2)=1/TwoAtomStationarity.markY β Q
  exact contact_radial_slope_algebra hy.ne' (by rwa [←hd]) hy2

theorem sourceRadialCurvature_pos (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) : 0 < sourceRadialCurvature μ Q := by
  rw [sourceRadialCurvature_eq]
  exact div_pos (μ.xi_pos hQ) (μ.scoreCovariance_det_pos hQ hnp)

theorem source_scoreQuadratic_radial_hasDerivAt (μ : FiniteMixture) (Q e k : ℝ) :
    HasDerivAt (fun v => scoreQuadratic μ Q (scorePairEquiv (e,v)))
      (2*sourceRadialSlope μ Q e k) k := by
  let A := (μ.scoreCovariance Q)⁻¹
  have h1 := (hasDerivAt_const k e).mul
    ((hasDerivAt_const k (A 0 0*e)).add ((hasDerivAt_id k).const_mul (A 0 1)))
  have h2 := (hasDerivAt_id k).mul
    ((hasDerivAt_const k (A 1 0*e)).add ((hasDerivAt_id k).const_mul (A 1 1)))
  convert h1.add h2 using 1
  · funext v
    simp only [scoreQuadratic,dotProduct,Matrix.mulVec,Fin.sum_univ_two]
    rfl
  · dsimp [sourceRadialSlope,sourceRadialCurvature,A]
    ring

theorem sourceRadialProfile_hasDerivAt (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (e k : ℝ) (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k) :
    HasDerivAt (sourceRadialProfile μ Q e)
      (-sourceRadialSlope μ Q e k+
        SemicirclePotential.resolvent (k/Real.sqrt (Q^2*μ.xi2 Q))/
          Real.sqrt (Q^2*μ.xi2 Q)) k := by
  have hb : 0 < Q^2*μ.xi2 Q := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hs : 0 < Real.sqrt (Q^2*μ.xi2 Q) := Real.sqrt_pos.mpr hb
  have hz : 2 < k/Real.sqrt (Q^2*μ.xi2 Q) := (lt_div_iff₀ hs).mpr hk
  have hquad := (source_scoreQuadratic_radial_hasDerivAt μ Q e k).div_const 2
  have hpot := (SemicirclePotential.potential_hasDerivAt hz).comp k
    ((hasDerivAt_id k).div_const (Real.sqrt (Q^2*μ.xi2 Q)))
  convert ((hasDerivAt_const k (1/2+Real.log ((Q^2*μ.xi2 Q)/(Q*μ.xi1 Q))/2)).sub hquad).add hpot using 1
  · funext v
    rfl
  · ring

private theorem resolventSquare_nonneg (z : ℝ) :
    0 ≤ SemicirclePotential.resolventSquare z := by
  unfold SemicirclePotential.resolventSquare
  apply intervalIntegral.integral_nonneg (by norm_num : (-2 : ℝ) ≤ 2)
  intro t _
  exact div_nonneg (SemicirclePotential.density_nonneg t) (sq_nonneg _)

/-- A quantitative bound for the literal semicircle second derivative,
using its genuine probability density and distance from the spectral edge. -/
theorem source_resolventSquare_le_inv_gap_sq {z : ℝ} (hz : 2 < z) :
    SemicirclePotential.resolventSquare z ≤ 1/(z-2)^2 := by
  have hgap : 0 < z-2 := sub_pos.mpr hz
  have hi : IntervalIntegrable
      (fun t => SemicirclePotential.density t/(z-t)^2) volume (-2 : ℝ) 2 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-2 : ℝ) ≤ 2)).mpr
      (SemicirclePotential.resolventSquare_integrable hz)
  have hc : IntervalIntegrable
      (fun t => SemicirclePotential.density t/(z-2)^2) volume (-2 : ℝ) 2 :=
    SemicirclePotential.density_continuous.intervalIntegrable (-2 : ℝ) 2 |>.div_const _
  unfold SemicirclePotential.resolventSquare
  calc
    _ ≤ ∫ t in (-2 : ℝ)..2, SemicirclePotential.density t/(z-2)^2 := by
      apply intervalIntegral.integral_mono_on (by norm_num : (-2 : ℝ) ≤ 2) hi hc
      intro t ht
      apply div_le_div_of_nonneg_left (SemicirclePotential.density_nonneg t)
        (sq_pos_of_pos hgap)
      nlinarith [ht.2]
    _ = _ := by
      rw [intervalIntegral.integral_div,SemicirclePotential.density_integral_interval]

/-- The actual semicircle radial contribution is concave throughout the
positive exterior spectral region, with its literal second derivative. -/
theorem source_semicircle_radial_concave {b : ℝ} (hb : 0 < b) :
    ConcaveOn ℝ (Ioi (2*Real.sqrt b)) (fun k => SemicirclePotential.potential (k/Real.sqrt b)) := by
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hs2 : (Real.sqrt b)^2=b := Real.sq_sqrt hb.le
  let f := fun k : ℝ => SemicirclePotential.potential (k/Real.sqrt b)
  let f' := fun k : ℝ => SemicirclePotential.resolvent (k/Real.sqrt b)/Real.sqrt b
  let f'' := fun k : ℝ => -SemicirclePotential.resolventSquare (k/Real.sqrt b)/b
  have hfirst (k : ℝ) (hk : k∈Ioi (2*Real.sqrt b)) : HasDerivAt f (f' k) k := by
    have hz : 2 < k/Real.sqrt b := (lt_div_iff₀ hs).mpr hk
    convert (SemicirclePotential.potential_hasDerivAt hz).comp k
      ((hasDerivAt_id k).div_const (Real.sqrt b)) using 1
    · rfl
    · dsimp [f']
      ring
  have hsecond (k : ℝ) (hk : k∈Ioi (2*Real.sqrt b)) : HasDerivAt f' (f'' k) k := by
    have hz : 2 < k/Real.sqrt b := (lt_div_iff₀ hs).mpr hk
    convert ((SemicirclePotential.resolvent_hasDerivAt hz).comp k
      ((hasDerivAt_id k).div_const (Real.sqrt b))).div_const (Real.sqrt b) using 1
    · rfl
    · dsimp [f'']
      field_simp [hs.ne',hb.ne']
      rw [hs2]
      ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ioi _)
  · intro k hk
    exact (hfirst k hk).continuousAt.continuousWithinAt
  · intro k hk
    exact (hfirst k (interior_subset hk)).hasDerivWithinAt
  · intro k hk
    exact (hsecond k (interior_subset hk)).hasDerivWithinAt
  · intro k _
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (resolventSquare_nonneg _)) hb.le

/-- The derivative of the actual mixed radial complexity. -/
def sourceRadialProfileDerivative (μ : FiniteMixture) (Q e k : ℝ) : ℝ :=
  -sourceRadialSlope μ Q e k+
    SemicirclePotential.resolvent (k/Real.sqrt (Q^2*μ.xi2 Q))/Real.sqrt (Q^2*μ.xi2 Q)

theorem sourceRadialProfileDerivative_hasDerivAt (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (e k : ℝ) (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k) :
    HasDerivAt (sourceRadialProfileDerivative μ Q e)
      (-sourceRadialCurvature μ Q-
        SemicirclePotential.resolventSquare (k/Real.sqrt (Q^2*μ.xi2 Q))/(Q^2*μ.xi2 Q)) k := by
  have hb : 0 < Q^2*μ.xi2 Q := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hs : 0 < Real.sqrt (Q^2*μ.xi2 Q) := Real.sqrt_pos.mpr hb
  have hs2 := Real.sq_sqrt hb.le
  have hz : 2 < k/Real.sqrt (Q^2*μ.xi2 Q) := (lt_div_iff₀ hs).mpr hk
  have hlin := ((hasDerivAt_const k
    ((((μ.scoreCovariance Q)⁻¹) 0 1+((μ.scoreCovariance Q)⁻¹) 1 0)/2*e)).add
      ((hasDerivAt_id k).const_mul (sourceRadialCurvature μ Q))).neg
  have hres := ((SemicirclePotential.resolvent_hasDerivAt hz).comp k
    ((hasDerivAt_id k).div_const (Real.sqrt (Q^2*μ.xi2 Q)))).div_const
      (Real.sqrt (Q^2*μ.xi2 Q))
  convert hlin.add hres using 1
  · rfl
  · simp only [zero_add,mul_one,mul_one_div,div_div,←pow_two,hs2]
    ring

/-- The source radial Hessian has a true fixed negative margin determined by
its physical score covariance; no intensity or count estimate is assumed. -/
theorem sourceRadialProfile_second_derivative_le (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (e k : ℝ) (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k) :
    deriv (sourceRadialProfileDerivative μ Q e) k ≤ -sourceRadialCurvature μ Q := by
  rw [(sourceRadialProfileDerivative_hasDerivAt μ hQ e k hk).deriv]
  exact sub_le_self _ (div_nonneg (resolventSquare_nonneg _)
    (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)).le)

/-- Both sides of the source radial Hessian are bounded at every exterior
mark by literal score curvature and the inverse square edge distance. -/
theorem sourceRadialProfile_second_derivative_ge (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (e k : ℝ) (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k) :
    -sourceRadialCurvature μ Q-1/(k-2*Real.sqrt (Q^2*μ.xi2 Q))^2 ≤
      deriv (sourceRadialProfileDerivative μ Q e) k := by
  have hb : 0 < Q^2*μ.xi2 Q := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hs : 0 < Real.sqrt (Q^2*μ.xi2 Q) := Real.sqrt_pos.mpr hb
  have hz : 2 < k/Real.sqrt (Q^2*μ.xi2 Q) := (lt_div_iff₀ hs).mpr hk
  have hbound := div_le_div_of_nonneg_right
    (source_resolventSquare_le_inv_gap_sq hz) hb.le
  have he : (1/(k/Real.sqrt (Q^2*μ.xi2 Q)-2)^2)/(Q^2*μ.xi2 Q)=
      1/(k-2*Real.sqrt (Q^2*μ.xi2 Q))^2 := by
    rw [show k/Real.sqrt (Q^2*μ.xi2 Q)-2=
      (k-2*Real.sqrt (Q^2*μ.xi2 Q))/Real.sqrt (Q^2*μ.xi2 Q) by field_simp,
      div_pow,one_div_div,div_div,Real.sq_sqrt hb.le]
    field_simp [(μ.xi2_pos hQ).ne']
  rw [he] at hbound
  rw [(sourceRadialProfileDerivative_hasDerivAt μ hQ e k hk).deriv]
  linarith
end SlowEquilibration.SphericalMarkedWindows

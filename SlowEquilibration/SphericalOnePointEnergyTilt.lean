-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalCountRectangles
public import SlowEquilibration.SphericalNegativeCriticalIntensity
public import SlowEquilibration.SphericalScoreDensityRates
public import SlowEquilibration.SphericalTAPCertificate

/-! Exact physical energy tilt at fixed radial mark. The determinant factor is
independent of energy, so this identity applies to actual critical-point and
actual local-maximum intensities without a limiting GOE prefactor assumption. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open SphericalModel SphericalSequentialRegression MeasureTheory
open scoped ENNReal Matrix
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The energy curvature of the literal inverse physical score covariance. -/
def sourceEnergyCurvature (μ : FiniteMixture) (Q : ℝ) : ℝ :=
  ((μ.scoreCovariance Q)⁻¹) 0 0

/-- Half the energy derivative of the literal score quadratic form. -/
def sourceEnergySlope (μ : FiniteMixture) (Q e k : ℝ) : ℝ :=
  sourceEnergyCurvature μ Q * e +
    (((μ.scoreCovariance Q)⁻¹) 0 1 + ((μ.scoreCovariance Q)⁻¹) 1 0)/2 * k


/-- The literal inverse covariance gives the source positive energy curvature. -/
theorem sourceEnergyCurvature_eq (μ : FiniteMixture) (Q : ℝ) :
    sourceEnergyCurvature μ Q =
      (Q*μ.xi1 Q+Q^2*μ.xi2 Q)/(μ.scoreCovariance Q).det := by
  simp only [sourceEnergyCurvature, Matrix.inv_def, Ring.inverse_eq_inv,
    Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero]
  unfold FiniteMixture.scoreCovariance
  simp only [Fin.isValue, Fin.reduceEq, ite_false]
  ring

theorem sourceEnergySlope_eq (μ : FiniteMixture) (Q e k : ℝ) :
    sourceEnergySlope μ Q e k =
      ((Q*μ.xi1 Q+Q^2*μ.xi2 Q)*e-Q*μ.xi1 Q*k)/(μ.scoreCovariance Q).det := by
  simp only [sourceEnergySlope, sourceEnergyCurvature, Matrix.inv_def, Ring.inverse_eq_inv,
    Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  unfold FiniteMixture.scoreCovariance
  simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false]
  ring

theorem sourceEnergyCurvature_pos (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) : 0 < sourceEnergyCurvature μ Q := by
  rw [sourceEnergyCurvature_eq]
  exact div_pos (add_pos (mul_pos hQ (μ.xi1_pos hQ))
    (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ))) (μ.scoreCovariance_det_pos hQ hnp)

theorem source_scoreQuadratic_energy_expansion (μ : FiniteMixture) (Q e k s : ℝ) :
    scoreQuadratic μ Q (scorePairEquiv (e+s,k)) =
      scoreQuadratic μ Q (scorePairEquiv (e,k)) +
        2*sourceEnergySlope μ Q e k*s + sourceEnergyCurvature μ Q*s^2 := by
  simp only [scoreQuadratic, scorePairEquiv_apply, dotProduct, Matrix.mulVec,
    Fin.sum_univ_two]
  change (e+s)*(((μ.scoreCovariance Q)⁻¹) 0 0*(e+s)+((μ.scoreCovariance Q)⁻¹) 0 1*k) +
      k*(((μ.scoreCovariance Q)⁻¹) 1 0*(e+s)+((μ.scoreCovariance Q)⁻¹) 1 1*k) =
    e*(((μ.scoreCovariance Q)⁻¹) 0 0*e+((μ.scoreCovariance Q)⁻¹) 0 1*k) +
      k*(((μ.scoreCovariance Q)⁻¹) 1 0*e+((μ.scoreCovariance Q)⁻¹) 1 1*k) +
      2*sourceEnergySlope μ Q e k*s + sourceEnergyCurvature μ Q*s^2
  unfold sourceEnergySlope sourceEnergyCurvature
  ring

/-- Exact finite-dimensional Gaussian tilt in physical, unnormalized energy. -/
theorem physicalScorePdf_energy_tilt (N : ℕ) (hN : 0 < N) (μ : FiniteMixture)
    (Q h k t : ℝ) :
    physicalScorePdf N μ Q (scorePairEquiv ((h+t)/(N : ℝ),k)) =
      physicalScorePdf N μ Q (scorePairEquiv (h/(N : ℝ),k)) *
        ENNReal.ofReal (Real.exp (-sourceEnergySlope μ Q (h/(N : ℝ)) k*t -
          sourceEnergyCurvature μ Q*t^2/(2*(N : ℝ)))) := by
  have hn : (N : ℝ) ≠ 0 := by positivity
  have he : (h+t)/(N : ℝ)=h/(N : ℝ)+t/(N : ℝ) := add_div _ _ _
  unfold physicalScorePdf
  rw [he,source_scoreQuadratic_energy_expansion]
  have hExponent : -(N : ℝ)/2 *
      (scoreQuadratic μ Q (scorePairEquiv (h/(N : ℝ),k)) +
        2*sourceEnergySlope μ Q (h/(N : ℝ)) k*(t/(N : ℝ)) +
        sourceEnergyCurvature μ Q*(t/(N : ℝ))^2) =
      -(N : ℝ)/2*scoreQuadratic μ Q (scorePairEquiv (h/(N : ℝ),k)) +
        (-sourceEnergySlope μ Q (h/(N : ℝ)) k*t -
          sourceEnergyCurvature μ Q*t^2/(2*(N : ℝ))) := by
    field_simp
    ring
  rw [hExponent,Real.exp_add,←mul_assoc]
  exact ENNReal.ofReal_mul (by positivity)

/-- The actual mixed critical-point intensity in physical energy coordinates. -/
def mixedEnergyRadialIntensity (n : ℕ) (μ : FiniteMixture) (Q h k : ℝ) : ℝ≥0∞ :=
  mixedCriticalIntensity n μ Q (scorePairEquiv (h/(n+2 : ℕ),k)) /
    ENNReal.ofReal (n+2 : ℕ)

/-- The actual negative-Hessian intensity in physical energy coordinates. -/
def mixedMaximumEnergyRadialIntensity (n : ℕ) (μ : FiniteMixture) (Q h k : ℝ) : ℝ≥0∞ :=
  mixedNegativeIntensity n μ Q (scorePairEquiv (h/(n+2 : ℕ),k)) /
    ENNReal.ofReal (n+2 : ℕ)

theorem mixedEnergyRadialIntensity_energy_tilt (n : ℕ) (μ : FiniteMixture)
    (Q h k t : ℝ) :
    mixedEnergyRadialIntensity n μ Q (h+t) k =
      mixedEnergyRadialIntensity n μ Q h k *
        ENNReal.ofReal (Real.exp (-sourceEnergySlope μ Q (h/(n+2 : ℕ)) k*t -
          sourceEnergyCurvature μ Q*t^2/(2*(n+2 : ℕ)))) := by
  unfold mixedEnergyRadialIntensity mixedCriticalIntensity
  rw [physicalScorePdf_energy_tilt (n+2) (by omega)]
  have hr : scorePairEquiv ((h+t)/(n+2 : ℕ),k) 1=k := rfl
  have hr' : scorePairEquiv (h/(n+2 : ℕ),k) 1=k := rfl
  rw [hr,hr']
  simp only [div_eq_mul_inv]
  ac_rfl

theorem mixedMaximumEnergyRadialIntensity_energy_tilt (n : ℕ) (μ : FiniteMixture)
    (Q h k t : ℝ) :
    mixedMaximumEnergyRadialIntensity n μ Q (h+t) k =
      mixedMaximumEnergyRadialIntensity n μ Q h k *
        ENNReal.ofReal (Real.exp (-sourceEnergySlope μ Q (h/(n+2 : ℕ)) k*t -
          sourceEnergyCurvature μ Q*t^2/(2*(n+2 : ℕ)))) := by
  unfold mixedMaximumEnergyRadialIntensity mixedNegativeIntensity
  rw [physicalScorePdf_energy_tilt (n+2) (by omega)]
  have hr : scorePairEquiv ((h+t)/(n+2 : ℕ),k) 1=k := rfl
  have hr' : scorePairEquiv (h/(n+2 : ℕ),k) 1=k := rfl
  rw [hr,hr']
  simp only [div_eq_mul_inv]
  ac_rfl

private theorem contact_slope_algebra {V a b z y : ℝ}
    (hy : y ≠ 0) (hD : V*(a+b)-a^2 ≠ 0) (hy2 : y^2=(1+z)*a) :
    ((a+b)*((a+z*V)/y)-a*(y+b/y))/(V*(a+b)-a^2)=z/y := by
  apply (div_eq_iff hD).mpr
  field_simp [hy]
  rw [hy2]
  ring

/-- The exact source microscopic energy rate βx follows from the literal
pointwise certificate, rather than a count or pressure-limit hypothesis. -/
theorem sourceEnergySlope_at_contact (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree) :
    sourceEnergySlope μ Q (TwoAtomStationarity.markE μ β x Q)
      (TwoAtomStationarity.markK μ β Q)=β*x := by
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
  rw [sourceEnergySlope_eq,hd]
  change ((TwoAtomStationarity.markA μ Q+TwoAtomStationarity.markB μ Q)*
      ((TwoAtomStationarity.markA μ Q+TwoAtomStationarity.markZ x Q*μ.xi Q)/
        TwoAtomStationarity.markY β Q)-TwoAtomStationarity.markA μ Q*
      (TwoAtomStationarity.markY β Q+TwoAtomStationarity.markB μ Q/
        TwoAtomStationarity.markY β Q)) /
      (μ.xi Q*(TwoAtomStationarity.markA μ Q+TwoAtomStationarity.markB μ Q)-
        (TwoAtomStationarity.markA μ Q)^2)=β*x
  rw [contact_slope_algebra hy.ne' (by rwa [←hd]) hy2]
  exact TwoAtomStationarity.markZ_div_markY h.beta_pos h.overlap_range
end SlowEquilibration.SphericalMarkedWindows

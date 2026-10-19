-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMarkedSchurCurvature

/-! Identification of the explicit symmetric modified precision with the
literal covariance inverse minus the source semicircle curvature matrix. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open scoped Matrix
set_option maxHeartbeats 300000

theorem sourceMarkedPrecision_eq_covariance_inverse (μ : FiniteMixture) (Q : ℝ) :
    sourceMarkedPrecision μ Q=(μ.scoreCovariance Q)⁻¹-
      Matrix.diagonal ![0,1/(2*(Q^2*μ.xi2 Q))] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [sourceMarkedPrecision,sourceEnergyCurvature,sourceEnergyRadialCross,
      sourceRadialCurvature,sourceModifiedRadialCurvature,Matrix.inv_def,Ring.inverse_eq_inv,
      Matrix.adjugate_fin_two,FiniteMixture.scoreCovariance,Matrix.diagonal]
end SlowEquilibration.SphericalMarkedWindows

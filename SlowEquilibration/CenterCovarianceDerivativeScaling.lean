-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGaussianJet

/-! Exact center-covariance derivatives at every overlap, retaining Q. -/
@[expose] public section
namespace SlowEquilibration.SphericalGaussianJet
noncomputable section
open SphericalModel

theorem firstCovariance_center_at {P : ℕ} (c : Degree P → ℝ) (Q r : ℝ) :
    firstCovariance (centerCoefficients c Q) r=Q*firstCovariance c (Q*r) := by
  classical
  unfold firstCovariance centerCoefficients
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [mul_pow]
  have hpow : Q*Q^(p.val.val-1)=Q^p.val.val := by
    rw [← pow_succ',Nat.sub_add_cancel (show 1 ≤ p.val.val by omega)]
  rw [← hpow]
  ring

theorem secondCovariance_center_at {P : ℕ} (c : Degree P → ℝ) (Q r : ℝ) :
    secondCovariance (centerCoefficients c Q) r=Q^2*secondCovariance c (Q*r) := by
  classical
  unfold secondCovariance centerCoefficients
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [mul_pow]
  have hpow : Q^2*Q^(p.val.val-2)=Q^p.val.val := by
    rw [← pow_add,Nat.add_sub_of_le p.property]
  rw [← hpow]
  ring

end
end SlowEquilibration.SphericalGaussianJet

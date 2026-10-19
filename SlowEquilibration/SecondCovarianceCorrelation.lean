-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CovarianceProfileOrders

/-! Actual signed correlation of the common Hessian blocks and the true
Gaussian rotation parameter, without an assumed bound on that correlation. -/
@[expose] public section
namespace SlowEquilibration.SphericalTwoPointCovariance
noncomputable section
open SphericalModel SphericalGaussianJet
set_option maxHeartbeats 500000

lemma abs_secondCovariance_le_one {P : ℕ} (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p)
    {r : ℝ} (hr : |r| ≤ 1) : |secondCovariance c r| ≤ secondCovariance c 1 := by
  unfold secondCovariance
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hp2 : (2:ℝ) ≤ p.val.val := by exact_mod_cast p.property
  have hp0 : 0 ≤ (p.val.val:ℝ)-1 := by linarith
  have hcoeff : 0 ≤ c p*(p.val.val:ℝ)*((p.val.val:ℝ)-1) :=
    mul_nonneg (mul_nonneg (hc p) (Nat.cast_nonneg _)) hp0
  rw [abs_mul,abs_of_nonneg hcoeff,abs_pow,one_pow,mul_one]
  exact mul_le_of_le_one_right hcoeff (pow_le_one₀ (abs_nonneg r) hr)

def hessianCorrelation {P : ℕ} (c : Degree P → ℝ) (r : ℝ) : ℝ :=
  secondCovariance c r/secondCovariance c 1

def hessianIndependentScale {P : ℕ} (c : Degree P → ℝ) (r : ℝ) : ℝ :=
  Real.sqrt (1-hessianCorrelation c r^2)

lemma hessianCorrelation_abs_le_one {P : ℕ} (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p)
    (hb : 0 < secondCovariance c 1) {r : ℝ} (hr : |r| ≤ 1) : |hessianCorrelation c r| ≤ 1 := by
  rw [hessianCorrelation,abs_div,abs_of_pos hb]
  exact (div_le_one₀ hb).mpr (abs_secondCovariance_le_one c hc hr)

/-- A genuine real Gaussian coupling is now explicitly constructed from
its actual field covariance, for negative correlations as well. -/
theorem hessianCorrelation_rotation {P : ℕ} (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p)
    (hb : 0 < secondCovariance c 1) {r : ℝ} (hr : |r| ≤ 1) :
    hessianCorrelation c r^2+hessianIndependentScale c r^2=1 := by
  have hh:=(sq_le_sq₀ (abs_nonneg _) (by norm_num : 0 ≤ (1:ℝ))).mpr (hessianCorrelation_abs_le_one c hc hb hr)
  simp only [sq_abs,one_pow] at hh
  rw [hessianIndependentScale,Real.sq_sqrt (by linarith)]
  ring

end
end SlowEquilibration.SphericalTwoPointCovariance

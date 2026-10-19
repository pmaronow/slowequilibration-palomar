-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeModel
public import SlowEquilibration.CSLatitudeTrial

@[expose] public section

/-! # Exact scalar covariance of the source transverse amplitude model -/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel
open scoped BigOperators Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The true transverse covariance after removing the shared random
constant; that constant has zero expected logarithmic pressure. -/
def amplitudeTransverseCovariance (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (r t : ℝ) : ℝ :=
  amplitudeLatitudeCovariance μ p₀ s r t-μ.xi (r^2)

private theorem binomial_latitude (p : ℕ) (r t : ℝ) :
    (∑ k : Fin (p+1), (Nat.choose p k.val:ℝ)*r^(2*(p-k.val))*(1-r^2)^k.val*t^k.val)=
      (r^2+(1-r^2)*t)^p := by
  change (∑ k : Fin (p+1), (fun k : ℕ => (Nat.choose p k:ℝ)*r^(2*(p-k))*(1-r^2)^k*t^k) k.val)=_
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (Nat.choose p k:ℝ)*r^(2*(p-k))*(1-r^2)^k*t^k) (p+1)]
  rw [show r^2+(1-r^2)*t=(1-r^2)*t+r^2 from add_comm _ _,add_pow]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_pow,pow_mul]
  ring

/-- The unperturbed independent bank has exactly the physical latitude
covariance polynomial, retaining every supported original degree. -/
theorem amplitudeLatitudeCovariance_one (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (r t : ℝ) : amplitudeLatitudeCovariance μ p₀ (fun _ => 1) r t=
      μ.xi (r^2+(1-r^2)*t) := by
  classical
  unfold amplitudeLatitudeCovariance
  simp only [bankAmplitude_one,one_pow,one_mul]
  rw [Fintype.sum_sigma,← covariancePolynomial_mixture μ]
  unfold covariancePolynomial
  apply Finset.sum_congr rfl
  intro p _
  calc
    _=(mixtureCoefficients μ p)*∑ k : Fin (p.val.val+1),
        (Nat.choose p.val.val k.val:ℝ)*r^(2*(p.val.val-k.val))*(1-r^2)^k.val*t^k.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _=_ := by rw [binomial_latitude]

/-- The actual bank model's unperturbed nonconstant covariance is the
manuscript auxiliary covariance used by the true spherical CS functional. -/
theorem amplitudeTransverseCovariance_one (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (r : ℝ) : amplitudeTransverseCovariance μ p₀ (fun _ => 1) r=μ.auxiliaryCovariance r := by
  funext t
  rw [amplitudeTransverseCovariance,amplitudeLatitudeCovariance_one]
  rfl

end
end SlowEquilibration.SphericalPlateauAmplitudeModel

-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPositivePerturbation
public import SlowEquilibration.GaussianReplicaProbe

@[expose] public section

/-! # Actual pure-degree probes of the finite positivity perturbation

The unit-degree tensor probe is constructed in the same actual Gaussian
coordinate space. Its cross Gram kernel is the exact overlap power, and its
norm/selected diagonal are derived from tensor monomials.
-/

namespace SlowEquilibration.SphericalPositivePerturbation
noncomputable section
open MeasureTheory Set
open scoped Topology BigOperators RealInnerProductSpace
open SphericalAging.FiniteModel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

def unitProbeCoefficients {K : ℕ} (p : Fin K) (j : Fin K) : ℝ := if j=p then 1 else 0

def probeLinear {N K : ℕ} (p : Fin K) : Vector N → PerturbationDisorder N K →L[ℝ] ℝ :=
  linear (unitProbeCoefficients p)

theorem probe_cross_inner {N K : ℕ} (p : Fin K) (a : Fin K → ℝ) (z y : Vector N) :
    inner ℝ (feature (unitProbeCoefficients p) z) (feature a y) =
      a p*(inner ℝ z y)^(p.val+1) := by
  classical
  rw [feature_inner]
  rw [Finset.sum_eq_single p]
  · simp [unitProbeCoefficients]
  · intro j _ hj;simp [unitProbeCoefficients,hj]
  · intro hp;exact (hp (Finset.mem_univ p)).elim

theorem probe_feature_norm {N K : ℕ} (p : Fin K) (z : Vector N) (hz : ‖z‖=1) :
    ‖feature (unitProbeCoefficients p) z‖=1 := by
  have hs : (∑ j : Fin K,(unitProbeCoefficients p j)^2)=1 := by
    classical
    simp [unitProbeCoefficients]
  have hh := feature_norm_sq (unitProbeCoefficients p) z hz
  rw [hs] at hh
  nlinarith [norm_nonneg (feature (unitProbeCoefficients p) z)]

theorem probeLinear_norm {N K : ℕ} (p : Fin K) (z : Vector N) (hz : ‖z‖=1) :
    ‖probeLinear (N := N) p z‖=1 := by
  rw [probeLinear,linear,innerSL_apply_norm]
  exact probe_feature_norm p z hz

theorem probeLinear_measurable {N K : ℕ} (p : Fin K) : Measurable (probeLinear (N := N) p) :=
  linear_measurable (unitProbeCoefficients p)

/-- The exact Gaussian coordinate cross covariance is the original
overlap-power kernel, not a supplied covariance identity. -/
theorem probe_coordinate_cross_kernel {N K : ℕ} (p : Fin K) (a : Fin K → ℝ)
    (z y : Vector N) :
    (∑ i : TensorCoordinate N K,probeLinear p z (EuclideanSpace.single i 1)*
      linear a y (EuclideanSpace.single i 1)) = a p*(inner ℝ z y)^(p.val+1) := by
  have h := probe_cross_inner p a z y
  rw [PiLp.inner_apply] at h
  simpa only [RCLike.inner_apply,conj_trivial,probeLinear,linear_coordinate,feature,mul_comm] using h

/-- With the active coefficient normalized to one before scalar
parameterization, its genuine diagonal is v²4⁻ᵖ. -/
theorem active_diagonal_of_coefficient_one {N K : ℕ} (v : ℝ) (x : Fin K → ℝ) (p : Fin K)
    (hp : x p=1) (z : Vector N) (hz : ‖z‖=1) :
    (∑ i : TensorCoordinate N K, if degreeLabel p i=true then
      (GaussianSpinComparison.coordinateObservable (linear (coefficients v x)) i z)^2 else 0) =
      v^2*(1/4 : ℝ)^(p.val+1) := by
  rw [active_diagonal _ p z hz]
  dsimp [coefficients]
  rw [hp,mul_one,mul_pow,← pow_mul,pow_mul',show (1/2 : ℝ)^2=1/4 by norm_num]

theorem active_diagonal_le_v_sq {N K : ℕ} (v : ℝ) (x : Fin K → ℝ) (p : Fin K)
    (hp : x p=1) (z : Vector N) (hz : ‖z‖=1) :
    (∑ i : TensorCoordinate N K, if degreeLabel p i=true then
      (GaussianSpinComparison.coordinateObservable (linear (coefficients v x)) i z)^2 else 0) ≤ v^2 := by
  rw [active_diagonal_of_coefficient_one v x p hp z hz]
  exact mul_le_of_le_one_right (sq_nonneg v) (pow_le_one₀ (by norm_num) (by norm_num))

end
end SlowEquilibration.SphericalPositivePerturbation

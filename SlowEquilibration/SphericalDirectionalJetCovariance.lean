-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGaussianJet

@[expose] public section

/-! Genuine directional first-jet covariances at a sphere point.  The
direction need not be radial or tangent; affine latitude radial marks are
therefore covered without replacing the physical tensor field. -/

namespace SlowEquilibration.SphericalGaussianJet
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel
open SphericalAging.HamiltonianDerivativeCovariance
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem pure_value_directional_covariance {N p : ℕ} (hN : 0 < N) (_hp : 2 ≤ p)
    (x v : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    cov[fun J : PureDisorder N p => iteratedFDeriv ℝ 0
      (SphericalAging.FiniteModel.Hamiltonian N p J) x (fun i => Fin.elim0 i),
      fun J => iteratedFDeriv ℝ 1 (SphericalAging.FiniteModel.Hamiltonian N p J) x (fun _ => v);
      PureLaw N p] = (p : ℝ)*inner ℝ x v := by
  rw [covariance_comm, covariance_eq_sub (Hamiltonian_derivative_memLp 1 x (fun _ => v))
    (Hamiltonian_derivative_memLp 0 x (fun i => Fin.elim0 i))]
  simp only [Hamiltonian_derivative_mean, zero_mul, sub_zero, Pi.mul_apply]
  rw [Hamiltonian_derivative_covariance_gram]
  simp only [coefficientDerivative, iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply]
  rw [coefficient_gradient_gram_left]
  have hn := normalization_first_power (p := p) hN (inner ℝ x x)
  rw [real_inner_self_eq_norm_sq, hx, div_self (Nat.cast_ne_zero.mpr hN.ne'), one_pow] at hn
  calc
    _ = (SphericalAging.FiniteModel.normalization N p^2 * (inner ℝ x x)^(p-1)) *
        ((p : ℝ)*inner ℝ v x) := by ring
    _ = _ := by rw [real_inner_self_eq_norm_sq, hx, hn, real_inner_comm v x]; ring

theorem pure_directional_gradient_covariance {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p)
    (x u v : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    cov[fun J : PureDisorder N p => iteratedFDeriv ℝ 1
      (SphericalAging.FiniteModel.Hamiltonian N p J) x (fun _ => u),
      fun J => iteratedFDeriv ℝ 1 (SphericalAging.FiniteModel.Hamiltonian N p J) x (fun _ => v);
      PureLaw N p] = (p : ℝ)*inner ℝ u v+
        ((p : ℝ)*((p : ℝ)-1)/(N : ℝ))*inner ℝ u x*inner ℝ x v := by
  rw [covariance_eq_sub (Hamiltonian_derivative_memLp 1 x (fun _ => u))
    (Hamiltonian_derivative_memLp 1 x (fun _ => v))]
  simp only [Hamiltonian_derivative_mean, zero_mul, sub_zero, Pi.mul_apply]
  rw [Hamiltonian_derivative_covariance_gram]
  simp only [coefficientDerivative, iteratedFDeriv_one_apply]
  rw [coefficient_gradient_cross_gram_overlap hN hp, real_inner_self_eq_norm_sq, hx,
    div_self (Nat.cast_ne_zero.mpr hN.ne')]
  simp

theorem value_directional_covariance {N P : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (x v : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    cov[jet c 0 x (fun i => Fin.elim0 i), jet c 1 x (fun _ => v); disorderLaw N P] =
      firstCovariance c 1*inner ℝ x v := by
  rw [jet_covariance c hc]
  have hpure (p : Degree P) := pure_value_directional_covariance hN p.property x v hx
  simp_rw [hpure]
  unfold firstCovariance
  simp only [one_pow, mul_one]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem directional_gradient_covariance {N P : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (x u v : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    cov[jet c 1 x (fun _ => u), jet c 1 x (fun _ => v); disorderLaw N P] =
      firstCovariance c 1*inner ℝ u v+
        (secondCovariance c 1/(N : ℝ))*inner ℝ u x*inner ℝ x v := by
  rw [jet_covariance c hc]
  have hpure (p : Degree P) := pure_directional_gradient_covariance hN p.property x u v hx
  simp_rw [hpure]
  unfold firstCovariance secondCovariance
  simp only [one_pow, mul_one]
  rw [Finset.sum_mul, Finset.sum_div, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  ring

end
end SlowEquilibration.SphericalGaussianJet

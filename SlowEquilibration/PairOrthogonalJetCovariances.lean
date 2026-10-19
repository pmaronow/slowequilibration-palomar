-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGaussianJet

/-! Actual two-point first-order jet covariances at zero overlap. -/

@[expose] public section
namespace SlowEquilibration.PairOrthogonalJetCovariances

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalGaussianJet
open SphericalAging.FiniteModel SphericalAging.HamiltonianDerivativeCovariance
open scoped BigOperators RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma pure_zero_one_covariance_at_orthogonal {N p : ℕ} (hp : 2 ≤ p)
    (x y b : SphericalModel.Vector N) (hxy : inner ℝ x y=0) :
    cov[fun J : PureDisorder N p => iteratedFDeriv ℝ 0 (Hamiltonian N p J) x (fun i => Fin.elim0 i),
      fun J => iteratedFDeriv ℝ 1 (Hamiltonian N p J) y (fun _ => b);PureLaw N p]=0 := by
  rw [covariance_comm,covariance_eq_sub (Hamiltonian_derivative_memLp 1 y (fun _ => b))
    (Hamiltonian_derivative_memLp 0 x (fun i => Fin.elim0 i))]
  simp only [Hamiltonian_derivative_mean,zero_mul,sub_zero,Pi.mul_apply]
  rw [Hamiltonian_derivative_covariance_gram]
  simp only [coefficientDerivative,iteratedFDeriv_zero_apply,iteratedFDeriv_one_apply]
  have hyx : inner ℝ y x=0 := by rw [real_inner_comm];exact hxy
  rw [coefficient_gradient_gram_left,hyx,zero_pow (by omega : p-1 ≠ 0)]
  ring

lemma pure_one_one_covariance_at_orthogonal {N p : ℕ} (hp : 3 ≤ p)
    (x y a b : SphericalModel.Vector N) (hxy : inner ℝ x y=0) :
    cov[fun J : PureDisorder N p => iteratedFDeriv ℝ 1 (Hamiltonian N p J) x (fun _ => a),
      fun J => iteratedFDeriv ℝ 1 (Hamiltonian N p J) y (fun _ => b);PureLaw N p]=0 := by
  rw [covariance_eq_sub (Hamiltonian_derivative_memLp 1 x (fun _ => a))
    (Hamiltonian_derivative_memLp 1 y (fun _ => b))]
  simp only [Hamiltonian_derivative_mean,zero_mul,sub_zero,Pi.mul_apply]
  rw [Hamiltonian_derivative_covariance_gram]
  simp only [coefficientDerivative,iteratedFDeriv_one_apply]
  rw [coefficient_gradient_cross_gram (by omega),hxy,
    zero_pow (by omega : p-1 ≠ 0),zero_pow (by omega : p-2 ≠ 0)]
  ring

/-- Every true first-order two-point jet cross covariance vanishes at zero
overlap for mixtures with no degree-two component. -/
theorem low_order_jet_covariance_zero {N P : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p)
    (hdeg : ∀ p,c p ≠ 0 → 3 ≤ p.val.val)
    (x y : SphericalModel.Vector N) (hxy : inner ℝ x y=0)
    {k l : ℕ} (hk : k ≤ 1) (hl : l ≤ 1)
    (a : Fin k → SphericalModel.Vector N) (b : Fin l → SphericalModel.Vector N) :
    cov[jet c k x a,jet c l y b;disorderLaw N P]=0 := by
  rw [jet_covariance c hc]
  apply Finset.sum_eq_zero
  intro p hp
  by_cases hcp : c p=0
  · rw [hcp,zero_mul]
  have hdegree := hdeg p hcp
  have hpure : cov[fun J : PureDisorder N p.val.val => iteratedFDeriv ℝ k (Hamiltonian N p.val.val J) x a,
      fun J => iteratedFDeriv ℝ l (Hamiltonian N p.val.val J) y b;PureLaw N p.val.val]=0 := by
    interval_cases k <;> interval_cases l
    · simp only [iteratedFDeriv_zero_apply]
      rw [Hamiltonian_probability_covariance hN,hxy,zero_pow (by omega : p.val.val ≠ 0)]
      ring
    · have ha : a=(fun i : Fin 0 => Fin.elim0 i) := funext fun i => Fin.elim0 i
      have hb : b=(fun _ => b 0) := funext fun i => by congr;exact Subsingleton.elim i 0
      rw [ha,hb]
      exact pure_zero_one_covariance_at_orthogonal (by omega) x y (b 0) hxy
    · rw [covariance_comm]
      have hb : b=(fun i : Fin 0 => Fin.elim0 i) := funext fun i => Fin.elim0 i
      have ha : a=(fun _ => a 0) := funext fun i => by congr;exact Subsingleton.elim i 0
      rw [ha,hb]
      exact pure_zero_one_covariance_at_orthogonal (by omega) y x (a 0) (by rwa [real_inner_comm])
    · have ha : a=(fun _ => a 0) := funext fun i => by congr;exact Subsingleton.elim i 0
      have hb : b=(fun _ => b 0) := funext fun i => by congr;exact Subsingleton.elim i 0
      rw [ha,hb]
      exact pure_one_one_covariance_at_orthogonal hdegree x y (a 0) (b 0) hxy
  rw [hpure,mul_zero]

lemma center_degree_support {μ : FiniteMixture} (hμ : 3 ≤ μ.minDegree) (Q : ℝ) :
    ∀ p,centerCoefficients (mixtureCoefficients μ) Q p ≠ 0 → 3 ≤ p.val.val := by
  intro p hp
  have hc : μ.coeff p.val.val ≠ 0 := by
    intro hz
    apply hp
    simp [centerCoefficients,mixtureCoefficients,hz]
  exact hμ.trans (μ.degree_bounds (Finsupp.mem_support_iff.mpr hc)).1

end
end SlowEquilibration.PairOrthogonalJetCovariances

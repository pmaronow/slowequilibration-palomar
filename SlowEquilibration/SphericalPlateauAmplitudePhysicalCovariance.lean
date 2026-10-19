-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeCovariance

@[expose] public section

/-! # Physical covariance of the actual unperturbed source amplitude bank -/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel
open scoped BigOperators Topology InnerProductSpace
set_option maxHeartbeats 1250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

/-- Exact component normalization, including degree zero. -/
theorem bankComponentKernel_eq (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (i : BankIndex μ) (u v : Vector (n+1)) :
    bankComponentKernel μ x e i u v=(n+1:ℝ)*mixtureCoefficients μ i.1*
      (Nat.choose i.1.val.val i.2.val:ℝ)*(overlap x u*overlap x v)^(i.1.val.val-i.2.val)*
      ((inner ℝ (e.toContinuousLinearMap.adjoint u) (e.toContinuousLinearMap.adjoint v))/(n+1:ℝ))^i.2.val := by
  have hN : (Real.sqrt (n+1:ℝ))^2=(n+1:ℝ) := Real.sq_sqrt (by positivity)
  have hC : (bankCoefficient μ i)^2=mixtureCoefficients μ i.1*(Nat.choose i.1.val.val i.2.val:ℝ) :=
    Real.sq_sqrt (mul_nonneg (mixtureCoefficients_nonnegative μ i.1) (Nat.cast_nonneg _))
  have hpow : (((Real.sqrt (n+1:ℝ))⁻¹)^i.2.val)^2=((n+1:ℝ)⁻¹)^i.2.val := by
    rw [← pow_mul,Nat.mul_comm i.2.val 2,pow_mul,inv_pow,hN]
  unfold bankComponentKernel bankComponentScale
  calc
    _=(Real.sqrt (n+1:ℝ))^2*(bankCoefficient μ i)^2*
      (overlap x u*overlap x v)^(i.1.val.val-i.2.val)*
      (((Real.sqrt (n+1:ℝ))⁻¹)^i.2.val)^2*
      (inner ℝ (e.toContinuousLinearMap.adjoint u) (e.toContinuousLinearMap.adjoint v))^i.2.val := by
        rw [mul_pow]
        ring
    _=_ := by
      rw [hN,hC,hpow,div_eq_mul_inv,mul_pow]
      ring

private theorem binomial_pair (p : ℕ) (a b : ℝ) :
    (∑ k : Fin (p+1), (Nat.choose p k.val:ℝ)*a^(p-k.val)*b^k.val)=(a+b)^p := by
  change (∑ k : Fin (p+1), (fun k : ℕ => (Nat.choose p k:ℝ)*a^(p-k)*b^k) k.val)=_
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (Nat.choose p k:ℝ)*a^(p-k)*b^k) (p+1)]
  rw [show a+b=b+a from add_comm _ _,add_pow]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Actual Gaussian covariance at amplitude one, before the concrete
orthonormal frame's Parseval identity is substituted. -/
theorem amplitudeField_covariance_one (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (u v : Vector (n+1)) :
    covariance (fun D : BankDisorder n μ => amplitudeField μ x e p₀ (fun _ => 1) D u)
      (fun D => amplitudeField μ x e p₀ (fun _ => 1) D v) (bankLaw n μ)=
      (n+1:ℝ)*μ.xi (overlap x u*overlap x v+
        (inner ℝ (e.toContinuousLinearMap.adjoint u) (e.toContinuousLinearMap.adjoint v))/(n+1:ℝ)) := by
  classical
  rw [amplitudeField_covariance]
  simp only [bankAmplitude_one,one_pow,one_mul,bankComponentKernel_eq]
  rw [Fintype.sum_sigma,← covariancePolynomial_mixture μ]
  unfold covariancePolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  calc
    _=(n+1:ℝ)*mixtureCoefficients μ p*∑ k : Fin (p.val.val+1),
      (Nat.choose p.val.val k.val:ℝ)*(overlap x u*overlap x v)^(p.val.val-k.val)*
        ((inner ℝ (e.toContinuousLinearMap.adjoint u) (e.toContinuousLinearMap.adjoint v))/(n+1:ℝ))^k.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _=_ := by rw [binomial_pair]; ring

/-- A complete orthonormal latitude frame recovers exactly the original
ambient polynomial covariance. The premise is a finite-dimensional
Parseval identity, not a probabilistic or thermodynamic estimate. -/
theorem amplitudeField_covariance_one_of_parseval (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (hFrame : ∀ u v : Vector (n+1), inner ℝ (e.toContinuousLinearMap.adjoint u)
      (e.toContinuousLinearMap.adjoint v)=inner ℝ u v-inner ℝ u x*inner ℝ v x/(n+1:ℝ))
    (p₀ : Degree μ.maxDegree) (u v : Vector (n+1)) :
    covariance (fun D : BankDisorder n μ => amplitudeField μ x e p₀ (fun _ => 1) D u)
      (fun D => amplitudeField μ x e p₀ (fun _ => 1) D v) (bankLaw n μ)=
      (n+1:ℝ)*μ.xi (overlap u v) := by
  rw [amplitudeField_covariance_one,hFrame]
  congr 2
  unfold overlap
  rw [real_inner_comm x u,real_inner_comm x v]
  field_simp
  simp only [Nat.cast_add,Nat.cast_one]
  ring

end
end SlowEquilibration.SphericalPlateauAmplitudeModel

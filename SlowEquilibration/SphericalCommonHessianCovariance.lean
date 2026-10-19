-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTwoPointCovariance

/-! Genuine fourth-jet covariance of the actual finite tensor field on the
common orthogonal complement. All spatial rank terms vanish by actual
orthogonality, leaving the correlated-GOE covariance with its literal 1/N. -/
@[expose] public section
namespace SlowEquilibration.SphericalTwoPointCovariance
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open SphericalAging.FiniteModel SphericalAging.HamiltonianDerivativeCovariance
open SphericalAging.HamiltonianTangentHessianCovariance
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

/-- Ordinary differentiation of the coefficient kernel. Orthogonality is
used at the evaluation point, not imposed on a replacement covariance. -/
lemma inner_product_polynomial_second {N p : ℕ} (hp : 2 ≤ p) (C : ℝ)
    (x y u v a b : SphericalModel.Vector N) (huy : inner ℝ u y=0) (hvy : inner ℝ v y=0) :
    iteratedFDeriv ℝ 2 (fun z => C*(inner ℝ x z)^(p-2)*inner ℝ u z*inner ℝ v z) y ![a,b]=
      C*(inner ℝ x y)^(p-2)*(inner ℝ u a*inner ℝ v b+inner ℝ u b*inner ℝ v a) := by
  let F:=fun z : SphericalModel.Vector N => C*(inner ℝ x z)^(p-2)
  let D:=fun z : SphericalModel.Vector N => C*((p:ℝ)-2)*(inner ℝ x z)^(p-3)*inner ℝ x b
  let ψ:=fun z : SphericalModel.Vector N => F z*inner ℝ u z*inner ℝ v z
  have hF (z) := (((innerSL ℝ x).hasFDerivAt (x:=z)).pow (p-2)).const_mul C
  have hProd (z) := (hF z |>.mul ((innerSL ℝ u).hasFDerivAt (x:=z))).mul
    ((innerSL ℝ v).hasFDerivAt (x:=z))
  have hdir : (fun z : SphericalModel.Vector N => fderiv ℝ ψ z b)=
      (fun z => D z*inner ℝ u z*inner ℝ v z+
        F z*inner ℝ u b*inner ℝ v z+F z*inner ℝ u z*inner ℝ v b) := by
    funext z
    have hP:=hProd z
    change HasFDerivAt ψ _ z at hP
    rw [hP.fderiv]
    simp only [add_apply,smul_apply,smul_eq_mul,nsmul_eq_mul,innerSL_apply_apply,Pi.mul_apply]
    rw [Nat.cast_sub hp,show p-2-1=p-3 by omega]
    norm_num only [Nat.cast_ofNat]
    dsimp only [D,F]
    ring
  have hD := ((((innerSL ℝ x).hasFDerivAt (x:=y)).pow (p-3)).const_mul (C*((p:ℝ)-2))).mul_const (inner ℝ x b)
  have hfirst:=(hD.mul ((innerSL ℝ u).hasFDerivAt (x:=y))).mul ((innerSL ℝ v).hasFDerivAt (x:=y))
  have hsecond:=((hF y).mul_const (inner ℝ u b)).mul ((innerSL ℝ v).hasFDerivAt (x:=y))
  have hthird:=((hF y).mul ((innerSL ℝ u).hasFDerivAt (x:=y))).mul_const (inner ℝ v b)
  have hder:=hfirst.add hsecond |>.add hthird
  change HasFDerivAt (fun z : SphericalModel.Vector N =>
    D z*inner ℝ u z*inner ℝ v z+F z*inner ℝ u b*inner ℝ v z+F z*inner ℝ u z*inner ℝ v b) _ y at hder
  have hFC : ContDiff ℝ 2 F := contDiff_const.mul ((innerSL ℝ x).contDiff.pow (p-2))
  have hψ : ContDiff ℝ 2 ψ := (hFC.mul (innerSL ℝ u).contDiff).mul (innerSL ℝ v).contDiff
  have hiter : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 ψ) y :=
    hψ.differentiable_iteratedFDeriv (by norm_num) y
  change iteratedFDeriv ℝ 2 ψ y ![a,b]=_
  rw [hiter.iteratedFDeriv_succ_apply_left']
  simp only [iteratedFDeriv_one_apply,Matrix.cons_val_zero,Fin.tail]
  change (fderiv ℝ (fun z => fderiv ℝ ψ z b) y) a=_
  rw [hdir,hder.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,innerSL_apply_apply,Pi.mul_apply,huy,hvy,mul_zero,zero_mul,add_zero,zero_add]
  ring

/-- Actual pure-block coefficient Gram, derived by two true derivatives. -/
lemma pure_common_hessian_covariance {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p)
    (x y u v a b : SphericalModel.Vector N) (huy : inner ℝ u y=0) (hvy : inner ℝ v y=0) :
    cov[fun J : PureDisorder N p => iteratedFDeriv ℝ 2 (Hamiltonian N p J) x ![u,v],
      fun J => iteratedFDeriv ℝ 2 (Hamiltonian N p J) y ![a,b];PureLaw N p]=
      (p:ℝ)*((p:ℝ)-1)*overlap x y^(p-2)/(N:ℝ)*
        (inner ℝ u a*inner ℝ v b+inner ℝ u b*inner ℝ v a) := by
  rw [covariance_eq_sub (Hamiltonian_derivative_memLp 2 x ![u,v])
    (Hamiltonian_derivative_memLp 2 y ![a,b])]
  simp only [Hamiltonian_derivative_mean,zero_mul,sub_zero,Pi.mul_apply]
  rw [Hamiltonian_derivative_covariance_gram]
  have htwo (I : TensorIndex N p) : coefficientDerivative 2 I x ![u,v]=bilinearCoeff I x u v := by
    simp only [coefficientDerivative,bilinearCoeff,iteratedFDeriv_two_apply,Fin.isValue,
      Matrix.cons_val_zero,Matrix.cons_val_one]
  simp_rw [htwo]
  have hcoeff : (fun z : SphericalModel.Vector N => ∑ I : TensorIndex N p,
      bilinearCoeff I x u v*SphericalAging.GaussianIntegrationByParts.hamiltonianCoefficient I z)=
      (fun z => (normalization N p^2*(p:ℝ)*((p:ℝ)-1))*(inner ℝ x z)^(p-2)*inner ℝ u z*inner ℝ v z) := by
    funext z
    exact bilinear_coefficient_gram_left hp x z u v
  rw [← linear_combination_derivative,hcoeff,
    inner_product_polynomial_second hp _ x y u v a b huy hvy]
  have hscale:=normalization_second_power hN hp (inner ℝ x y)
  unfold overlap
  linear_combination (p:ℝ)*((p:ℝ)-1)*(inner ℝ u a*inner ℝ v b+inner ℝ u b*inner ℝ v a)*hscale

/-- Literal fourth-jet covariance of the original mixed tensor disorder.
Directions u,v in the common complement remove all spatial rank terms. -/
theorem common_hessian_covariance {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y u v a b : SphericalModel.Vector N)
    (huy : inner ℝ u y=0) (hvy : inner ℝ v y=0) :
    cov[jet c 2 x ![u,v],jet c 2 y ![a,b];disorderLaw N P]=
      secondCovariance c (overlap x y)/(N:ℝ)*
        (inner ℝ u a*inner ℝ v b+inner ℝ u b*inner ℝ v a) := by
  rw [jet_covariance c hc]
  have hp (p : Degree P) := pure_common_hessian_covariance hN p.property x y u v a b huy hvy
  simp_rw [hp]
  unfold secondCovariance
  simp only [Finset.sum_mul,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  ring

end
end SlowEquilibration.SphericalTwoPointCovariance

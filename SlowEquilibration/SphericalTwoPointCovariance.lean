-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPairRegression

/-! Actual low-order two-point derivative covariances of the finite tensor
field at arbitrary overlap. These are coefficient-space Gaussian covariances,
with the literal N factors retained. -/

@[expose] public section
namespace SlowEquilibration.SphericalTwoPointCovariance

noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open scoped Topology BigOperators RealInnerProductSpace
open SphericalModel SphericalGaussianJet
open SphericalAging.FiniteModel SphericalAging.HamiltonianDerivativeCovariance
open SphericalAging.HamiltonianTangentHessianCovariance
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

lemma pure_gradient_value_covariance {N p : ℕ} (hN : 0 < N)
    (x y u : SphericalModel.Vector N) :
    cov[fun J : PureDisorder N p => iteratedFDeriv ℝ 1 (Hamiltonian N p J) x (fun _ => u),
      fun J => iteratedFDeriv ℝ 0 (Hamiltonian N p J) y (fun i => Fin.elim0 i);PureLaw N p]=
      (p:ℝ)*overlap x y^(p-1)*inner ℝ u y := by
  rw [covariance_eq_sub (Hamiltonian_derivative_memLp 1 x (fun _ => u))
    (Hamiltonian_derivative_memLp 0 y (fun i => Fin.elim0 i))]
  simp only [Hamiltonian_derivative_mean,zero_mul,sub_zero,Pi.mul_apply]
  rw [Hamiltonian_derivative_covariance_gram]
  simp only [coefficientDerivative,iteratedFDeriv_one_apply,iteratedFDeriv_zero_apply]
  rw [coefficient_gradient_gram_left]
  calc
    _=(p:ℝ)*(normalization N p^2*(inner ℝ x y)^(p-1))*inner ℝ u y := by ring
    _=_ := by rw [normalization_first_power hN];rfl

lemma pure_gradient_gradient_covariance {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p)
    (x y u v : SphericalModel.Vector N) :
    cov[fun J : PureDisorder N p => iteratedFDeriv ℝ 1 (Hamiltonian N p J) x (fun _ => u),
      fun J => iteratedFDeriv ℝ 1 (Hamiltonian N p J) y (fun _ => v);PureLaw N p]=
      (p:ℝ)*overlap x y^(p-1)*inner ℝ u v+
        (p:ℝ)*((p:ℝ)-1)*overlap x y^(p-2)/(N:ℝ)*inner ℝ u y*inner ℝ x v := by
  rw [covariance_eq_sub (Hamiltonian_derivative_memLp 1 x (fun _ => u))
    (Hamiltonian_derivative_memLp 1 y (fun _ => v))]
  simp only [Hamiltonian_derivative_mean,zero_mul,sub_zero,Pi.mul_apply]
  rw [Hamiltonian_derivative_covariance_gram]
  simp only [coefficientDerivative,iteratedFDeriv_one_apply]
  rw [coefficient_gradient_cross_gram_overlap hN hp]
  unfold overlap
  ring

lemma pure_hessian_value_covariance {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p)
    (x y u v : SphericalModel.Vector N) :
    cov[fun J : PureDisorder N p => iteratedFDeriv ℝ 2 (Hamiltonian N p J) x ![u,v],
      fun J => iteratedFDeriv ℝ 0 (Hamiltonian N p J) y (fun i => Fin.elim0 i);PureLaw N p]=
      (p:ℝ)*((p:ℝ)-1)*overlap x y^(p-2)/(N:ℝ)*inner ℝ u y*inner ℝ v y := by
  rw [covariance_eq_sub (Hamiltonian_derivative_memLp 2 x ![u,v])
    (Hamiltonian_derivative_memLp 0 y (fun i => Fin.elim0 i))]
  simp only [Hamiltonian_derivative_mean,zero_mul,sub_zero,Pi.mul_apply]
  rw [Hamiltonian_derivative_covariance_gram]
  simp only [coefficientDerivative,iteratedFDeriv_zero_apply,iteratedFDeriv_two_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Fin.isValue]
  change (∑ I : TensorIndex N p,bilinearCoeff I x u v*
    SphericalAging.GaussianIntegrationByParts.hamiltonianCoefficient I y)=_
  rw [bilinear_coefficient_gram_left hp]
  calc
    _=(p:ℝ)*((p:ℝ)-1)*(normalization N p^2*(inner ℝ x y)^(p-2))*inner ℝ u y*inner ℝ v y := by ring
    _=_ := by rw [normalization_second_power hN hp];unfold overlap;ring

/-- The actual field derivative covariance at two arbitrary points. -/
theorem gradient_value_covariance {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y u : SphericalModel.Vector N) :
    cov[jet c 1 x (fun _ => u),jet c 0 y (fun i => Fin.elim0 i);disorderLaw N P]=
      firstCovariance c (overlap x y)*inner ℝ u y := by
  rw [jet_covariance c hc]
  simp_rw [pure_gradient_value_covariance hN]
  unfold firstCovariance
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Literal trace-plus-rank-one covariance of two arbitrary directional
first derivatives, uniform in the choice of tangent coordinate frames. -/
theorem gradient_gradient_covariance {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y u v : SphericalModel.Vector N) :
    cov[jet c 1 x (fun _ => u),jet c 1 y (fun _ => v);disorderLaw N P]=
      firstCovariance c (overlap x y)*inner ℝ u v+
        secondCovariance c (overlap x y)/(N:ℝ)*inner ℝ u y*inner ℝ x v := by
  rw [jet_covariance c hc]
  have hp (p : Degree P) := pure_gradient_gradient_covariance hN p.property x y u v
  simp_rw [hp]
  unfold firstCovariance secondCovariance
  simp only [Finset.sum_mul,Finset.sum_div,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Exact covariance of an actual Hessian bilinear entry with the field
value at the second point, including its explicit 1/N factor. -/
theorem hessian_value_covariance {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y u v : SphericalModel.Vector N) :
    cov[jet c 2 x ![u,v],jet c 0 y (fun i => Fin.elim0 i);disorderLaw N P]=
      secondCovariance c (overlap x y)/(N:ℝ)*inner ℝ u y*inner ℝ v y := by
  rw [jet_covariance c hc]
  have hp (p : Degree P) := pure_hessian_value_covariance hN p.property x y u v
  simp_rw [hp]
  unfold secondCovariance
  simp only [Finset.sum_mul,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  ring

def thirdCovariance {P : ℕ} (c : Degree P → ℝ) (r : ℝ) : ℝ :=
  ∑ p : Degree P,c p*(p.val.val:ℝ)*((p.val.val:ℝ)-1)*((p.val.val:ℝ)-2)*r^(p.val.val-3)

lemma normalization_third_power {N p : ℕ} (hN : 0 < N) (hp : 3 ≤ p) (z : ℝ) :
    normalization N p^2*z^(p-3)=(z/(N:ℝ))^(p-3)/(N:ℝ)^2 := by
  have hNr : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  rw [normalization_sq N p hN,zpow_neg,zpow_natCast,div_pow]
  have hn : p-1=(p-3)+2 := by omega
  rw [hn,pow_add]
  field_simp

lemma pure_hessian_gradient_covariance {N p : ℕ} (hN : 0 < N) (hp : 3 ≤ p)
    (x y u v w : SphericalModel.Vector N) :
    cov[fun J : PureDisorder N p => iteratedFDeriv ℝ 2 (Hamiltonian N p J) x ![u,v],
      fun J => iteratedFDeriv ℝ 1 (Hamiltonian N p J) y (fun _ => w);PureLaw N p]=
      (p:ℝ)*((p:ℝ)-1)*((p:ℝ)-2)*overlap x y^(p-3)/(N:ℝ)^2*
        inner ℝ x w*inner ℝ u y*inner ℝ v y+
      (p:ℝ)*((p:ℝ)-1)*overlap x y^(p-2)/(N:ℝ)*
        (inner ℝ u w*inner ℝ v y+inner ℝ u y*inner ℝ v w) := by
  rw [covariance_eq_sub (Hamiltonian_derivative_memLp 2 x ![u,v])
    (Hamiltonian_derivative_memLp 1 y (fun _ => w))]
  simp only [Hamiltonian_derivative_mean,zero_mul,sub_zero,Pi.mul_apply]
  rw [Hamiltonian_derivative_covariance_gram]
  have htwo (I : TensorIndex N p) : coefficientDerivative 2 I x ![u,v]=bilinearCoeff I x u v := by
    simp only [coefficientDerivative,bilinearCoeff,iteratedFDeriv_two_apply,Fin.isValue,
      Matrix.cons_val_zero,Matrix.cons_val_one]
  simp_rw [htwo]
  let F := fun z : SphericalModel.Vector N => normalization N p^2*(p:ℝ)*((p:ℝ)-1)*
    (inner ℝ x z)^(p-2)
  have hcoeff : (fun z : SphericalModel.Vector N => ∑ I : TensorIndex N p,
      bilinearCoeff I x u v*SphericalAging.GaussianIntegrationByParts.hamiltonianCoefficient I z)=
      fun z => F z*inner ℝ u z*inner ℝ v z := by
    funext z
    exact bilinear_coefficient_gram_left (by omega) x z u v
  have hF := (((innerSL ℝ x).hasFDerivAt (x := y)).pow (p-2)).const_mul
    (normalization N p^2*(p:ℝ)*((p:ℝ)-1))
  have hProd := (hF.mul ((innerSL ℝ u).hasFDerivAt (x := y))).mul ((innerSL ℝ v).hasFDerivAt (x := y))
  change HasFDerivAt (fun z => F z*inner ℝ u z*inner ℝ v z) _ y at hProd
  have hd := linear_combination_derivative (fun I : TensorIndex N p => bilinearCoeff I x u v)
    1 y (fun _ => w)
  rw [hcoeff,iteratedFDeriv_one_apply,hProd.fderiv] at hd
  rw [← hd]
  simp only [add_apply,smul_apply,smul_eq_mul,nsmul_eq_mul,innerSL_apply_apply,
    Pi.mul_apply]
  rw [Nat.cast_sub (by omega : 2 ≤ p),show p-2-1=p-3 by omega]
  norm_num only [Nat.cast_ofNat]
  have h1 := normalization_third_power hN hp (inner ℝ x y)
  have h2 := normalization_second_power hN (by omega : 2 ≤ p) (inner ℝ x y)
  unfold overlap
  linear_combination
    (p:ℝ)*((p:ℝ)-1)*((p:ℝ)-2)*inner ℝ x w*inner ℝ u y*inner ℝ v y*h1+
      (p:ℝ)*((p:ℝ)-1)*(inner ℝ u w*inner ℝ v y+inner ℝ u y*inner ℝ v w)*h2

/-- The literal 1/N² and 1/N third/second profile terms in a true
Hessian/gradient cross covariance. Degree-two blocks are excluded explicitly
here, as in the source small-overlap assumption d≥4. -/
theorem hessian_gradient_covariance {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x y u v w : SphericalModel.Vector N) :
    cov[jet c 2 x ![u,v],jet c 1 y (fun _ => w);disorderLaw N P]=
      thirdCovariance c (overlap x y)/(N:ℝ)^2*inner ℝ x w*inner ℝ u y*inner ℝ v y+
      secondCovariance c (overlap x y)/(N:ℝ)*
        (inner ℝ u w*inner ℝ v y+inner ℝ u y*inner ℝ v w) := by
  rw [jet_covariance c hc]
  unfold thirdCovariance secondCovariance
  simp only [Finset.sum_mul,Finset.sum_div,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hz : c p=0
  · simp [hz]
  rw [pure_hessian_gradient_covariance hN (hdeg p hz)]
  ring

lemma overlap_comm {N : ℕ} (x y : SphericalModel.Vector N) : overlap y x=overlap x y := by
  unfold overlap
  rw [real_inner_comm]

lemma inner_eq_dimension_overlap {N : ℕ} (hN : 0 < N) (x y : SphericalModel.Vector N) :
    inner ℝ x y=(N:ℝ)*overlap x y := by
  unfold overlap
  field_simp

/-- Cross covariance of the value and the actual extensive radial mark. -/
theorem value_radial_two_point_covariance {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y : SphericalModel.Vector N) :
    cov[jet c 0 x (fun i => Fin.elim0 i),jet c 1 y (fun _ => y);disorderLaw N P]=
      (N:ℝ)*overlap x y*firstCovariance c (overlap x y) := by
  rw [covariance_comm]
  apply (gradient_value_covariance hN c hc y x y).trans
  have hρ := overlap_comm x y
  have hi : inner ℝ y x=(N:ℝ)*overlap x y :=
    (real_inner_comm x y).trans (inner_eq_dimension_overlap hN x y)
  calc
    _=firstCovariance c (overlap x y)*((N:ℝ)*overlap x y) :=
      congrArg₂ HMul.hMul (congrArg (firstCovariance c) hρ) hi
    _=_ := by ring

/-- The literal extensive radial/radial two-point covariance. -/
theorem radial_radial_two_point_covariance {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y : SphericalModel.Vector N) :
    cov[jet c 1 x (fun _ => x),jet c 1 y (fun _ => y);disorderLaw N P]=
      (N:ℝ)*(overlap x y*firstCovariance c (overlap x y)+
        overlap x y^2*secondCovariance c (overlap x y)) := by
  rw [gradient_gradient_covariance hN c hc,inner_eq_dimension_overlap hN x y]
  field_simp

/-- Tangent/directional gradient versus extensive radial score at the other point. -/
theorem gradient_radial_covariance {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y u : SphericalModel.Vector N) :
    cov[jet c 1 x (fun _ => u),jet c 1 y (fun _ => y);disorderLaw N P]=
      (firstCovariance c (overlap x y)+overlap x y*secondCovariance c (overlap x y))*inner ℝ u y := by
  rw [gradient_gradient_covariance hN c hc,inner_eq_dimension_overlap hN x y]
  field_simp

/-- Hessian bilinear entry versus extensive radial score at the other point. -/
theorem hessian_radial_covariance {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x y u v : SphericalModel.Vector N) :
    cov[jet c 2 x ![u,v],jet c 1 y (fun _ => y);disorderLaw N P]=
      (2*secondCovariance c (overlap x y)+overlap x y*thirdCovariance c (overlap x y))/(N:ℝ)*
        inner ℝ u y*inner ℝ v y := by
  rw [hessian_gradient_covariance hN c hc hdeg,inner_eq_dimension_overlap hN x y]
  field_simp
  ring

lemma vanishing_polynomial_bound {ι : Type*} [Fintype ι] (a : ι → ℝ) (e : ι → ℕ)
    (hvan : ∀ i,a i≠0 → 1 ≤ e i) {r : ℝ} (hr : |r| ≤ 1) :
    |∑ i,a i*r^(e i)| ≤ (∑ i,|a i|) * |r| := by
  calc
    _ ≤ ∑ i,|a i*r^(e i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,|a i| * |r| := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hz : a i=0
      · simp [hz]
      rw [abs_mul,abs_pow]
      have he : 1 ≤ e i := hvan i hz
      obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e i≠0)
      have hp : |r|^(e i) ≤ |r| := by
        rw [hk,pow_succ]
        exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (abs_nonneg r) hr) (abs_nonneg r)).trans_eq (one_mul _)
      exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
    _=_ := (Finset.sum_mul _ _ _).symm

def valueProfileBound {P : ℕ} (c : Degree P → ℝ) : ℝ := ∑ p : Degree P,|c p|
def firstProfileBound {P : ℕ} (c : Degree P → ℝ) : ℝ := ∑ p : Degree P,|c p*(p.val.val:ℝ)|
def secondProfileBound {P : ℕ} (c : Degree P → ℝ) : ℝ := ∑ p : Degree P,|c p*(p.val.val:ℝ)*((p.val.val:ℝ)-1)|
def thirdProfileBound {P : ℕ} (c : Degree P → ℝ) : ℝ := ∑ p : Degree P,|c p*(p.val.val:ℝ)*((p.val.val:ℝ)-1)*((p.val.val:ℝ)-2)|

/-- All four actual covariance profiles vanish at least linearly at zero,
with literal finite-coefficient constants independent of spatial dimension. -/
theorem profile_bounds {P : ℕ} (c : Degree P → ℝ)
    (hdeg : ∀ p,c p≠0 → 4 ≤ p.val.val) {r : ℝ} (hr : |r| ≤ 1) :
    |covariancePolynomial c r| ≤ valueProfileBound c * |r| ∧
    |firstCovariance c r| ≤ firstProfileBound c * |r| ∧
    |secondCovariance c r| ≤ secondProfileBound c * |r| ∧
    |thirdCovariance c r| ≤ thirdProfileBound c * |r| := by
  refine ⟨?_,?_,?_,?_⟩
  · exact vanishing_polynomial_bound c (fun p => p.val.val)
      (fun p hp => by have h:=hdeg p hp;omega) hr
  · exact vanishing_polynomial_bound (fun p => c p*(p.val.val:ℝ)) (fun p => p.val.val-1)
      (fun p hp => by
        have hcp : c p≠0 := by intro hz;simp [hz] at hp
        have h:=hdeg p hcp;omega) hr
  · exact vanishing_polynomial_bound (fun p => c p*(p.val.val:ℝ)*((p.val.val:ℝ)-1)) (fun p => p.val.val-2)
      (fun p hp => by
        have hcp : c p≠0 := by intro hz;simp [hz] at hp
        have h:=hdeg p hcp;omega) hr
  · exact vanishing_polynomial_bound (fun p => c p*(p.val.val:ℝ)*((p.val.val:ℝ)-1)*((p.val.val:ℝ)-2)) (fun p => p.val.val-3)
      (fun p hp => by
        have hcp : c p≠0 := by intro hz;simp [hz] at hp
        have h:=hdeg p hcp;omega) hr

end
end SlowEquilibration.SphericalTwoPointCovariance

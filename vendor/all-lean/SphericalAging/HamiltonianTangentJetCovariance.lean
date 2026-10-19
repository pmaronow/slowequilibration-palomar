module

public import SphericalAging.HamiltonianDerivativeCovariance
public import Mathlib.Analysis.InnerProductSpace.Calculus

public section

/-! Exact coefficient Grams of the actual first and second tangent Hamiltonian
jets. These are polynomial derivative identities, without a Gaussian matrix-law premise. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.HamiltonianTangentJetCovariance
open Set FiniteModel GaussianIntegrationByParts HamiltonianDerivativeCovariance
open scoped BigOperators InnerProductSpace
local instance {N : ℕ} : NormedAddCommGroup (Vector N→L[ℝ]ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance {N : ℕ} : NormedSpace ℝ (Vector N→L[ℝ]ℝ) := ContinuousLinearMap.toNormedSpace
local instance {N : ℕ} : NormedAddCommGroup (Vector N→L[ℝ]Vector N→L[ℝ]ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance {N : ℕ} : NormedSpace ℝ (Vector N→L[ℝ]Vector N→L[ℝ]ℝ) := ContinuousLinearMap.toNormedSpace

@[expose]  def firstCoeff {N p : ℕ} (I : TensorIndex N p) (x u : Vector N) : ℝ :=
  fderiv ℝ (hamiltonianCoefficient I) x u
@[expose]  def secondCoeff {N p : ℕ} (I : TensorIndex N p) (x u : Vector N) : ℝ :=
  fderiv ℝ (fderiv ℝ (hamiltonianCoefficient I)) x u u

 theorem kernel_second_left {N p : ℕ} (hp : 2≤p) (x y u : Vector N) :
    iteratedFDeriv ℝ 2 (fun z : Vector N => normalization N p^2*(inner ℝ z y)^p) x (fun _ => u)=
      normalization N p^2*(p:ℝ)*((p:ℝ)-1)*(inner ℝ x y)^(p-2)*(inner ℝ u y)^2 := by
  have hfd : fderiv ℝ (fun z : Vector N => normalization N p^2*(inner ℝ z y)^p)=
      fun z => (normalization N p^2*(p:ℝ)*(inner ℝ z y)^(p-1)) • innerSL ℝ y :=
    funext (fun z => (covarianceKernel_hasFDerivAt_left z y).fderiv)
  have hi : HasFDerivAt (fun z : Vector N => inner ℝ z y) (innerSL ℝ y) x := by
    convert (innerSL ℝ y).hasFDerivAt (x:=x) using 1
    funext z
    exact real_inner_comm _ _
  rw [iteratedFDeriv_two_apply,hfd,
    (((hi.pow (p-1)).const_mul (normalization N p^2*(p:ℝ))).smul_const (innerSL ℝ y)).fderiv]
  simp only [ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.mul_apply,ContinuousLinearMap.id_apply,
    innerSL_apply_apply,←Nat.cast_smul_eq_nsmul ℝ,smul_eq_mul]
  rw [show ((p-1:ℕ):ℝ)=(p:ℝ)-1 by rw [Nat.cast_sub (by omega)];norm_num,
    show p-1-1=p-2 by omega,real_inner_comm y u]
  ring

 theorem second_coefficient_gram_left {N p : ℕ} (hp : 2≤p) (x y u : Vector N) :
    (∑I : TensorIndex N p,secondCoeff I x u*hamiltonianCoefficient I y)=
      normalization N p^2*(p:ℝ)*((p:ℝ)-1)*(inner ℝ x y)^(p-2)*(inner ℝ u y)^2 := by
  have h := coefficient_derivative_gram (p:=p) 2 x y (fun _ => u)
  simp only [coefficientDerivative,iteratedFDeriv_two_apply] at h
  exact h.trans (by simpa only [iteratedFDeriv_two_apply] using kernel_second_left hp x y u)

 theorem second_derivative_square_product {N : ℕ} {f : Vector N→ℝ} (hf : ContDiff ℝ 2 f)
    (L : Vector N→L[ℝ]ℝ) (x u v : Vector N) (hx : L x=0) :
    fderiv ℝ (fderiv ℝ (fun z => f z*(L z)^2)) x u v=2*f x*L u*L v := by
  have hd (z : Vector N) : HasFDerivAt (fun z => f z*(L z)^2)
      (((L z)^2) • fderiv ℝ f z+(2*f z*L z) • L) z := by
    convert ((hf.differentiable (by norm_num) z).hasFDerivAt).mul (L.hasFDerivAt.pow 2) using 1
    ext w
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.mul_apply,smul_eq_mul,ContinuousLinearMap.id_apply]
    norm_num
    ring
  have hde : fderiv ℝ (fun z => f z*(L z)^2)=
      fun z => ((L z)^2) • fderiv ℝ f z+(2*f z*L z) • L := funext (fun z => (hd z).fderiv)
  have h2 := ((L.hasFDerivAt.pow 2).smul
      (((hf.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt)).add
    ((((hf.differentiable (by norm_num) x).hasFDerivAt.const_mul 2).mul L.hasFDerivAt).smul_const L)
  change HasFDerivAt (fun z => ((L z)^2) • fderiv ℝ f z+(2*f z*L z) • L) _ x at h2
  rw [hde,h2.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.id_apply,smul_eq_mul,hx,zero_pow (by norm_num : (2:ℕ)≠0),
    zero_mul,mul_zero,add_zero,zero_add,zero_smul]
  norm_num

 theorem second_tangent_gram {N p : ℕ} (hp : 2≤p) (x u v : Vector N)
    (hu : inner ℝ u x=0) :
    (∑I : TensorIndex N p,secondCoeff I x u*secondCoeff I x v)=
      2*normalization N p^2*(p:ℝ)*((p:ℝ)-1)*(inner ℝ x x)^(p-2)*(inner ℝ u v)^2 := by
  have he : (fun z : Vector N =>
      ∑I : TensorIndex N p,secondCoeff I x u*hamiltonianCoefficient I z)=
      fun z => (normalization N p^2*(p:ℝ)*((p:ℝ)-1)*(inner ℝ x z)^(p-2))*(inner ℝ u z)^2 := by
    funext z
    exact second_coefficient_gram_left hp x z u
  have hh := linear_combination_derivative (fun I : TensorIndex N p => secondCoeff I x u)
    2 x (fun _ => v)
  rw [he,iteratedFDeriv_two_apply] at hh
  have hf : ContDiff ℝ 2 (fun z : Vector N => normalization N p^2*(p:ℝ)*((p:ℝ)-1)*(inner ℝ x z)^(p-2)) := by
    have hi : ContDiff ℝ 2 (fun z : Vector N => inner ℝ x z) := by
      exact contDiff_const.inner ℝ contDiff_id
    exact contDiff_const.mul (hi.pow (p-2))
  have hh2 := second_derivative_square_product hf (innerSL ℝ u) x v v
    (by simpa only [innerSL_apply_apply] using hu)
  simp only [innerSL_apply_apply] at hh2
  rw [hh2] at hh
  simp only [coefficientDerivative,iteratedFDeriv_two_apply,innerSL_apply_apply] at hh
  exact hh.symm.trans (by ring)

end SphericalAging.HamiltonianTangentJetCovariance

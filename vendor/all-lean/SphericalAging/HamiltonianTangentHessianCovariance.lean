module

public import SphericalAging.HamiltonianTangentJetCovariance
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

public section

/-! Exact bilinear covariance of the genuine tangent Hamiltonian Hessian.
The covariance of the actual ordered Gaussian derivatives is derived from
the polynomial kernel, including its GOE normalization. -/

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace SphericalAging.HamiltonianTangentHessianCovariance
open Set MeasureTheory ProbabilityTheory FiniteModel GaussianIntegrationByParts
open HamiltonianDerivativeCovariance HamiltonianTangentJetCovariance
open scoped BigOperators InnerProductSpace
local instance {N : ℕ} : NormedAddCommGroup (Vector N →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance {N : ℕ} : NormedSpace ℝ (Vector N →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance {N : ℕ} : NormedAddCommGroup (Vector N →L[ℝ] Vector N →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance {N : ℕ} : NormedSpace ℝ (Vector N →L[ℝ] Vector N →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
variable {N p : ℕ}

@[expose] def bilinearCoeff (I : TensorIndex N p) (x u v : Vector N) : ℝ :=
  fderiv ℝ (fderiv ℝ (hamiltonianCoefficient I)) x u v

theorem bilinearCoeff_symm (I : TensorIndex N p) (x u v : Vector N) :
    bilinearCoeff I x u v = bilinearCoeff I x v u :=
  ((coefficient_contDiff I).contDiffAt.isSymmSndFDerivAt (by simp)) u v

theorem bilinearCoeff_polarization (I : TensorIndex N p) (x u v : Vector N) :
    secondCoeff I x (u+v) =
      secondCoeff I x u + 2*bilinearCoeff I x u v + secondCoeff I x v := by
  simp only [secondCoeff, bilinearCoeff, map_add, ContinuousLinearMap.add_apply]
  rw [show fderiv ℝ (fderiv ℝ (hamiltonianCoefficient I)) x v u =
      fderiv ℝ (fderiv ℝ (hamiltonianCoefficient I)) x u v from
        bilinearCoeff_symm I x v u]
  ring

theorem bilinear_coefficient_gram_left (hp : 2 ≤ p) (x y u v : Vector N) :
    (∑ I : TensorIndex N p, bilinearCoeff I x u v * hamiltonianCoefficient I y) =
      normalization N p^2 * (p:ℝ) * ((p:ℝ)-1) *
        (inner ℝ x y)^(p-2) * inner ℝ u y * inner ℝ v y := by
  have he : (∑ I : TensorIndex N p, bilinearCoeff I x u v * hamiltonianCoefficient I y) =
      ((∑ I : TensorIndex N p, secondCoeff I x (u+v) * hamiltonianCoefficient I y) -
        (∑ I : TensorIndex N p, secondCoeff I x u * hamiltonianCoefficient I y) -
        (∑ I : TensorIndex N p, secondCoeff I x v * hamiltonianCoefficient I y))/2 := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro I _
    rw [bilinearCoeff_polarization]
    ring
  rw [he, second_coefficient_gram_left hp, second_coefficient_gram_left hp,
    second_coefficient_gram_left hp, inner_add_left]
  ring

theorem second_derivative_product_vanish {f : Vector N → ℝ} (hf : ContDiff ℝ 2 f)
    (L M : Vector N →L[ℝ] ℝ) (x w z : Vector N) (hL : L x = 0) (hM : M x = 0) :
    fderiv ℝ (fderiv ℝ (fun y => f y * L y * M y)) x w z =
      f x * (L w * M z + L z * M w) := by
  have hd (y : Vector N) : HasFDerivAt (fun y => f y * L y * M y)
      ((L y * M y) • fderiv ℝ f y + (f y * M y) • L + (f y * L y) • M) y := by
    convert (((hf.differentiable (by norm_num) y).hasFDerivAt).mul L.hasFDerivAt).mul M.hasFDerivAt using 1
    ext a
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.mul_apply, smul_eq_mul, ContinuousLinearMap.id_apply, Pi.mul_apply]
    ring
  have hde : fderiv ℝ (fun y => f y * L y * M y) =
      fun y => (L y * M y) • fderiv ℝ f y + (f y * M y) • L + (f y * L y) • M :=
    funext (fun y => (hd y).fderiv)
  have h2 := ((L.hasFDerivAt.mul M.hasFDerivAt).smul
      (((hf.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt)).add
    ((((hf.differentiable (by norm_num) x).hasFDerivAt.mul M.hasFDerivAt).smul_const L))
  have h3 := h2.add (((hf.differentiable (by norm_num) x).hasFDerivAt.mul L.hasFDerivAt).smul_const M)
  change HasFDerivAt (fun y => (L y * M y) • fderiv ℝ f y + (f y * M y) • L + (f y * L y) • M) _ x at h3
  rw [hde, h3.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, hL, hM, zero_mul, mul_zero,
    add_zero, zero_add, zero_smul, Pi.mul_apply, ContinuousLinearMap.zero_apply]
  ring

theorem bilinear_tangent_coefficient_gram (hp : 2 ≤ p) (x u v w z : Vector N)
    (hu : inner ℝ u x = 0) (hv : inner ℝ v x = 0) :
    (∑ I : TensorIndex N p, bilinearCoeff I x u v * bilinearCoeff I x w z) =
      normalization N p^2 * (p:ℝ) * ((p:ℝ)-1) * (inner ℝ x x)^(p-2) *
        (inner ℝ u w * inner ℝ v z + inner ℝ u z * inner ℝ v w) := by
  have he : (fun y : Vector N => ∑ I : TensorIndex N p,
      bilinearCoeff I x u v * hamiltonianCoefficient I y) =
      fun y => (normalization N p^2 * (p:ℝ) * ((p:ℝ)-1) * (inner ℝ x y)^(p-2)) *
        inner ℝ u y * inner ℝ v y := funext (fun y => bilinear_coefficient_gram_left hp x y u v)
  have hh := linear_combination_derivative (fun I : TensorIndex N p => bilinearCoeff I x u v)
    2 x ![w,z]
  rw [he, iteratedFDeriv_two_apply] at hh
  have hf : ContDiff ℝ 2 (fun y : Vector N =>
      normalization N p^2 * (p:ℝ) * ((p:ℝ)-1) * (inner ℝ x y)^(p-2)) := by
    exact contDiff_const.mul ((contDiff_const.inner ℝ contDiff_id).pow (p-2))
  have hh2 := second_derivative_product_vanish hf (innerSL ℝ u) (innerSL ℝ v) x w z
    (by simpa only [innerSL_apply_apply] using hu) (by simpa only [innerSL_apply_apply] using hv)
  simp only [innerSL_apply_apply] at hh2
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] at hh
  rw [hh2] at hh
  simp only [coefficientDerivative, iteratedFDeriv_two_apply,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] at hh
  exact hh.symm

theorem actual_tangent_hessian_covariance (hN : 0 < N) (hp : 2 ≤ p)
    (x u v w z : Vector N) {r : ℝ} (hx : ‖x‖^2 = (N:ℝ)*r)
    (hu : inner ℝ u x = 0) (hv : inner ℝ v x = 0) :
    (∫ J : Disorder N p,
      (fderiv ℝ (fderiv ℝ (Hamiltonian N p J)) x u v) *
        (fderiv ℝ (fderiv ℝ (Hamiltonian N p J)) x w z) ∂disorderLaw N p) =
      ((p:ℝ) * ((p:ℝ)-1) * r^(p-2) / (N:ℝ)) *
        (inner ℝ u w * inner ℝ v z + inner ℝ u z * inner ℝ v w) := by
  have hg := Hamiltonian_derivative_covariance_gram (p:=p) 2 2 x x ![u,v] ![w,z]
  simp only [iteratedFDeriv_two_apply, coefficientDerivative,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] at hg
  rw [hg]
  change (∑ I : TensorIndex N p, bilinearCoeff I x u v * bilinearCoeff I x w z) = _
  rw [bilinear_tangent_coefficient_gram hp x u v w z hu hv]
  have hr : inner ℝ x x / (N:ℝ) = r := by
    rw [real_inner_self_eq_norm_sq, hx]
    exact mul_div_cancel_left₀ r (Nat.cast_ne_zero.mpr hN.ne')
  calc
    _ = ((p:ℝ) * ((p:ℝ)-1)) * (normalization N p^2 * (inner ℝ x x)^(p-2)) *
        (inner ℝ u w * inner ℝ v z + inner ℝ u z * inner ℝ v w) := by ring
    _ = _ := by rw [normalization_second_power hN hp, hr]; ring

theorem actual_bilinear_hessian_mean (x u v : Vector N) :
    (∫ J : Disorder N p, fderiv ℝ (fderiv ℝ (Hamiltonian N p J)) x u v ∂disorderLaw N p) = 0 := by
  simpa only [iteratedFDeriv_two_apply, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one] using Hamiltonian_derivative_mean (p:=p) 2 x ![u,v]

theorem actual_bilinear_hessian_memLp (x u v : Vector N) :
    MemLp (fun J : Disorder N p => fderiv ℝ (fderiv ℝ (Hamiltonian N p J)) x u v)
      2 (disorderLaw N p) := by
  simpa only [iteratedFDeriv_two_apply, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one] using Hamiltonian_derivative_memLp (p:=p) 2 x ![u,v]

theorem actual_bilinear_hessian_hasGaussianLaw (x u v : Vector N) :
    HasGaussianLaw (fun J : Disorder N p => fderiv ℝ (fderiv ℝ (Hamiltonian N p J)) x u v)
      (disorderLaw N p) := by
  simpa only [iteratedFDeriv_two_apply, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one] using Hamiltonian_derivative_hasGaussianLaw (p:=p) 2 x ![u,v]

theorem actual_tangent_hessian_coordinate_covariance {ι : Type*} [DecidableEq ι]
    (hN : 0 < N) (hp : 2 ≤ p) (x : Vector N) {r : ℝ} (hx : ‖x‖^2 = (N:ℝ)*r)
    (e : ι → Vector N) (he : Orthonormal ℝ e) (htan : ∀i, inner ℝ (e i) x = 0)
    (i j k l : ι) :
    (∫ J : Disorder N p,
      (fderiv ℝ (fderiv ℝ (Hamiltonian N p J)) x (e i) (e j)) *
        (fderiv ℝ (fderiv ℝ (Hamiltonian N p J)) x (e k) (e l)) ∂disorderLaw N p) =
      ((p:ℝ) * ((p:ℝ)-1) * r^(p-2) / (N:ℝ)) *
        ((if i=k then 1 else 0) * (if j=l then 1 else 0) +
          (if i=l then 1 else 0) * (if j=k then 1 else 0)) := by
  rw [actual_tangent_hessian_covariance hN hp x (e i) (e j) (e k) (e l) hx (htan i) (htan j)]
  simp only [(orthonormal_iff_ite.mp he)]

end SphericalAging.HamiltonianTangentHessianCovariance

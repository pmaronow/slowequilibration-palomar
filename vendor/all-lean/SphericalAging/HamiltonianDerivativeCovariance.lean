module

public import SphericalAging.GaussianIntegrationByParts
public import SphericalAging.LandscapeDerivatives
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.Trace

public section

/-!
# Genuine cross-covariances of Hamiltonian derivatives

Every derivative is the actual iterated Fréchet derivative of the manuscript's
ordered Gaussian Hamiltonian. Their Gaussian laws and mixed covariance kernel
are proved by integration against the actual product disorder measure.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace BigOperators
namespace SphericalAging.HamiltonianDerivativeCovariance
open FiniteModel GaussianIntegrationByParts

/-- Actual ordered coefficient functions are smooth polynomials. -/
theorem coefficient_contDiff {N p : ℕ} (I : TensorIndex N p) :
    ContDiff ℝ ⊤ (hamiltonianCoefficient I) :=
  contDiff_const.mul (tensorMonomial_contDiff I)

/-- The genuine coefficient derivative in any ordered list of directions. -/
@[expose] def coefficientDerivative {N p : ℕ} (k : ℕ) (I : TensorIndex N p)
    (x : Vector N) (a : Fin k → Vector N) : ℝ :=
  iteratedFDeriv ℝ k (hamiltonianCoefficient I) x a

/-- True differentiation of the actual finite coefficient expansion. -/
theorem linear_combination_derivative {N p : ℕ} (c : TensorIndex N p → ℝ)
    (k : ℕ) (x : Vector N) (a : Fin k → Vector N) :
    iteratedFDeriv ℝ k (fun z : Vector N => ∑ I : TensorIndex N p, c I*hamiltonianCoefficient I z) x a =
      ∑ I : TensorIndex N p, c I*coefficientDerivative k I x a := by
  rw [iteratedFDeriv_fun_sum_apply (fun I _ =>
    (contDiff_const.mul (coefficient_contDiff I)).contDiffAt.of_le (by simp))]
  simp only [ContinuousMultilinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro I _
  have hi := iteratedFDeriv_const_smul_apply' (i := k) (x := x) (a := c I)
    ((coefficient_contDiff I).contDiffAt.of_le (by simp))
  simpa only [smul_eq_mul,ContinuousMultilinearMap.smul_apply,coefficientDerivative] using congrArg (fun f => f a) hi

/-- All true Hamiltonian derivatives are linear functions of the actual iid Gaussian tensor. -/
theorem Hamiltonian_derivative_tensorLinear {N p : ℕ} (J : Disorder N p)
    (k : ℕ) (x : Vector N) (a : Fin k → Vector N) :
    iteratedFDeriv ℝ k (Hamiltonian N p J) x a=
      tensorLinear (fun I => coefficientDerivative k I x a) J := by
  have he : Hamiltonian N p J=fun z => ∑ I : TensorIndex N p, J I*hamiltonianCoefficient I z := by
    funext z
    exact hamiltonian_eq_sum_coefficients J z
  rw [he,linear_combination_derivative]
  simp only [tensorLinear,mul_comm]

/-- Exact mean zero for every genuine Hamiltonian derivative. -/
theorem Hamiltonian_derivative_mean {N p : ℕ} (k : ℕ) (x : Vector N) (a : Fin k → Vector N) :
    ∫ J : Disorder N p, iteratedFDeriv ℝ k (Hamiltonian N p J) x a ∂disorderLaw N p=0 := by
  simp_rw [Hamiltonian_derivative_tensorLinear]
  exact tensorLinear_mean _

theorem Hamiltonian_derivative_memLp {N p : ℕ} (k : ℕ) (x : Vector N) (a : Fin k → Vector N) :
    MemLp (fun J : Disorder N p => iteratedFDeriv ℝ k (Hamiltonian N p J) x a) 2 (disorderLaw N p) := by
  simp_rw [Hamiltonian_derivative_tensorLinear]
  exact tensorLinear_memLp _

theorem Hamiltonian_derivative_hasGaussianLaw {N p : ℕ} (k : ℕ) (x : Vector N) (a : Fin k → Vector N) :
    HasGaussianLaw (fun J : Disorder N p => iteratedFDeriv ℝ k (Hamiltonian N p J) x a) (disorderLaw N p) := by
  simp_rw [Hamiltonian_derivative_tensorLinear]
  exact tensorLinear_hasGaussianLaw _

/-- Actual product-Gaussian integration gives the complete coefficient derivative Gram kernel. -/
theorem Hamiltonian_derivative_covariance_gram {N p : ℕ} (k l : ℕ)
    (x y : Vector N) (a : Fin k → Vector N) (b : Fin l → Vector N) :
    ∫ J : Disorder N p,
      iteratedFDeriv ℝ k (Hamiltonian N p J) x a*iteratedFDeriv ℝ l (Hamiltonian N p J) y b ∂disorderLaw N p =
      ∑ I : TensorIndex N p, coefficientDerivative k I x a*coefficientDerivative l I y b := by
  simp_rw [Hamiltonian_derivative_tensorLinear]
  exact tensorLinear_covariance _ _

/-- Exact deterministic coefficient kernel with the manuscript's ordered normalization. -/
theorem coefficient_gram {N p : ℕ} (x y : Vector N) :
    ∑ I : TensorIndex N p, hamiltonianCoefficient I x*hamiltonianCoefficient I y =
      normalization N p^2*(inner ℝ x y)^p := by
  unfold hamiltonianCoefficient
  have he : (∑ I : TensorIndex N p,
      (normalization N p*tensorMonomial x I)*(normalization N p*tensorMonomial y I)) =
      normalization N p^2*∑ I : TensorIndex N p, tensorMonomial x I*tensorMonomial y I := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I _
    ring
  rw [he,tensorMonomial_gram]

/-- First differentiation of the genuine coefficient Gram kernel, for every derivative order. -/
theorem coefficient_derivative_gram {N p : ℕ} (k : ℕ)
    (x y : Vector N) (a : Fin k → Vector N) :
    ∑ I : TensorIndex N p, coefficientDerivative k I x a*hamiltonianCoefficient I y =
      iteratedFDeriv ℝ k (fun z : Vector N => normalization N p^2*(inner ℝ z y)^p) x a := by
  have he : (fun z : Vector N => normalization N p^2*(inner ℝ z y)^p) =
      fun z => ∑ I : TensorIndex N p, hamiltonianCoefficient I y*hamiltonianCoefficient I z := by
    funext z
    rw [← coefficient_gram z y]
    simp only [mul_comm]
  rw [he,linear_combination_derivative]
  simp only [mul_comm]

/-- All first/second and higher cross-covariances are genuine mixed derivatives of the exact polynomial kernel. -/
theorem Hamiltonian_mixed_derivative_covariance {N p : ℕ} (k l : ℕ)
    (x y : Vector N) (a : Fin k → Vector N) (b : Fin l → Vector N) :
    ∫ J : Disorder N p,
      iteratedFDeriv ℝ k (Hamiltonian N p J) x a*iteratedFDeriv ℝ l (Hamiltonian N p J) y b ∂disorderLaw N p =
      iteratedFDeriv ℝ l (fun z : Vector N =>
        iteratedFDeriv ℝ k (fun w : Vector N => normalization N p^2*(inner ℝ w z)^p) x a) y b := by
  rw [Hamiltonian_derivative_covariance_gram]
  have he : (fun z : Vector N => iteratedFDeriv ℝ k
      (fun w : Vector N => normalization N p^2*(inner ℝ w z)^p) x a) =
      fun z => ∑ I : TensorIndex N p, coefficientDerivative k I x a*hamiltonianCoefficient I z := by
    funext z
    exact (coefficient_derivative_gram k x z a).symm
  rw [he,linear_combination_derivative]

/-- Genuine derivative of the exact covariance polynomial in its first spatial argument. -/
theorem covarianceKernel_hasFDerivAt_left {N p : ℕ} (x y : Vector N) :
    HasFDerivAt (fun z : Vector N => normalization N p^2*(inner ℝ z y)^p)
      ((normalization N p^2*(p : ℝ)*(inner ℝ x y)^(p-1)) • innerSL ℝ y) x := by
  have hi : HasFDerivAt (fun z : Vector N => inner ℝ z y) (innerSL ℝ y) x := by
    convert (innerSL ℝ y).hasFDerivAt (x := x) using 1
    funext z
    simp only [innerSL_apply_apply]
    exact real_inner_comm _ _
  convert (hi.pow p).const_mul (normalization N p^2) using 1
  ext a
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.id_apply,innerSL_apply_apply]
  ring

/-- Actual ordered coefficient gradient Gram kernel, before simplifying the dimension factor. -/
theorem coefficient_gradient_gram_left {N p : ℕ} (x y a : Vector N) :
    ∑ I : TensorIndex N p, (fderiv ℝ (hamiltonianCoefficient I) x a)*hamiltonianCoefficient I y =
      normalization N p^2*(p : ℝ)*(inner ℝ x y)^(p-1)*inner ℝ a y := by
  have hg := coefficient_derivative_gram (p := p) 1 x y (fun _ => a)
  simp only [coefficientDerivative,iteratedFDeriv_one_apply] at hg
  rw [hg,(covarianceKernel_hasFDerivAt_left x y).fderiv]
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,innerSL_apply_apply]
  rw [real_inner_comm y a]

/-- True derivative of the first-gradient kernel in its second argument. -/
theorem firstGradientKernel_hasFDerivAt {N p : ℕ} (x y a : Vector N) :
    HasFDerivAt (fun z : Vector N =>
      normalization N p^2*(p : ℝ)*(inner ℝ x z)^(p-1)*inner ℝ a z)
      ((normalization N p^2*(p : ℝ)) •
        ((((p-1 : ℕ) : ℝ)*(inner ℝ x y)^((p-1)-1)*inner ℝ a y) • innerSL ℝ x+
          (inner ℝ x y)^(p-1) • innerSL ℝ a)) y := by
  have hi : HasFDerivAt (fun z : Vector N => inner ℝ x z) (innerSL ℝ x) y := by
    convert (innerSL ℝ x).hasFDerivAt (x := y) using 1
    funext z
    simp only [innerSL_apply_apply]
  have ha : HasFDerivAt (fun z : Vector N => inner ℝ a z) (innerSL ℝ a) y := by
    convert (innerSL ℝ a).hasFDerivAt (x := y) using 1
    funext z
    simp only [innerSL_apply_apply]
  convert ((hi.pow (p-1)).const_mul (normalization N p^2*(p : ℝ))).mul ha using 1
  ext b
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,smul_eq_mul,
    ContinuousLinearMap.mul_apply,ContinuousLinearMap.id_apply,innerSL_apply_apply]
  ring

/-- Exact gradient-gradient coefficient kernel, including the trace and rank-one terms. -/
theorem coefficient_gradient_cross_gram {N p : ℕ} (hp : 2 ≤ p) (x y a b : Vector N) :
    ∑ I : TensorIndex N p,
      (fderiv ℝ (hamiltonianCoefficient I) x a)*(fderiv ℝ (hamiltonianCoefficient I) y b) =
      normalization N p^2*((p : ℝ)*(inner ℝ x y)^(p-1)*inner ℝ a b+
        (p : ℝ)*((p : ℝ)-1)*(inner ℝ x y)^(p-2)*inner ℝ a y*inner ℝ x b) := by
  have hleft : HasFDerivAt (fun z : Vector N =>
      ∑ I : TensorIndex N p, (fderiv ℝ (hamiltonianCoefficient I) x a)*hamiltonianCoefficient I z)
      (∑ I : TensorIndex N p, (fderiv ℝ (hamiltonianCoefficient I) x a) •
        fderiv ℝ (hamiltonianCoefficient I) y) y := by
    exact HasFDerivAt.fun_sum (fun I _ =>
      ((coefficient_contDiff I).differentiable (by simp) y).hasFDerivAt.const_mul _)
  have he : (fun z : Vector N =>
      ∑ I : TensorIndex N p, (fderiv ℝ (hamiltonianCoefficient I) x a)*hamiltonianCoefficient I z) =
      fun z => normalization N p^2*(p : ℝ)*(inner ℝ x z)^(p-1)*inner ℝ a z := by
    funext z
    exact coefficient_gradient_gram_left x z a
  rw [he] at hleft
  have hc := congrArg (fun f : Vector N →L[ℝ] ℝ => f b)
    (hleft.unique (firstGradientKernel_hasFDerivAt x y a))
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply,smul_eq_mul,innerSL_apply_apply] at hc
  have hpred : ((p-1 : ℕ) : ℝ)=(p : ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hsub : (p-1)-1=p-2 := by omega
  rw [hpred,hsub] at hc
  exact hc.trans (by ring)

/-- Genuine Gaussian covariance of directional Euclidean gradients. -/
theorem Hamiltonian_gradient_covariance {N p : ℕ} (hp : 2 ≤ p) (x y a b : Vector N) :
    ∫ J : Disorder N p,
      inner ℝ (gradient (Hamiltonian N p J) x) a*inner ℝ (gradient (Hamiltonian N p J) y) b ∂disorderLaw N p =
      normalization N p^2*((p : ℝ)*(inner ℝ x y)^(p-1)*inner ℝ a b+
        (p : ℝ)*((p : ℝ)-1)*(inner ℝ x y)^(p-2)*inner ℝ a y*inner ℝ x b) := by
  have hg := Hamiltonian_derivative_covariance_gram (p := p) 1 1 x y (fun _ => a) (fun _ => b)
  simp only [coefficientDerivative,iteratedFDeriv_one_apply] at hg
  simp only [inner_gradient_left]
  exact hg.trans (coefficient_gradient_cross_gram hp x y a b)

/-- Genuine mixed derivative covariance in the manuscript's exact `N * overlap^p` convention. -/
theorem Hamiltonian_mixed_derivative_covariance_overlap {N p : ℕ} (hN : 0 < N) (hp : 1 ≤ p)
    (k l : ℕ) (x y : Vector N) (a : Fin k → Vector N) (b : Fin l → Vector N) :
    ∫ J : Disorder N p,
      iteratedFDeriv ℝ k (Hamiltonian N p J) x a*iteratedFDeriv ℝ l (Hamiltonian N p J) y b ∂disorderLaw N p =
      iteratedFDeriv ℝ l (fun z : Vector N =>
        iteratedFDeriv ℝ k (fun w : Vector N => (N : ℝ)*((inner ℝ w z)/N)^p) x a) y b := by
  rw [Hamiltonian_mixed_derivative_covariance]
  have he (z : Vector N) : (fun w : Vector N => normalization N p^2*(inner ℝ w z)^p) =
      fun w => (N : ℝ)*((inner ℝ w z)/N)^p := by
    funext w
    rw [normalization_sq N p hN,dimension_covariance_scale N p hN hp]
  simp_rw [he]

theorem normalization_first_power {N p : ℕ} (hN : 0 < N) (z : ℝ) :
    normalization N p^2*z^(p-1)=(z/N)^(p-1) := by
  rw [normalization_sq N p hN,zpow_neg,zpow_natCast,div_pow]
  simp [div_eq_mul_inv,mul_comm]

theorem normalization_second_power {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p) (z : ℝ) :
    normalization N p^2*z^(p-2)=(z/N)^(p-2)/N := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [normalization_sq N p hN,zpow_neg,zpow_natCast,div_pow]
  have hn : p-1=(p-2)+1 := by omega
  rw [hn,pow_succ]
  field_simp

/-- Source trace/rank-one coefficient covariance, with all dimension factors explicit. -/
theorem coefficient_gradient_cross_gram_overlap {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p)
    (x y a b : Vector N) :
    ∑ I : TensorIndex N p,
      (fderiv ℝ (hamiltonianCoefficient I) x a)*(fderiv ℝ (hamiltonianCoefficient I) y b) =
      (p : ℝ)*((inner ℝ x y)/N)^(p-1)*inner ℝ a b+
        ((p : ℝ)*((p : ℝ)-1)/N)*((inner ℝ x y)/N)^(p-2)*inner ℝ a y*inner ℝ x b := by
  rw [coefficient_gradient_cross_gram hp]
  calc
    _ = (p : ℝ)*(normalization N p^2*(inner ℝ x y)^(p-1))*inner ℝ a b+
      (p : ℝ)*((p : ℝ)-1)*(normalization N p^2*(inner ℝ x y)^(p-2))*inner ℝ a y*inner ℝ x b := by ring
    _ = _ := by rw [normalization_first_power hN,normalization_second_power hN hp]; ring

/-- Genuine directional gradient covariance with the manuscript's trace/rank-one coefficients. -/
theorem Hamiltonian_gradient_covariance_overlap {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p)
    (x y a b : Vector N) :
    ∫ J : Disorder N p,
      inner ℝ (gradient (Hamiltonian N p J) x) a*inner ℝ (gradient (Hamiltonian N p J) y) b ∂disorderLaw N p =
      (p : ℝ)*((inner ℝ x y)/N)^(p-1)*inner ℝ a b+
        ((p : ℝ)*((p : ℝ)-1)/N)*((inner ℝ x y)/N)^(p-2)*inner ℝ a y*inner ℝ x b := by
  have hg := Hamiltonian_derivative_covariance_gram (p := p) 1 1 x y (fun _ => a) (fun _ => b)
  simp only [coefficientDerivative,iteratedFDeriv_one_apply] at hg
  simp only [inner_gradient_left]
  exact hg.trans (coefficient_gradient_cross_gram_overlap hN hp x y a b)

/-- Exact coordinate covariance of the true ordered-coefficient gradients, including repeated indices. -/
theorem coefficient_gradient_coordinate_cross {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p)
    (x y : Vector N) (i j : Fin N) :
    ∑ I : TensorIndex N p, (gradient (hamiltonianCoefficient I) x) i*(gradient (hamiltonianCoefficient I) y) j =
      (p : ℝ)*((inner ℝ x y)/N)^(p-1)*(if i=j then 1 else 0)+
        ((p : ℝ)*((p : ℝ)-1)/N)*((inner ℝ x y)/N)^(p-2)*y i*x j := by
  have hg := coefficient_gradient_cross_gram_overlap hN hp x y
    (HardSphereDynamics.basisVector i) (HardSphereDynamics.basisVector j)
  simpa [← inner_gradient_left,HardSphereDynamics.basisVector,EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right,eq_comm] using hg

/-- Actual ordered coefficient-gradient cross-covariance as an operator. -/
@[expose] def gradientCrossOperator {N p : ℕ} (x y : Vector N) : Vector N →L[ℝ] Vector N :=
  ∑ I : TensorIndex N p,
    (innerSL ℝ (gradient (hamiltonianCoefficient I) y)).smulRight (gradient (hamiltonianCoefficient I) x)

/-- True operator identity, rather than a stipulated trace/rank-one covariance. -/
theorem gradientCrossOperator_eq {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p) (x y : Vector N) :
    gradientCrossOperator (p := p) x y =
      ((p : ℝ)*((inner ℝ x y)/N)^(p-1)) • ContinuousLinearMap.id ℝ (Vector N)+
        (((p : ℝ)*((p : ℝ)-1)/N)*((inner ℝ x y)/N)^(p-2)) • (innerSL ℝ x).smulRight y := by
  apply ContinuousLinearMap.ext
  intro b
  apply ext_inner_right ℝ
  intro a
  simp only [gradientCrossOperator,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.id_apply,
    sum_inner,real_inner_smul_left,inner_add_left,innerSL_apply_apply,← inner_gradient_left]
  have hg := coefficient_gradient_cross_gram_overlap hN hp x y a b
  simp only [← inner_gradient_left] at hg
  rw [real_inner_comm a b, real_inner_comm a y]
  simpa only [mul_comm,mul_left_comm,mul_assoc] using hg

/-- Normalized trace of an actual finite-dimensional linear operator. -/
@[expose] def operatorTrace {N : ℕ} (U : Vector N →L[ℝ] Vector N) : ℝ :=
  LinearMap.trace ℝ (Vector N) U.toLinearMap

/-- Exact contraction of the covariance operator with an arbitrary actual flow matrix. -/
theorem gradientCrossOperator_trace {N p : ℕ} (hN : 0 < N) (hp : 2 ≤ p)
    (x y : Vector N) (U : Vector N →L[ℝ] Vector N) :
    operatorTrace (U.comp (gradientCrossOperator (p := p) x y)) =
      (p : ℝ)*((inner ℝ x y)/N)^(p-1)*operatorTrace U+
        (((p : ℝ)*((p : ℝ)-1)/N)*((inner ℝ x y)/N)^(p-2))*inner ℝ x (U y) := by
  rw [gradientCrossOperator_eq hN hp]
  have he : U.comp
      (((p : ℝ)*((inner ℝ x y)/N)^(p-1)) • ContinuousLinearMap.id ℝ (Vector N)+
        (((p : ℝ)*((p : ℝ)-1)/N)*((inner ℝ x y)/N)^(p-2)) • (innerSL ℝ x).smulRight y) =
      ((p : ℝ)*((inner ℝ x y)/N)^(p-1)) • U+
        (((p : ℝ)*((p : ℝ)-1)/N)*((inner ℝ x y)/N)^(p-2)) • (innerSL ℝ x).smulRight (U y) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,
      map_add,map_smul]
  rw [he]
  simp only [operatorTrace,ContinuousLinearMap.toLinearMap_add,ContinuousLinearMap.toLinearMap_smul,
    map_add,map_smul,smul_eq_mul]
  rw [show ((innerSL ℝ x).smulRight (U y)).toLinearMap=(innerSL ℝ x).toLinearMap.smulRight (U y) from rfl,
    LinearMap.trace_smulRight]
  rfl

end SphericalAging.HamiltonianDerivativeCovariance

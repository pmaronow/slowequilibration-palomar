module

public import SphericalAging.HamiltonianTangentHessianCovariance
public import SphericalAging.OrthogonalGaussianDisclosure
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

public section

/-! The genuine Hamiltonian tangent Hessian has independent centered Gaussian
upper-triangular entries, with twice the variance on the diagonal. The entire
matrix law is derived from the original ordered iid disorder. -/

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace SphericalAging.HamiltonianTangentHessianGaussianLaw
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open GaussianIntegrationByParts HamiltonianDerivativeCovariance
open HamiltonianTangentHessianCovariance OrthogonalGaussianDisclosure
open scoped BigOperators InnerProductSpace NNReal
local instance {N : ℕ} : NormedAddCommGroup (Vector N →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance {N : ℕ} : NormedSpace ℝ (Vector N →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance {N : ℕ} : NormedAddCommGroup (Vector N →L[ℝ] Vector N →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance {N : ℕ} : NormedSpace ℝ (Vector N →L[ℝ] Vector N →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
variable {N p k : ℕ}

@[expose] abbrev UpperIndex (k : ℕ) := {ij : Fin k × Fin k // ij.1 ≤ ij.2}

@[expose] def hessianEntry (x : Vector N) (e : Fin k → Vector N) (i j : Fin k) (J : Disorder N p) : ℝ :=
  fderiv ℝ (fderiv ℝ (Hamiltonian N p J)) x (e i) (e j)

@[expose] def upperEntries (x : Vector N) (e : Fin k → Vector N) (J : Disorder N p) : UpperIndex k → ℝ :=
  fun ij => hessianEntry x e ij.1.1 ij.1.2 J

@[expose] def entryOperator (x : Vector N) (e : Fin k → Vector N) (i j : Fin k) :
    TensorSpace N p →L[ℝ] ℝ :=
  innerSL ℝ (WithLp.toLp 2 (fun I : TensorIndex N p => bilinearCoeff I x (e i) (e j)))

@[expose] def upperOperator (x : Vector N) (e : Fin k → Vector N) :
    TensorSpace N p →L[ℝ] (UpperIndex k → ℝ) :=
  ContinuousLinearMap.pi (fun ij => entryOperator x e ij.1.1 ij.1.2)

theorem hessianEntry_tensorLinear (x : Vector N) (e : Fin k → Vector N) (i j : Fin k)
    (J : Disorder N p) :
    hessianEntry x e i j J = tensorLinear (fun I => bilinearCoeff I x (e i) (e j)) J := by
  simpa only [hessianEntry, coefficientDerivative, bilinearCoeff, iteratedFDeriv_two_apply,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] using
      Hamiltonian_derivative_tensorLinear J 2 x ![e i,e j]

theorem entryOperator_apply (x : Vector N) (e : Fin k → Vector N) (i j : Fin k)
    (J : Disorder N p) :
    entryOperator x e i j (WithLp.toLp 2 J) = hessianEntry x e i j J := by
  rw [hessianEntry_tensorLinear]
  simp only [entryOperator, innerSL_apply_apply, PiLp.inner_apply, tensorLinear,
    WithLp.ofLp_toLp, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl (fun I _ => mul_comm _ _)

theorem upperOperator_apply (x : Vector N) (e : Fin k → Vector N) (J : Disorder N p) :
    upperOperator x e (WithLp.toLp 2 J) = upperEntries x e J := by
  funext ij
  exact entryOperator_apply x e ij.1.1 ij.1.2 J

theorem actual_upperEntries_jointGaussian (x : Vector N) (e : Fin k → Vector N) :
    HasGaussianLaw (upperEntries (p:=p) x e) (disorderLaw N p) := by
  have hg := ((ordered_tensor_hasLaw N p).hasGaussianLaw).map_fun (upperOperator (p:=p) x e)
  simpa only [Function.comp_def, upperOperator_apply] using hg

theorem actual_entry_covariance (hN : 0 < N) (hp : 2 ≤ p) (x : Vector N) {r : ℝ}
    (hx : ‖x‖^2 = (N:ℝ)*r) (e : Fin k → Vector N) (he : Orthonormal ℝ e)
    (htan : ∀i, inner ℝ (e i) x = 0) (i j l m : Fin k) :
    cov[hessianEntry (p:=p) x e i j, hessianEntry (p:=p) x e l m; disorderLaw N p] =
      ((p:ℝ) * ((p:ℝ)-1) * r^(p-2) / (N:ℝ)) *
        ((if i=l then 1 else 0) * (if j=m then 1 else 0) +
          (if i=m then 1 else 0) * (if j=l then 1 else 0)) := by
  unfold hessianEntry
  rw [covariance_eq_sub (actual_bilinear_hessian_memLp x (e i) (e j))
    (actual_bilinear_hessian_memLp x (e l) (e m))]
  simp only [hessianEntry, Pi.mul_apply, actual_bilinear_hessian_mean, zero_mul, sub_zero]
  exact actual_tangent_hessian_coordinate_covariance hN hp x hx e he htan i j l m

theorem upperIndex_covariance_factor_zero (a b : UpperIndex k) (hab : a ≠ b) :
    ((if a.1.1=b.1.1 then (1:ℝ) else 0) * (if a.1.2=b.1.2 then 1 else 0) +
      (if a.1.1=b.1.2 then 1 else 0) * (if a.1.2=b.1.1 then 1 else 0)) = 0 := by
  have hsame : ¬(a.1.1=b.1.1 ∧ a.1.2=b.1.2) := by
    rintro ⟨h1,h2⟩
    exact hab (Subtype.ext (Prod.ext h1 h2))
  have hswap : ¬(a.1.1=b.1.2 ∧ a.1.2=b.1.1) := by
    rintro ⟨h1,h2⟩
    have ha := a.2
    have hb := b.2
    have heq : a.1.1=a.1.2 := by omega
    exact hsame ⟨by omega,by omega⟩
  split_ifs <;> simp_all

theorem actual_upperEntries_independent (hN : 0 < N) (hp : 2 ≤ p) (x : Vector N) {r : ℝ}
    (hx : ‖x‖^2 = (N:ℝ)*r) (e : Fin k → Vector N) (he : Orthonormal ℝ e)
    (htan : ∀i, inner ℝ (e i) x = 0) :
    iIndepFun (fun ij : UpperIndex k => fun J : Disorder N p => upperEntries x e J ij)
      (disorderLaw N p) := by
  apply (actual_upperEntries_jointGaussian (p:=p) x e).iIndepFun_of_covariance_eq_zero
  intro a b hab
  change cov[hessianEntry x e a.1.1 a.1.2, hessianEntry x e b.1.1 b.1.2; disorderLaw N p] = 0
  rw [actual_entry_covariance hN hp x hx e he htan, upperIndex_covariance_factor_zero a b hab, mul_zero]

@[expose] def entryVariance (N p : ℕ) (r : ℝ) {k : ℕ} (ij : UpperIndex k) : ℝ≥0 :=
  (((p:ℝ) * ((p:ℝ)-1) * r^(p-2) / (N:ℝ)) *
    (if ij.1.1=ij.1.2 then 2 else 1)).toNNReal

theorem actual_upperEntry_hasLaw (hN : 0 < N) (hp : 2 ≤ p) (x : Vector N) {r : ℝ}
    (hx : ‖x‖^2 = (N:ℝ)*r) (e : Fin k → Vector N) (he : Orthonormal ℝ e)
    (htan : ∀i, inner ℝ (e i) x = 0) (ij : UpperIndex k) :
    HasLaw (fun J : Disorder N p => upperEntries x e J ij)
      (gaussianReal 0 (entryVariance N p r ij)) (disorderLaw N p) := by
  have hg := (actual_upperEntries_jointGaussian (p:=p) x e).eval ij
  refine ⟨hg.aemeasurable,?_⟩
  rw [hg.map_eq_gaussianReal]
  have hm : (∫ J : Disorder N p, upperEntries x e J ij ∂disorderLaw N p)=0 :=
    actual_bilinear_hessian_mean x (e ij.1.1) (e ij.1.2)
  rw [hm]
  congr 1
  apply congrArg Real.toNNReal
  rw [← covariance_self hg.aemeasurable]
  change cov[hessianEntry x e ij.1.1 ij.1.2,
    hessianEntry x e ij.1.1 ij.1.2; disorderLaw N p] = _
  rw [actual_entry_covariance hN hp x hx e he htan]
  by_cases hh : ij.1.1 = ij.1.2
  · simp only [hh, ite_true, one_mul, mul_one, eq_self, one_add_one_eq_two]
  · simp only [hh, Ne.symm hh, ite_false, ite_true, one_mul, mul_one, zero_mul, add_zero, eq_self]

theorem actual_tangent_hessian_upper_product_law (hN : 0 < N) (hp : 2 ≤ p)
    (x : Vector N) {r : ℝ} (hx : ‖x‖^2 = (N:ℝ)*r)
    (e : Fin k → Vector N) (he : Orthonormal ℝ e) (htan : ∀i, inner ℝ (e i) x = 0) :
    HasLaw (upperEntries (p:=p) x e)
      (Measure.pi (fun ij : UpperIndex k => gaussianReal 0 (entryVariance N p r ij)))
      (disorderLaw N p) :=
  (actual_upperEntries_independent hN hp x hx e he htan).hasLaw_pi
    (actual_upperEntry_hasLaw hN hp x hx e he htan)

end SphericalAging.HamiltonianTangentHessianGaussianLaw

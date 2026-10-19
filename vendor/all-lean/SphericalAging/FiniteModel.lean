module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Tactic

public section

/-!
# The actual ordered Gaussian tensor model

The disorder is the finite product of standard real Gaussian laws indexed by
all ordered p-tuples. No symmetrization is performed. The Hamiltonian has
exactly the normalization of Section 3. Its mean and covariance below are
proved by integration against this actual law, not postulated as model axioms.
-/

noncomputable section

namespace SphericalAging.FiniteModel

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace

@[expose] abbrev Vector (N : ℕ) := EuclideanSpace ℝ (Fin N)
@[expose] abbrev TensorIndex (N p : ℕ) := Fin p → Fin N
@[expose] abbrev Disorder (N p : ℕ) := TensorIndex N p → ℝ

@[expose] def disorderLaw (N p : ℕ) : Measure (Disorder N p) :=
  Measure.pi (fun _ : TensorIndex N p => gaussianReal 0 1)

instance disorderLaw_isProbability (N p : ℕ) : IsProbabilityMeasure (disorderLaw N p) := by
  unfold disorderLaw
  infer_instance

@[expose] def tensorMonomial {N p : ℕ} (x : Vector N) (I : TensorIndex N p) : ℝ :=
  ∏ k : Fin p, x (I k)

@[expose] def normalization (N p : ℕ) : ℝ :=
  (N : ℝ) ^ (-((p - 1 : ℕ) : ℝ) / 2)

@[expose] def Hamiltonian (N p : ℕ) (J : Disorder N p) (x : Vector N) : ℝ :=
  normalization N p * ∑ I : TensorIndex N p, J I * tensorMonomial x I

/-- The couplings really are independent under the specified product law. -/
theorem disorder_iIndepFun (N p : ℕ) :
    iIndepFun (fun I : TensorIndex N p => fun J : Disorder N p => J I)
      (disorderLaw N p) := by
  exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

theorem coordinate_hasLaw (N p : ℕ) (I : TensorIndex N p) :
    HasLaw (fun J : Disorder N p => J I) (gaussianReal 0 1) (disorderLaw N p) :=
  (measurePreserving_eval (fun _ : TensorIndex N p => gaussianReal 0 1) I).hasLaw

theorem disorder_hasGaussianLaw (N p : ℕ) :
    HasGaussianLaw (id : Disorder N p → Disorder N p) (disorderLaw N p) := by
  exact (disorder_iIndepFun N p).hasGaussianLaw
    (fun I => (coordinate_hasLaw N p I).hasGaussianLaw)

theorem coordinate_memLp (N p : ℕ) (I : TensorIndex N p) :
    MemLp (fun J : Disorder N p => J I) 2 (disorderLaw N p) := by
  exact (memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_measurePreserving
    (measurePreserving_eval (fun _ : TensorIndex N p => gaussianReal 0 1) I)

theorem coordinate_mean (N p : ℕ) (I : TensorIndex N p) :
    ∫ J : Disorder N p, J I ∂disorderLaw N p = 0 := by
  unfold disorderLaw
  rw [integral_eval]
  simp

theorem standardGaussian_second_moment : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (by fun_prop)] at h
  simpa using h

theorem coordinate_product_integrable (N p : ℕ) (I K : TensorIndex N p) :
    Integrable (fun J : Disorder N p => J I * J K) (disorderLaw N p) :=
  (coordinate_memLp N p I).integrable_mul (coordinate_memLp N p K)

theorem coordinate_covariance (N p : ℕ) (I K : TensorIndex N p) :
    ∫ J : Disorder N p, J I * J K ∂disorderLaw N p = if I = K then 1 else 0 := by
  classical
  by_cases hIK : I = K
  · subst K
    rw [ite_eq_left rfl]
    unfold disorderLaw
    simpa [pow_two] using integral_comp_eval
      (μ := fun _ : TensorIndex N p => gaussianReal 0 1)
      (i := I) (f := fun x : ℝ => x ^ 2) (by fun_prop)
      |>.trans standardGaussian_second_moment
  · rw [ite_eq_right hIK]
    rw [(disorder_iIndepFun N p).indepFun hIK |>.integral_fun_mul_eq_mul_integral
      (coordinate_memLp N p I).aestronglyMeasurable
      (coordinate_memLp N p K).aestronglyMeasurable,
      coordinate_mean, coordinate_mean, zero_mul]

@[expose] def tensorLinear {N p : ℕ} (a : TensorIndex N p → ℝ) (J : Disorder N p) : ℝ :=
  ∑ I : TensorIndex N p, a I * J I

theorem tensorLinear_memLp {N p : ℕ} (a : TensorIndex N p → ℝ) :
    MemLp (tensorLinear a) 2 (disorderLaw N p) := by
  classical
  exact memLp_finsetSum _ (fun I _ => (coordinate_memLp N p I).const_mul (a I))

theorem tensorLinear_mean {N p : ℕ} (a : TensorIndex N p → ℝ) :
    ∫ J : Disorder N p, tensorLinear a J ∂disorderLaw N p = 0 := by
  classical
  unfold tensorLinear
  rw [integral_finsetSum _ (fun I _ =>
    ((coordinate_memLp N p I).integrable (by norm_num)).const_mul (a I))]
  simp [integral_const_mul, coordinate_mean]

theorem tensorLinear_hasGaussianLaw {N p : ℕ} (a : TensorIndex N p → ℝ) :
    HasGaussianLaw (tensorLinear a) (disorderLaw N p) := by
  classical
  have hG : ∀ I : TensorIndex N p,
      HasGaussianLaw (fun J : Disorder N p => a I * J I) (disorderLaw N p) := by
    intro I
    simpa only [smul_eq_mul] using
      (coordinate_hasLaw N p I).hasGaussianLaw.fun_smul (a I)
  exact iIndepFun.hasGaussianLaw_fun_sum hG
    ((disorder_iIndepFun N p).comp (fun I z => a I * z) (fun _ => by fun_prop))

theorem tensorLinear_covariance {N p : ℕ} (a b : TensorIndex N p → ℝ) :
    ∫ J : Disorder N p, tensorLinear a J * tensorLinear b J ∂disorderLaw N p =
      ∑ I : TensorIndex N p, a I * b I := by
  classical
  have hint : ∀ I K : TensorIndex N p,
      Integrable (fun J : Disorder N p => (a I * b K) * (J I * J K))
        (disorderLaw N p) := fun I K =>
    (coordinate_product_integrable N p I K).const_mul _
  have hexp : ∀ J : Disorder N p,
      tensorLinear a J * tensorLinear b J =
        ∑ I : TensorIndex N p, ∑ K : TensorIndex N p, (a I * b K) * (J I * J K) := by
    intro J
    simp only [tensorLinear]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro I _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro K _
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun I _ => integrable_finsetSum _ (fun K _ => hint I K))]
  calc
    (∑ I : TensorIndex N p, ∫ J, ∑ K : TensorIndex N p,
        (a I * b K) * (J I * J K) ∂disorderLaw N p) =
      ∑ I : TensorIndex N p, ∑ K : TensorIndex N p,
        (a I * b K) * (if I = K then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro I _
      rw [integral_finsetSum _ (fun K _ => hint I K)]
      simp_rw [integral_const_mul, coordinate_covariance]
    _ = ∑ I : TensorIndex N p, a I * b I := by simp

theorem Hamiltonian_eq_tensorLinear {N p : ℕ} (J : Disorder N p) (x : Vector N) :
    Hamiltonian N p J x = normalization N p * tensorLinear (tensorMonomial x) J := by
  simp only [Hamiltonian, tensorLinear, mul_comm]

theorem Hamiltonian_memLp {N p : ℕ} (x : Vector N) :
    MemLp (fun J : Disorder N p => Hamiltonian N p J x) 2 (disorderLaw N p) := by
  simp_rw [Hamiltonian_eq_tensorLinear]
  exact (tensorLinear_memLp (tensorMonomial x)).const_mul _

theorem Hamiltonian_mean {N p : ℕ} (x : Vector N) :
    ∫ J : Disorder N p, Hamiltonian N p J x ∂disorderLaw N p = 0 := by
  simp_rw [Hamiltonian_eq_tensorLinear]
  rw [integral_const_mul, tensorLinear_mean, mul_zero]

theorem Hamiltonian_hasGaussianLaw {N p : ℕ} (x : Vector N) :
    HasGaussianLaw (fun J : Disorder N p => Hamiltonian N p J x) (disorderLaw N p) := by
  simp_rw [Hamiltonian_eq_tensorLinear]
  simpa only [smul_eq_mul] using
    (tensorLinear_hasGaussianLaw (tensorMonomial x)).fun_smul (normalization N p)

/-- Expansion over ordered index tuples, including repeated coordinate indices. -/
theorem tensorMonomial_gram {N p : ℕ} (x y : Vector N) :
    ∑ I : TensorIndex N p, tensorMonomial x I * tensorMonomial y I =
      (inner ℝ x y) ^ p := by
  classical
  simp only [tensorMonomial, ← Finset.prod_mul_distrib]
  calc
    (∑ I : TensorIndex N p, ∏ k : Fin p, x (I k) * y (I k)) =
        ∏ _k : Fin p, ∑ i : Fin N, x i * y i :=
      (Fintype.prod_sum (fun _k : Fin p => fun i : Fin N => x i * y i)).symm
    _ = (∑ i : Fin N, x i * y i) ^ p := by simp
    _ = (inner ℝ x y) ^ p := by simp [PiLp.inner_apply, mul_comm]

theorem normalization_sq (N p : ℕ) (hN : 0 < N) :
    normalization N p ^ 2 = (N : ℝ) ^ (-((p - 1 : ℕ) : ℤ)) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  unfold normalization
  rw [← Real.rpow_mul_natCast hNreal.le]
  have hexp : -((p - 1 : ℕ) : ℝ) / 2 * (2 : ℕ) = -((p - 1 : ℕ) : ℝ) := by ring
  rw [hexp, Real.rpow_neg_natCast]

/-- The exact nonsymmetrized tensor covariance in the manuscript. -/
theorem Hamiltonian_covariance {N p : ℕ} (hN : 0 < N) (x y : Vector N) :
    ∫ J : Disorder N p, Hamiltonian N p J x * Hamiltonian N p J y ∂disorderLaw N p =
      (N : ℝ) ^ (-((p - 1 : ℕ) : ℤ)) * (inner ℝ x y) ^ p := by
  simp_rw [Hamiltonian_eq_tensorLinear]
  have hexp : ∀ J : Disorder N p,
      (normalization N p * tensorLinear (tensorMonomial x) J) *
        (normalization N p * tensorLinear (tensorMonomial y) J) =
      normalization N p ^ 2 *
        (tensorLinear (tensorMonomial x) J * tensorLinear (tensorMonomial y) J) := by
    intro J
    ring
  simp_rw [hexp]
  rw [integral_const_mul, tensorLinear_covariance, tensorMonomial_gram, normalization_sq N p hN]

theorem Hamiltonian_probability_covariance {N p : ℕ} (hN : 0 < N) (x y : Vector N) :
    covariance (fun J : Disorder N p => Hamiltonian N p J x)
      (fun J : Disorder N p => Hamiltonian N p J y) (disorderLaw N p) =
      (N : ℝ) ^ (-((p - 1 : ℕ) : ℤ)) * (inner ℝ x y) ^ p := by
  rw [covariance_eq_sub (Hamiltonian_memLp x) (Hamiltonian_memLp y)]
  simp only [Pi.mul_apply, Hamiltonian_mean, zero_mul, sub_zero]
  exact Hamiltonian_covariance hN x y

theorem dimension_covariance_scale (N p : ℕ) (hN : 0 < N) (hp : 1 ≤ p) (z : ℝ) :
    (N : ℝ) ^ (-((p - 1 : ℕ) : ℤ)) * z ^ p = (N : ℝ) * (z / N) ^ p := by
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hexp : p = (p - 1) + 1 := by omega
  rw [zpow_neg, zpow_natCast, div_pow]
  have hpow : (N : ℝ) ^ p = (N : ℝ) ^ (p - 1) * N := by
    simpa only [pow_succ] using congrArg (fun k : ℕ => (N : ℝ) ^ k) hexp
  rw [hpow]
  field_simp

/-- On the radius-sqrt(N) sphere this is `N * overlap^p`. -/
theorem Hamiltonian_covariance_overlap {N p : ℕ} (hN : 0 < N) (hp : 1 ≤ p)
    (x y : Vector N) :
    ∫ J : Disorder N p, Hamiltonian N p J x * Hamiltonian N p J y ∂disorderLaw N p =
      (N : ℝ) * ((inner ℝ x y) / N) ^ p := by
  rw [Hamiltonian_covariance hN, dimension_covariance_scale N p hN hp]

theorem Hamiltonian_variance_on_sphere {N p : ℕ} (hN : 0 < N) (hp : 1 ≤ p)
    (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) :
    variance (fun J : Disorder N p => Hamiltonian N p J x) (disorderLaw N p) = N := by
  rw [← covariance_self (Hamiltonian_memLp x).aemeasurable,
    Hamiltonian_probability_covariance hN,
    dimension_covariance_scale N p hN hp, real_inner_self_eq_norm_sq, hx]
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp [hNreal]

theorem tensorMonomial_contDiff {N p : ℕ} (I : TensorIndex N p) :
    ContDiff ℝ ⊤ (fun x : Vector N => tensorMonomial x I) := by
  unfold tensorMonomial
  fun_prop

theorem Hamiltonian_contDiff {N p : ℕ} (J : Disorder N p) :
    ContDiff ℝ ⊤ (fun x : Vector N => Hamiltonian N p J x) := by
  unfold Hamiltonian
  exact contDiff_const.mul (ContDiff.sum (fun I _ =>
    contDiff_const.mul (tensorMonomial_contDiff I)))

end SphericalAging.FiniteModel

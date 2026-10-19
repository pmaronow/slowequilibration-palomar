-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalModel
public import SlowEquilibration.InfiniteMixtureSummability
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-! The original infinite ordered Gaussian tensor disorder. Its countable
product law, independent blocks and literal field series are constructed here. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open MeasureTheory ProbabilityTheory SphericalModel
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Degree p+2 has its genuine independent ordered tensor coefficient block. -/
abbrev Disorder (N : ℕ) := (p : ℕ) → SphericalAging.FiniteModel.Disorder N (p+2)

/-- Actual countable product, rather than the finite-product measure. -/
def disorderLaw (N : ℕ) : Measure (Disorder N) :=
  Measure.infinitePi (fun p : ℕ => SphericalAging.FiniteModel.disorderLaw N (p+2))

instance (N : ℕ) : IsProbabilityMeasure (disorderLaw N) := by unfold disorderLaw;infer_instance

/-- One weighted actual homogeneous term of the source infinite field. -/
def block {N : ℕ} (μ : InfiniteMixture) (p : ℕ) (J : Disorder N) (x : Vector N) : ℝ :=
  Real.sqrt (μ.coeff (p+2))*SphericalAging.FiniteModel.Hamiltonian N (p+2) (J p) x

/-- The literal original series; convergence and the continuous version are
proved separately, rather than postulated in this definition. -/
def field {N : ℕ} (μ : InfiniteMixture) (J : Disorder N) (x : Vector N) : ℝ :=
  ∑' p,block μ p J x

theorem degree_hasLaw {N : ℕ} (p : ℕ) :
    HasLaw (fun J : Disorder N => J p) (SphericalAging.FiniteModel.disorderLaw N (p+2)) (disorderLaw N) :=
  (measurePreserving_eval_infinitePi (fun q : ℕ => SphericalAging.FiniteModel.disorderLaw N (q+2)) p).hasLaw

theorem independent_degrees (N : ℕ) :
    iIndepFun (fun p (J : Disorder N) => J p) (disorderLaw N) :=
  iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)

theorem degree_hasGaussianLaw {N : ℕ} (p : ℕ) :
    HasGaussianLaw (fun J : Disorder N => J p) (disorderLaw N) := by
  haveI : IsGaussian (SphericalAging.FiniteModel.disorderLaw N (p+2)) := by
    have h := SphericalAging.FiniteModel.disorder_hasGaussianLaw N (p+2)
    simpa only [Measure.map_id] using h.isGaussian_map
  exact (degree_hasLaw p).hasGaussianLaw

theorem block_hasGaussianLaw {N : ℕ} (μ : InfiniteMixture) (p : ℕ) (x : Vector N) :
    HasGaussianLaw (fun J : Disorder N => block μ p J x) (disorderLaw N) := by
  have h := (degree_hasGaussianLaw (N := N) p).map_fun
    (Real.sqrt (μ.coeff (p+2)) • pureFieldCLM N (p+2) x)
  change HasGaussianLaw (fun J : Disorder N => Real.sqrt (μ.coeff (p+2))*SphericalAging.FiniteModel.Hamiltonian N (p+2) (J p) x) _
  simpa only [smul_apply,smul_eq_mul,pureFieldCLM_apply] using h

theorem block_memLp {N : ℕ} (μ : InfiniteMixture) (p : ℕ) (x : Vector N) :
    MemLp (fun J : Disorder N => block μ p J x) 2 (disorderLaw N) :=
  (block_hasGaussianLaw μ p x).memLp_two

theorem block_mean {N : ℕ} (μ : InfiniteMixture) (p : ℕ) (x : Vector N) :
    ∫ J,block μ p J x ∂disorderLaw N=0 := by
  unfold block
  rw [integral_const_mul]
  have h := (degree_hasLaw (N := N) p).integral_comp
    (SphericalAging.FiniteModel.Hamiltonian_memLp x).aestronglyMeasurable
  dsimp only [Function.comp_def] at h
  rw [h,SphericalAging.FiniteModel.Hamiltonian_mean,mul_zero]

theorem block_product_integral {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (p : ℕ) (x y : Vector N) :
    ∫ J,block μ p J x*block μ p J y ∂disorderLaw N=
      (N:ℝ)*μ.coeff (p+2)*(overlap x y)^(p+2) := by
  have he (J : Disorder N) : block μ p J x*block μ p J y=
      μ.coeff (p+2)*(SphericalAging.FiniteModel.Hamiltonian N (p+2) (J p) x*
        SphericalAging.FiniteModel.Hamiltonian N (p+2) (J p) y) := by
    dsimp [block]
    calc
      _ = Real.sqrt (μ.coeff (p+2))^2 * (SphericalAging.FiniteModel.Hamiltonian N (p+2) (J p) x*
        SphericalAging.FiniteModel.Hamiltonian N (p+2) (J p) y) := by ring
      _ = _ := by rw [Real.sq_sqrt (μ.nonneg (p+2))]
  simp_rw [he]
  rw [integral_const_mul]
  have h := (degree_hasLaw (N := N) p).integral_comp
    ((SphericalAging.FiniteModel.Hamiltonian_memLp x).integrable_mul
      (SphericalAging.FiniteModel.Hamiltonian_memLp y)).aestronglyMeasurable
  dsimp only [Function.comp_def,Pi.mul_apply] at h
  rw [h,SphericalAging.FiniteModel.Hamiltonian_covariance_overlap hN (by omega)]
  change _=(N:ℝ)*μ.coeff (p+2)*(inner ℝ x y/N)^(p+2)
  ring

/-- The block as an actual element of the common original-disorder L² space. -/
def blockLp {N : ℕ} (μ : InfiniteMixture) (p : ℕ) (x : Vector N) : Lp ℝ 2 (disorderLaw N) :=
  (block_memLp μ p x).toLp (fun J => block μ p J x)

theorem blockLp_norm_sq {N : ℕ} (hN : 0<N) (μ : InfiniteMixture) (p : ℕ) (x : Vector N) :
    ‖blockLp μ p x‖^2=(N:ℝ)*μ.coeff (p+2)*(‖x‖^2/N)^(p+2) := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [RCLike.inner_apply,conj_trivial]
  unfold blockLp
  have he := (block_memLp μ p x).coeFn_toLp
  rw [integral_congr_ae (he.fun_mul he)]
  simpa only [overlap,real_inner_self_eq_norm_sq] using block_product_integral hN μ p x x

theorem blockLp_norm_le {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (p : ℕ) (x : Vector N) (hx : ‖x‖^2≤(N:ℝ)) :
    ‖blockLp μ p x‖≤Real.sqrt N*Real.sqrt (μ.coeff (p+2)) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [blockLp_norm_sq hN,mul_pow,Real.sq_sqrt hNr.le,
    Real.sq_sqrt (μ.nonneg (p+2))]
  exact mul_le_of_le_one_right (mul_nonneg hNr.le (μ.nonneg (p+2)))
    (pow_le_one₀ (div_nonneg (sq_nonneg _) hNr.le) ((div_le_one hNr).2 hx))

theorem summable_blockLp_norm {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (x : Vector N) (hx : ‖x‖^2≤(N:ℝ)) :
    Summable (fun p => ‖blockLp μ p x‖) :=
  (μ.summable_shifted_sqrt.mul_left (Real.sqrt N)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun p => blockLp_norm_le hN μ p x hx)

theorem independent_blocks {N : ℕ} (μ : InfiniteMixture) (x : Vector N) :
    iIndepFun (fun p (J : Disorder N) => block μ p J x) (disorderLaw N) := by
  have h := (independent_degrees N).comp
    (fun p => Real.sqrt (μ.coeff (p+2)) • pureFieldCLM N (p+2) x)
    (fun _ => ContinuousLinearMap.measurable _)
  simpa only [Function.comp_def,smul_apply,smul_eq_mul,pureFieldCLM_apply,block] using h

theorem partialSum_hasGaussianLaw {N : ℕ} (μ : InfiniteMixture) (x : Vector N) (n : ℕ) :
    HasGaussianLaw (fun J : Disorder N => ∑ p∈Finset.range n,block μ p J x)
      (disorderLaw N) := by
  have hi : iIndepFun (fun p : Finset.range n => fun J : Disorder N => block μ p J x)
      (disorderLaw N) := (independent_blocks μ x).precomp Subtype.val_injective
  have h := hi.hasGaussianLaw_fun_sum (fun p : Finset.range n => block_hasGaussianLaw μ p x)
  convert h using 1
  funext J
  exact (Finset.sum_coe_sort (Finset.range n) (fun p => block μ p J x)).symm

end SlowEquilibration.SphericalInfiniteModel

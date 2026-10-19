-- SPDX-License-Identifier: Apache-2.0
module

public import SphericalAging.FiniteModel
public import SphericalAging.SphereInitialLaw
public import SphericalAging.TensorHamiltonianRotation
public import SlowEquilibration.MixtureCurvature
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Covariance

@[expose] public section

/-!
# Actual finite mixed spherical Gaussian fields

The degree blocks are independent genuine ordered Gaussian tensors from the
immutable `all-lean` dependency. Degrees range from two through a fixed finite
maximum, with arbitrary nonnegative coefficients and no parity restriction.
The field is a finite linear combination of these tensors with the manuscript's
normalization. Its Gaussian finite-dimensional laws, smoothness, mean and
covariance are proved against that product disorder measure.

These are the field foundations of `lem:pre-field`. They do not construct a
Parisi minimizer or prove any slow-equilibration estimate.
-/

namespace SlowEquilibration.SphericalModel

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace

abbrev Vector (N : ℕ) := SphericalAging.FiniteModel.Vector N

/-- All allowed degrees in a finite mixture. Both odd and even degrees occur. -/
abbrev Degree (P : ℕ) := {p : Fin (P + 1) // 2 ≤ p.val}

/-- Each degree has its own ordered Gaussian tensor, including repeated indices. -/
abbrev Disorder (N P : ℕ) :=
  (p : Degree P) → SphericalAging.FiniteModel.Disorder N p.val.val

/-- The actual product law of independent degree-specific Gaussian tensors. -/
def disorderLaw (N P : ℕ) : Measure (Disorder N P) :=
  Measure.pi (fun p : Degree P => SphericalAging.FiniteModel.disorderLaw N p.val.val)

instance disorderLaw_probability (N P : ℕ) : IsProbabilityMeasure (disorderLaw N P) := by
  unfold disorderLaw
  infer_instance

/-- The ordinary covariance polynomial of the finite degree family. -/
def covariancePolynomial {P : ℕ} (c : Degree P → ℝ) (r : ℝ) : ℝ :=
  ∑ p : Degree P, c p * r ^ p.val.val

/-- The manuscript's normalized overlap, defined on the ambient Euclidean space. -/
def overlap {N : ℕ} (x y : Vector N) : ℝ := inner ℝ x y / N

/-- The pure tensor Hamiltonian in one degree block, pulled back to the actual product law. -/
def blockField {N P : ℕ} (p : Degree P) (J : Disorder N P) (x : Vector N) : ℝ :=
  SphericalAging.FiniteModel.Hamiltonian N p.val.val (J p) x

/-- The mixed field with amplitude `sqrt(c_p)` in each independent block. -/
def field {N P : ℕ} (c : Degree P → ℝ) (J : Disorder N P) (x : Vector N) : ℝ :=
  ∑ p : Degree P, Real.sqrt (c p) * blockField p J x

theorem independent_degree_blocks (N P : ℕ) :
    iIndepFun (fun p (J : Disorder N P) => J p) (disorderLaw N P) := by
  exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

theorem degree_block_hasLaw {N P : ℕ} (p : Degree P) :
    HasLaw (fun J : Disorder N P => J p)
      (SphericalAging.FiniteModel.disorderLaw N p.val.val) (disorderLaw N P) := by
  exact (measurePreserving_eval
    (fun q : Degree P => SphericalAging.FiniteModel.disorderLaw N q.val.val) p).hasLaw

theorem disorder_hasGaussianLaw (N P : ℕ) :
    HasGaussianLaw (id : Disorder N P → Disorder N P) (disorderLaw N P) := by
  apply (independent_degree_blocks N P).hasGaussianLaw
  intro p
  have : IsGaussian (SphericalAging.FiniteModel.disorderLaw N p.val.val) := by
    have h := SphericalAging.FiniteModel.disorder_hasGaussianLaw N p.val.val
    simpa only [Measure.map_id] using h.isGaussian_map
  exact (degree_block_hasLaw p).hasGaussianLaw

/-- The exact continuous linear functional supplied by one ordered tensor. -/
def pureFieldCLM (N p : ℕ) (x : Vector N) :
    SphericalAging.FiniteModel.Disorder N p →L[ℝ] ℝ :=
  SphericalAging.FiniteModel.normalization N p •
    ∑ I : SphericalAging.FiniteModel.TensorIndex N p,
      SphericalAging.FiniteModel.tensorMonomial x I • ContinuousLinearMap.proj I

@[simp] theorem pureFieldCLM_apply {N p : ℕ}
    (x : Vector N) (J : SphericalAging.FiniteModel.Disorder N p) :
    pureFieldCLM N p x J = SphericalAging.FiniteModel.Hamiltonian N p J x := by
  simp [pureFieldCLM, SphericalAging.FiniteModel.Hamiltonian, mul_comm]

/-- The whole mixed field is an actual continuous linear functional of disorder. -/
def fieldCLM {N P : ℕ} (c : Degree P → ℝ) (x : Vector N) : Disorder N P →L[ℝ] ℝ :=
  ∑ p : Degree P, Real.sqrt (c p) •
    (pureFieldCLM N p.val.val x).comp (ContinuousLinearMap.proj p)

@[simp] theorem fieldCLM_apply {N P : ℕ} (c : Degree P → ℝ)
    (x : Vector N) (J : Disorder N P) : fieldCLM c x J = field c J x := by
  simp [fieldCLM, field, blockField]

theorem field_hasGaussianLaw {N P : ℕ} (c : Degree P → ℝ) (x : Vector N) :
    HasGaussianLaw (fun J : Disorder N P => field c J x) (disorderLaw N P) := by
  simpa using (disorder_hasGaussianLaw N P).map_fun (fieldCLM c x)

/-- Every finite collection of field values is jointly Gaussian, not merely
marginally Gaussian. This is the genuine Gaussian-process property. -/
theorem field_jointGaussian {N P : ℕ} {ι : Type*} [Fintype ι]
    (c : Degree P → ℝ) (x : ι → Vector N) :
    HasGaussianLaw (fun J : Disorder N P => fun i => field c J (x i))
      (disorderLaw N P) := by
  simpa using (disorder_hasGaussianLaw N P).map_fun
    (ContinuousLinearMap.pi (fun i => fieldCLM c (x i)))

theorem blockField_memLp {N P : ℕ} (p : Degree P) (x : Vector N) :
    MemLp (fun J : Disorder N P => blockField p J x) 2 (disorderLaw N P) := by
  exact (SphericalAging.FiniteModel.Hamiltonian_memLp x).comp_measurePreserving
    (measurePreserving_eval _ p)

theorem field_memLp {N P : ℕ} (c : Degree P → ℝ) (x : Vector N) :
    MemLp (fun J : Disorder N P => field c J x) 2 (disorderLaw N P) :=
  (field_hasGaussianLaw c x).memLp_two

theorem blockField_mean {N P : ℕ} (p : Degree P) (x : Vector N) :
    ∫ J : Disorder N P, blockField p J x ∂disorderLaw N P = 0 := by
  simp only [blockField, disorderLaw]
  rw [integral_comp_eval
    (μ := fun q : Degree P => SphericalAging.FiniteModel.disorderLaw N q.val.val)
    (i := p) (f := fun T => SphericalAging.FiniteModel.Hamiltonian N p.val.val T x)
    (SphericalAging.FiniteModel.Hamiltonian_memLp (p := p.val.val) x).aestronglyMeasurable]
  exact SphericalAging.FiniteModel.Hamiltonian_mean x

theorem field_mean {N P : ℕ} (c : Degree P → ℝ) (x : Vector N) :
    ∫ J : Disorder N P, field c J x ∂disorderLaw N P = 0 := by
  unfold field
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, blockField_mean]
    simp
  · intro p _
    exact ((blockField_memLp p x).integrable (by norm_num)).const_mul _

theorem blockField_covariance {N P : ℕ} (hN : 0 < N)
    (p q : Degree P) (x y : Vector N) :
    covariance (fun J : Disorder N P => blockField p J x)
      (fun J => blockField q J y) (disorderLaw N P) =
      if p = q then (N : ℝ) * overlap x y ^ p.val.val else 0 := by
  classical
  by_cases hpq : p = q
  · subst q
    rw [ite_eq_left rfl]
    have hmap : (disorderLaw N P).map (fun J : Disorder N P => J p) =
        SphericalAging.FiniteModel.disorderLaw N p.val.val :=
      (degree_block_hasLaw p).map_eq
    have hcov := covariance_map_fun
      (μ := disorderLaw N P) (Z := fun J : Disorder N P => J p)
      (X := fun J => SphericalAging.FiniteModel.Hamiltonian N p.val.val J x)
      (Y := fun J => SphericalAging.FiniteModel.Hamiltonian N p.val.val J y)
      (by rw [hmap]; exact
        (SphericalAging.FiniteModel.Hamiltonian_memLp x).aestronglyMeasurable)
      (by rw [hmap]; exact
        (SphericalAging.FiniteModel.Hamiltonian_memLp y).aestronglyMeasurable)
      (degree_block_hasLaw p).aemeasurable
    rw [hmap] at hcov
    simp only [blockField]
    rw [← hcov, SphericalAging.FiniteModel.Hamiltonian_probability_covariance hN,
      SphericalAging.FiniteModel.dimension_covariance_scale N p.val.val hN (by omega)]
    rfl
  · rw [ite_eq_right hpq]
    have hmx : Measurable (fun J =>
        SphericalAging.FiniteModel.Hamiltonian N p.val.val J x) := by
      have heq : (fun J => SphericalAging.FiniteModel.Hamiltonian N p.val.val J x) =
          pureFieldCLM N p.val.val x := by
        funext J
        exact (pureFieldCLM_apply x J).symm
      rw [heq]
      exact (pureFieldCLM N p.val.val x).measurable
    have hmy : Measurable (fun J =>
        SphericalAging.FiniteModel.Hamiltonian N q.val.val J y) := by
      have heq : (fun J => SphericalAging.FiniteModel.Hamiltonian N q.val.val J y) =
          pureFieldCLM N q.val.val y := by
        funext J
        exact (pureFieldCLM_apply y J).symm
      rw [heq]
      exact (pureFieldCLM N q.val.val y).measurable
    exact ((independent_degree_blocks N P).indepFun hpq |>.comp hmx hmy).covariance_eq_zero
      (blockField_memLp p x) (blockField_memLp q y)

/-- The exact covariance `N ξ(R(x,y))`, proved under the actual disorder law. -/
theorem field_covariance {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (x y : Vector N) :
    covariance (fun J : Disorder N P => field c J x)
      (fun J => field c J y) (disorderLaw N P) =
      (N : ℝ) * covariancePolynomial c (overlap x y) := by
  classical
  unfold field
  rw [covariance_fun_sum_fun_sum]
  · simp_rw [covariance_const_mul_left, covariance_const_mul_right, blockField_covariance hN]
    simp only [mul_ite, mul_zero]
    unfold covariancePolynomial
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_eq_single p]
    · simp only [ite_true]
      have hsqrt : Real.sqrt (c p) * Real.sqrt (c p) = c p := by
        nlinarith [Real.sq_sqrt (hc p)]
      calc
        _ = (Real.sqrt (c p) * Real.sqrt (c p)) *
            ((N : ℝ) * overlap x y ^ p.val.val) := by ring
        _ = _ := by rw [hsqrt]; ring
    · intro q _ hpq
      simp [Ne.symm hpq]
    · simp
  · intro p
    exact (blockField_memLp p x).const_mul _
  · intro p
    exact (blockField_memLp p y).const_mul _

/-- Every realized finite mixed field is smooth on the ambient space and
hence restricts to a smooth function on the manuscript sphere. -/
theorem field_contDiff {N P : ℕ} (c : Degree P → ℝ) (J : Disorder N P) :
    ContDiff ℝ ⊤ (fun x : Vector N => field c J x) := by
  unfold field blockField
  exact ContDiff.sum (fun p _ =>
    contDiff_const.mul (SphericalAging.FiniteModel.Hamiltonian_contDiff (J p)))

/-- The same covariance written as the actual expectation of a product,
using the proved centering rather than assuming it. -/
theorem field_product_integral {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (x y : Vector N) :
    (∫ J : Disorder N P, field c J x * field c J y ∂disorderLaw N P) =
      (N : ℝ) * covariancePolynomial c (overlap x y) := by
  have h := field_covariance hN c hc x y
  rw [covariance_eq_sub (field_memLp c x) (field_memLp c y)] at h
  simpa only [Pi.mul_apply, field_mean, zero_mul, sub_zero] using h

theorem overlap_self {N : ℕ} (hN : 0 < N) (x : Vector N)
    (hx : ‖x‖ ^ 2 = (N : ℝ)) : overlap x x = 1 := by
  rw [overlap, real_inner_self_eq_norm_sq, hx]
  exact div_self (Nat.cast_ne_zero.mpr hN.ne')

theorem field_variance_on_sphere {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) :
    variance (fun J : Disorder N P => field c J x) (disorderLaw N P) =
      (N : ℝ) * covariancePolynomial c 1 := by
  rw [← covariance_self (field_memLp c x).aemeasurable,
    field_covariance hN c hc, overlap_self hN x hx]

/-- Pointwise Gaussian exponential moment used in the annealed partition
formula. The sphere integral/Fubini step is separate. -/
theorem field_exp_integral_on_sphere {N P : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (x : Vector N)
    (hx : ‖x‖ ^ 2 = (N : ℝ)) (β : ℝ) :
    (∫ J : Disorder N P, Real.exp (β * field c J x) ∂disorderLaw N P) =
      Real.exp ((N : ℝ) * β ^ 2 * covariancePolynomial c 1 / 2) := by
  have hG := field_hasGaussianLaw c x
  change mgf (fun J => field c J x) (disorderLaw N P) β = _
  rw [mgf_gaussianReal ⟨hG.aemeasurable, hG.map_eq_gaussianReal⟩,
    Real.coe_toNNReal _ (variance_nonneg _ _), field_mean,
    field_variance_on_sphere hN c hc x hx]
  congr 1
  ring

/-- The canonical radius-sqrt(N) sphere probability law: the pushforward
of a standard Euclidean Gaussian under radial normalization. -/
abbrev sphereLaw (N : ℕ) : Measure (Vector N) := SphericalAging.SphereInitialLaw.sphereLaw N

theorem sphereLaw_probability (N : ℕ) : IsProbabilityMeasure (sphereLaw N) := by
  infer_instance

/-- Genuine support on the sphere, proved by the radial Gaussian construction. -/
theorem sphereLaw_support {N : ℕ} (hN : 1 ≤ N) :
    ∀ᵐ x ∂sphereLaw N, ‖x‖ ^ 2 = (N : ℝ) :=
  SphericalAging.SphereInitialLaw.sphereLaw_support hN

/-- The sphere law is invariant under every orthogonal map. -/
theorem sphereLaw_rotation_invariant {N : ℕ} (U : Vector N ≃ₗᵢ[ℝ] Vector N) :
    (sphereLaw N).map U = sphereLaw N :=
  SphericalAging.SphereInitialLaw.sphereLaw_rotation_invariant U

/-- Literal orthogonal rotation of every independent tensor block. -/
def rotatedDisorder {N P : ℕ} (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (J : Disorder N P) : Disorder N P :=
  fun p => SphericalAging.TensorHamiltonianRotation.rotatedDisorder U (J p)

theorem rotatedDisorder_measurable {N P : ℕ} (U : Vector N ≃ₗᵢ[ℝ] Vector N) :
    Measurable (rotatedDisorder (P := P) U) := by
  apply Measurable.of_eval
  intro p
  exact (SphericalAging.TensorHamiltonianRotation.rotatedDisorder_measurable U).comp
    (measurable_pi_apply p)

/-- The tensor rotation preserves the genuine product disorder law. -/
theorem rotatedDisorder_hasLaw {N P : ℕ} (U : Vector N ≃ₗᵢ[ℝ] Vector N) :
    HasLaw (rotatedDisorder (P := P) U) (disorderLaw N P) (disorderLaw N P) := by
  refine ⟨(rotatedDisorder_measurable U).aemeasurable, ?_⟩
  unfold rotatedDisorder disorderLaw
  rw [Measure.pi_map_pi (fun p =>
    (SphericalAging.TensorHamiltonianRotation.rotatedDisorder_measurable U).aemeasurable)]
  congr 1
  funext p
  exact (SphericalAging.TensorHamiltonianRotation.rotatedDisorder_hasLaw
    (p := p.val.val) U).map_eq

/-- Pathwise equality for all ambient points, under the law-preserving tensor action. -/
theorem field_rotated {N P : ℕ} (c : Degree P → ℝ)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (J : Disorder N P) (x : Vector N) :
    field c (rotatedDisorder U J) (U x) = field c J x := by
  unfold field blockField rotatedDisorder
  simp_rw [SphericalAging.TensorHamiltonianRotation.Hamiltonian_rotated]

theorem field_precomp_rotation {N P : ℕ} (c : Degree P → ℝ)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (J : Disorder N P) (x : Vector N) :
    field c (rotatedDisorder U J) x = field c J (U.symm x) := by
  simpa using field_rotated c U J (U.symm x)

/-- The random realized field is measurable in the ordinary cylinder
sigma-algebra on real-valued functions. -/
theorem measurable_fieldFunction {N P : ℕ} (c : Degree P → ℝ) :
    Measurable (fun J : Disorder N P => fun x : Vector N => field c J x) := by
  apply Measurable.of_eval
  intro x
  have heq : (fun J : Disorder N P => field c J x) = fieldCLM c x := by
    funext J
    exact (fieldCLM_apply c x J).symm
  rw [heq]
  exact (fieldCLM c x).measurable

/-- The actual random field and its orthogonal precomposition have the same
law, obtained from the literal law-preserving tensor action. -/
theorem field_rotation_sameLaw {N P : ℕ} (c : Degree P → ℝ)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) :
    HasLaw (fun J : Disorder N P => fun x : Vector N => field c J (U.symm x))
      ((disorderLaw N P).map (fun J => fun x : Vector N => field c J x))
      (disorderLaw N P) := by
  have hfield : HasLaw (fun J : Disorder N P => fun x : Vector N => field c J x)
      ((disorderLaw N P).map (fun J => fun x : Vector N => field c J x))
      (disorderLaw N P) :=
    hasLaw_map (measurable_fieldFunction (N := N) c).aemeasurable
  have hrot := hfield.fun_comp (rotatedDisorder_hasLaw (P := P) U)
  apply hrot.congr
  exact Filter.Eventually.of_forall (fun J => by
    funext x
    exact (field_precomp_rotation c U J x).symm)

/-- Restriction of the manuscript's canonical finitely supported coefficients
to the independent degree blocks of the realized field. -/
def mixtureCoefficients (μ : SlowEquilibration.FiniteMixture) :
    Degree μ.maxDegree → ℝ := fun p => μ.coeff p.val.val

theorem mixtureCoefficients_nonnegative (μ : SlowEquilibration.FiniteMixture) :
    ∀ p, 0 ≤ mixtureCoefficients μ p := fun p => μ.nonneg p.val.val

/-- The finite block polynomial is exactly the canonical covariance polynomial;
neither coefficients nor degrees are discarded. -/
theorem covariancePolynomial_mixture (μ : SlowEquilibration.FiniteMixture) (r : ℝ) :
    covariancePolynomial (mixtureCoefficients μ) r = μ.xi r := by
  classical
  have hsupport : μ.coeff.support ⊆ Finset.range (μ.maxDegree + 1) := by
    intro p hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (μ.degree_bounds hp).2)
  have hfilter :
      (∑ p : Fin (μ.maxDegree + 1) with 2 ≤ p.val, μ.coeff p.val * r ^ p.val) =
        ∑ p : Fin (μ.maxDegree + 1), μ.coeff p.val * r ^ p.val := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    split_ifs with h
    · rfl
    · rw [μ.zero_below_two p.val (by omega), zero_mul]
  calc
    covariancePolynomial (mixtureCoefficients μ) r =
        ∑ p : Fin (μ.maxDegree + 1) with 2 ≤ p.val, μ.coeff p.val * r ^ p.val := by
      simpa [covariancePolynomial, mixtureCoefficients, Degree] using
        (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
          (p := fun p : Fin (μ.maxDegree + 1) => 2 ≤ p.val)
          (fun p => μ.coeff p.val * r ^ p.val))
    _ = ∑ p : Fin (μ.maxDegree + 1), μ.coeff p.val * r ^ p.val := hfilter
    _ = ∑ p ∈ Finset.range (μ.maxDegree + 1), μ.coeff p * r ^ p :=
      Fin.sum_univ_eq_sum_range (fun p => μ.coeff p * r ^ p) _
    _ = μ.xi r := by
      exact (Finsupp.sum_of_support_subset μ.coeff hsupport
        (fun p c => c * r ^ p) (by simp)).symm

/-- The actual random Hamiltonian belonging to the manuscript's canonical
finite mixture, with the same coefficients used by the threshold results. -/
def fieldOfMixture {N : ℕ} (μ : SlowEquilibration.FiniteMixture)
    (J : Disorder N μ.maxDegree) (x : Vector N) : ℝ :=
  field (mixtureCoefficients μ) J x

theorem fieldOfMixture_covariance {N : ℕ} (hN : 1 ≤ N)
    (μ : SlowEquilibration.FiniteMixture) (x y : Vector N) :
    cov[fun J => fieldOfMixture μ J x, fun J => fieldOfMixture μ J y;
      disorderLaw N μ.maxDegree] = (N : ℝ) * μ.xi (overlap x y) := by
  simpa [fieldOfMixture, covariancePolynomial_mixture] using
    field_covariance hN (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ) x y

theorem fieldOfMixture_product_integral {N : ℕ} (hN : 1 ≤ N)
    (μ : SlowEquilibration.FiniteMixture) (x y : Vector N) :
    ∫ J, fieldOfMixture μ J x * fieldOfMixture μ J y ∂disorderLaw N μ.maxDegree =
      (N : ℝ) * μ.xi (overlap x y) := by
  simpa [fieldOfMixture, covariancePolynomial_mixture] using
    field_product_integral hN (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ) x y

theorem fieldOfMixture_jointGaussian {N : ℕ} (μ : SlowEquilibration.FiniteMixture)
    {ι : Type*} [Fintype ι] (x : ι → Vector N) :
    HasGaussianLaw (fun J : Disorder N μ.maxDegree => fun i => fieldOfMixture μ J (x i))
      (disorderLaw N μ.maxDegree) :=
  field_jointGaussian (mixtureCoefficients μ) x

theorem fieldOfMixture_mean {N : ℕ} (μ : SlowEquilibration.FiniteMixture) (x : Vector N) :
    ∫ J, fieldOfMixture μ J x ∂disorderLaw N μ.maxDegree = 0 :=
  field_mean (mixtureCoefficients μ) x

theorem fieldOfMixture_contDiff {N : ℕ} (μ : SlowEquilibration.FiniteMixture)
    (J : Disorder N μ.maxDegree) : ContDiff ℝ ⊤ (fieldOfMixture μ J) :=
  field_contDiff (mixtureCoefficients μ) J

theorem fieldOfMixture_rotation_sameLaw {N : ℕ} (μ : SlowEquilibration.FiniteMixture)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) :
    HasLaw (fun J : Disorder N μ.maxDegree =>
        fun x : Vector N => fieldOfMixture μ J (U.symm x))
      ((disorderLaw N μ.maxDegree).map
        (fun J => fun x : Vector N => fieldOfMixture μ J x))
      (disorderLaw N μ.maxDegree) :=
  field_rotation_sameLaw (mixtureCoefficients μ) U

/-- A deterministic tensor operator-norm bound throughout the entire ball,
with the dimension scaling valid for every derivative order. -/
theorem block_iteratedFDeriv_ball_bound {N P : ℕ} (hN : 1 ≤ N)
    (p : Degree P) (J : Disorder N P) (x : Vector N)
    (hx : ‖x‖ ≤ Real.sqrt (N : ℝ)) (n : ℕ) :
    Real.sqrt (N : ℝ) ^ n * ‖iteratedFDeriv ℝ n (blockField p J) x‖ ≤
      (N : ℝ) * (Nat.descFactorial p.val.val n : ℝ) *
        SphericalAging.GaussianLandscape.landscapeNorm N p.val.val (J p) := by
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN0
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have h := SphericalAging.LandscapeDerivatives.Hamiltonian_iteratedFDeriv_norm_le
    (J p) x n
  change ‖iteratedFDeriv ℝ n (blockField p J) x‖ ≤ _ at h
  by_cases hn : n ≤ p.val.val
  · have hp : p.val.val = (p.val.val - 1) + 1 := by omega
    have hscale : SphericalAging.FiniteModel.normalization N p.val.val *
        Real.sqrt (N : ℝ) ^ p.val.val = Real.sqrt (N : ℝ) := by
      calc
        _ = (SphericalAging.FiniteModel.normalization N p.val.val *
            Real.sqrt (N : ℝ) ^ (p.val.val - 1)) * Real.sqrt (N : ℝ) := by
          rw [mul_assoc, ← pow_succ, ← hp]
        _ = _ := by
          rw [SphericalAging.LandscapeDerivatives.normalization_sqrt_power hN0, one_mul]
    have hland : ‖SphericalAging.GaussianLandscape.tensorForm N p.val.val (J p)‖ =
        SphericalAging.GaussianLandscape.landscapeNorm N p.val.val (J p) *
          Real.sqrt (N : ℝ) := by
      unfold SphericalAging.GaussianLandscape.landscapeNorm
      rw [div_mul_cancel₀ _ hs.ne']
    calc
      _ ≤ Real.sqrt (N : ℝ) ^ n *
          (SphericalAging.FiniteModel.normalization N p.val.val *
            (Nat.descFactorial p.val.val n : ℝ) *
            ‖SphericalAging.GaussianLandscape.tensorForm N p.val.val (J p)‖ *
            Real.sqrt (N : ℝ) ^ (p.val.val - n)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs.le n)
        exact h.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg x) hx _)
          (by
            apply mul_nonneg
            · apply mul_nonneg
              · exact Real.rpow_nonneg (Nat.cast_nonneg N) _
              · positivity
            · exact norm_nonneg _))
      _ = (Nat.descFactorial p.val.val n : ℝ) *
          ‖SphericalAging.GaussianLandscape.tensorForm N p.val.val (J p)‖ *
          (SphericalAging.FiniteModel.normalization N p.val.val *
            Real.sqrt (N : ℝ) ^ p.val.val) := by
        have hpow : Real.sqrt (N : ℝ) ^ n * Real.sqrt (N : ℝ) ^ (p.val.val - n) =
            Real.sqrt (N : ℝ) ^ p.val.val := by
          rw [← pow_add, Nat.add_sub_of_le hn]
        calc
          _ = (Nat.descFactorial p.val.val n : ℝ) *
              ‖SphericalAging.GaussianLandscape.tensorForm N p.val.val (J p)‖ *
              SphericalAging.FiniteModel.normalization N p.val.val *
              (Real.sqrt (N : ℝ) ^ n * Real.sqrt (N : ℝ) ^ (p.val.val - n)) := by ring
          _ = _ := by rw [hpow]; ring
      _ = _ := by
        rw [hscale, hland]
        calc
          _ = (Nat.descFactorial p.val.val n : ℝ) *
              SphericalAging.GaussianLandscape.landscapeNorm N p.val.val (J p) *
              Real.sqrt (N : ℝ) ^ 2 := by ring
          _ = _ := by rw [Real.sq_sqrt hNr.le]; ring
  · have hzero : Nat.descFactorial p.val.val n = 0 :=
      Nat.descFactorial_of_lt (by omega)
    simp only [hzero, Nat.cast_zero, mul_zero, zero_mul] at h ⊢
    exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hs.le n) h

/-- The actual mixed derivatives are finite sums of the tensor derivatives. -/
theorem field_iteratedFDeriv {N P : ℕ} (c : Degree P → ℝ)
    (J : Disorder N P) (x : Vector N) (n : ℕ) :
    iteratedFDeriv ℝ n (field c J) x = ∑ p : Degree P,
      Real.sqrt (c p) • iteratedFDeriv ℝ n (blockField p J) x := by
  unfold field
  rw [iteratedFDeriv_fun_sum_apply]
  · apply Finset.sum_congr rfl
    intro p hp
    exact iteratedFDeriv_const_smul_apply' (a := Real.sqrt (c p))
      ((SphericalAging.FiniteModel.Hamiltonian_contDiff (J p)).of_le (by simp)).contDiffAt
  · intro p hp
    exact (((SphericalAging.FiniteModel.Hamiltonian_contDiff (J p)).of_le
      (by simp)).const_smul (Real.sqrt (c p))).contDiffAt

theorem field_iteratedFDeriv_ball_bound {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (J : Disorder N P) (x : Vector N)
    (hx : ‖x‖ ≤ Real.sqrt (N : ℝ)) (n : ℕ) :
    Real.sqrt (N : ℝ) ^ n * ‖iteratedFDeriv ℝ n (field c J) x‖ ≤
      (N : ℝ) * ∑ p : Degree P, Real.sqrt (c p) *
        (Nat.descFactorial p.val.val n : ℝ) *
        SphericalAging.GaussianLandscape.landscapeNorm N p.val.val (J p) := by
  rw [field_iteratedFDeriv]
  calc
    _ ≤ Real.sqrt (N : ℝ) ^ n * ∑ p : Degree P,
        ‖Real.sqrt (c p) • iteratedFDeriv ℝ n (blockField p J) x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ p : Degree P, Real.sqrt (c p) *
        (Real.sqrt (N : ℝ) ^ n * ‖iteratedFDeriv ℝ n (blockField p J) x‖) := by
      simp_rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ ∑ p : Degree P, Real.sqrt (c p) * ((N : ℝ) *
        (Nat.descFactorial p.val.val n : ℝ) *
        SphericalAging.GaussianLandscape.landscapeNorm N p.val.val (J p)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (block_iteratedFDeriv_ball_bound hN p J x hx n)
        (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

/-- Degree-dependent thresholds enlarged to absorb the finite union bound. -/
def blockThreshold {P : ℕ} (p : Degree P) : ℝ :=
  SphericalAging.GaussianLandscape.landscapeThreshold p.val.val +
    4 * ((Fintype.card (Degree P) : ℝ) + 1)

theorem blockThreshold_pos {P : ℕ} (p : Degree P) : 0 < blockThreshold p := by
  unfold blockThreshold
  have h := SphericalAging.GaussianLandscape.landscapeThreshold_pos p.val.val
  positivity

/-- A measurable event defined by the true ordered tensor operator norms. -/
def regularDisorder {N P : ℕ} : Set (Disorder N P) :=
  {J | ∀ p : Degree P,
    SphericalAging.GaussianLandscape.landscapeNorm N p.val.val (J p) ≤ blockThreshold p}

theorem regularDisorder_measurable (N P : ℕ) : MeasurableSet (regularDisorder (N := N) (P := P)) := by
  classical
  unfold regularDisorder
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro p
  exact measurableSet_le
    ((SphericalAging.GaussianLandscape.landscapeNorm_continuous N p.val.val).measurable.comp
      (measurable_pi_apply p)) measurable_const

/-- Every derivative order through three is bounded by this single constant,
depending only on the finite covariance coefficients. -/
def derivativeConstant {P : ℕ} (c : Degree P → ℝ) : ℝ :=
  1 + ∑ p : Degree P, Real.sqrt (c p) * (p.val.val : ℝ) ^ 3 * blockThreshold p

theorem derivativeConstant_pos {P : ℕ} (c : Degree P → ℝ) : 0 < derivativeConstant c := by
  unfold derivativeConstant
  have hsum : 0 ≤ ∑ p : Degree P,
      Real.sqrt (c p) * (p.val.val : ℝ) ^ 3 * blockThreshold p := by
    apply Finset.sum_nonneg
    intro p hp
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by positivity))
      (blockThreshold_pos p).le
  linarith

/-- A simultaneous, dimension-scaled operator norm bound on the entire ball.
Order zero is the field, order one the gradient norm, and orders two and three
are the genuine multilinear Euclidean derivatives. -/
theorem field_regularDisorder_derivatives {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (J : Disorder N P) (hJ : J ∈ regularDisorder)
    (x : Vector N) (hx : ‖x‖ ≤ Real.sqrt (N : ℝ)) (n : ℕ) (hn : n ≤ 3) :
    Real.sqrt (N : ℝ) ^ n * ‖iteratedFDeriv ℝ n (field c J) x‖ ≤
      derivativeConstant c * (N : ℝ) := by
  have hsum : (∑ p : Degree P, Real.sqrt (c p) *
      (Nat.descFactorial p.val.val n : ℝ) *
      SphericalAging.GaussianLandscape.landscapeNorm N p.val.val (J p)) ≤
      derivativeConstant c := by
    apply le_trans (b := ∑ p : Degree P,
      Real.sqrt (c p) * (p.val.val : ℝ) ^ 3 * blockThreshold p)
    · apply Finset.sum_le_sum
      intro p hp
      have hfac : (Nat.descFactorial p.val.val n : ℝ) ≤ (p.val.val : ℝ) ^ 3 := by
        exact_mod_cast (Nat.descFactorial_le_pow p.val.val n).trans
          (pow_le_pow_right' (show 1 ≤ p.val.val by omega) hn)
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hfac (Real.sqrt_nonneg _)
      · exact hJ p
      · exact SphericalAging.GaussianLandscape.landscapeNorm_nonnegative _ _ _
      · positivity
    · unfold derivativeConstant
      linarith
  exact (field_iteratedFDeriv_ball_bound hN c J x hx n).trans
    ((mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg N)).trans_eq (by ring))

/-- The finite union of genuine Gaussian tensor exceptional events has
exponentially small probability, uniformly in every dimension at least two. -/
theorem regularDisorder_failure_probability {N P : ℕ} (hN : 2 ≤ N) :
    (disorderLaw N P).real (regularDisorder (N := N) (P := P))ᶜ ≤
      Real.exp (-(N : ℝ)) := by
  classical
  let m : ℝ := Fintype.card (Degree P)
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hbad : (regularDisorder (N := N) (P := P))ᶜ =
      ⋃ p : Degree P, {J : Disorder N P |
        blockThreshold p < SphericalAging.GaussianLandscape.landscapeNorm N p.val.val (J p)} := by
    ext J
    simp [regularDisorder, not_forall, not_le]
  have hblock (p : Degree P) :
      (disorderLaw N P).real {J : Disorder N P |
        blockThreshold p < SphericalAging.GaussianLandscape.landscapeNorm N p.val.val (J p)} ≤
      2 * Real.exp (-(N : ℝ) * (m + 1) ^ 2) := by
    rw [(degree_block_hasLaw p).measureReal_eq
      (measurableSet_lt measurable_const
        (SphericalAging.GaussianLandscape.landscapeNorm_continuous N p.val.val).measurable)]
    have hthreshold : SphericalAging.GaussianLandscape.landscapeThreshold p.val.val ≤
        blockThreshold p := by
      unfold blockThreshold
      have hm0 : 0 ≤ (Fintype.card (Degree P) : ℝ) := by positivity
      linarith
    have htail := SphericalAging.GaussianLandscape.landscape_tail_dimension
      (N := N) (p := p.val.val) (by omega) (by omega) hthreshold
    have hbase : 0 ≤ SphericalAging.GaussianLandscape.landscapeThreshold p.val.val :=
      (SphericalAging.GaussianLandscape.landscapeThreshold_pos _).le
    have hsq : 16 * (m + 1) ^ 2 ≤ blockThreshold p ^ 2 := by
      dsimp [blockThreshold]
      change 16 * (m + 1) ^ 2 ≤
        (SphericalAging.GaussianLandscape.landscapeThreshold p.val.val + 4 * (m + 1)) ^ 2
      nlinarith [mul_nonneg hbase (show 0 ≤ m + 1 by linarith)]
    exact htail.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hsq)]))
      (by norm_num))
  rw [hbad]
  calc
    _ ≤ ∑ p : Degree P, (disorderLaw N P).real {J : Disorder N P |
        blockThreshold p < SphericalAging.GaussianLandscape.landscapeNorm N p.val.val (J p)} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _p : Degree P, 2 * Real.exp (-(N : ℝ) * (m + 1) ^ 2) :=
      Finset.sum_le_sum (fun p hp => hblock p)
    _ = (2 * m) * Real.exp (-(N : ℝ) * (m + 1) ^ 2) := by simp [m]; ring
    _ ≤ Real.exp (2 * m) * Real.exp (-(N : ℝ) * (m + 1) ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      linarith [Real.add_one_le_exp (2 * m)]
    _ = Real.exp (2 * m - (N : ℝ) * (m + 1) ^ 2) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-(N : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hNr) (sq_nonneg (m + 1)),
        mul_nonneg (sub_nonneg.mpr hNr) hm, sq_nonneg m]

/-- The four Euclidean bounds in `lem:pre-field`, with the actual gradient
and operator norms of the actual second and third derivatives. -/
theorem field_regularDisorder_ball_bounds {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (J : Disorder N P) (hJ : J ∈ regularDisorder)
    (x : Vector N) (hx : ‖x‖ ≤ Real.sqrt (N : ℝ)) :
    |field c J x| ≤ derivativeConstant c * (N : ℝ) ∧
    ‖gradient (field c J) x‖ ≤ derivativeConstant c * Real.sqrt (N : ℝ) ∧
    ‖iteratedFDeriv ℝ 2 (field c J) x‖ ≤ derivativeConstant c ∧
    ‖iteratedFDeriv ℝ 3 (field c J) x‖ ≤ derivativeConstant c / Real.sqrt (N : ℝ) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (show 0 < N by omega)
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hsq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hNr.le
  have hzero := field_regularDisorder_derivatives hN c J hJ x hx 0 (by norm_num)
  have hone := field_regularDisorder_derivatives hN c J hJ x hx 1 (by norm_num)
  have htwo := field_regularDisorder_derivatives hN c J hJ x hx 2 (by norm_num)
  have hthree := field_regularDisorder_derivatives hN c J hJ x hx 3 (by norm_num)
  have hgrad : ‖gradient (field c J) x‖ = ‖iteratedFDeriv ℝ 1 (field c J) x‖ := by
    rw [gradient, LinearIsometryEquiv.norm_map, norm_iteratedFDeriv_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hzero
  · rw [hgrad]
    apply (mul_le_mul_iff_right₀ hs).mp
    calc
      _ ≤ derivativeConstant c * (N : ℝ) := by simpa only [pow_one] using hone
      _ = Real.sqrt (N : ℝ) * (derivativeConstant c * Real.sqrt (N : ℝ)) := by
        calc
          _ = derivativeConstant c * Real.sqrt (N : ℝ) ^ 2 :=
            congrArg (fun z => derivativeConstant c * z) hsq.symm
          _ = _ := by ring
  · rw [hsq] at htwo
    rw [mul_comm (derivativeConstant c) (N : ℝ)] at htwo
    exact (mul_le_mul_iff_right₀ hNr).mp htwo
  · apply (le_div_iff₀ hs).mpr
    apply (mul_le_mul_iff_right₀ hNr).mp
    calc
      _ = Real.sqrt (N : ℝ) ^ 3 * ‖iteratedFDeriv ℝ 3 (field c J) x‖ := by
        calc
          _ = Real.sqrt (N : ℝ) ^ 2 *
              (‖iteratedFDeriv ℝ 3 (field c J) x‖ * Real.sqrt (N : ℝ)) :=
            congrArg (fun z => z * (‖iteratedFDeriv ℝ 3 (field c J) x‖ *
              Real.sqrt (N : ℝ))) hsq.symm
          _ = _ := by ring
      _ ≤ derivativeConstant c * (N : ℝ) := hthree
      _ = _ := by ring

/-- Extrinsic tangent gradient, with the actual orthogonal projection onto
the tangent space of the round sphere. -/
def tangentGradient {N P : ℕ} (c : Degree P → ℝ) (J : Disorder N P)
    (x : Vector N) : Vector N :=
  SphericalAging.LandscapeDerivatives.tangentProjection x (gradient (field c J) x)

/-- The standard extrinsic expression for the intrinsic Hessian of the
realized mixed Hamiltonian on the round sphere. -/
def tangentHessian {N P : ℕ} (c : Degree P → ℝ) (J : Disorder N P)
    (x : Vector N) : Vector N →L[ℝ] Vector N :=
  let π := SphericalAging.LandscapeDerivatives.tangentProjection x
  π.comp ((fderiv ℝ (gradient (field c J)) x).comp π) -
    (inner ℝ x (gradient (field c J) x) / (N : ℝ)) • π

theorem field_regularDisorder_sphere_bounds {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (J : Disorder N P) (hJ : J ∈ regularDisorder)
    (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) :
    ‖tangentGradient c J x‖ ≤ derivativeConstant c * Real.sqrt (N : ℝ) ∧
    ‖tangentHessian c J x‖ ≤ 2 * derivativeConstant c := by
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN0
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hnorm : ‖x‖ = Real.sqrt (N : ℝ) :=
    SphericalAging.LandscapeDerivatives.sphere_norm x hx
  obtain ⟨_, hg, hH, _⟩ := field_regularDisorder_ball_bounds hN c J hJ x hnorm.le
  let π := SphericalAging.LandscapeDerivatives.tangentProjection x
  have hπ : ‖π‖ ≤ 1 := SphericalAging.LandscapeDerivatives.tangentProjection_norm_le hN0 x hx
  have hH' : ‖fderiv ℝ (gradient (field c J)) x‖ ≤ derivativeConstant c := by
    simpa only [SphericalAging.LandscapeDerivatives.gradient_derivative_norm] using hH
  have hradial : |inner ℝ x (gradient (field c J) x) / (N : ℝ)| ≤ derivativeConstant c := by
    rw [abs_div, abs_of_pos hNr]
    apply (div_le_iff₀ hNr).mpr
    calc
      _ ≤ ‖x‖ * ‖gradient (field c J) x‖ := abs_real_inner_le_norm _ _
      _ ≤ Real.sqrt (N : ℝ) * (derivativeConstant c * Real.sqrt (N : ℝ)) := by
        rw [hnorm]
        exact mul_le_mul_of_nonneg_left hg hs.le
      _ = _ := by
        calc
          _ = derivativeConstant c * Real.sqrt (N : ℝ) ^ 2 := by ring
          _ = _ := by rw [Real.sq_sqrt hNr.le]
  have hphp : ‖π.comp ((fderiv ℝ (gradient (field c J)) x).comp π)‖ ≤ derivativeConstant c := by
    calc
      _ ≤ ‖π‖ * ‖(fderiv ℝ (gradient (field c J)) x).comp π‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖(fderiv ℝ (gradient (field c J)) x).comp π‖ :=
        mul_le_of_le_one_left (norm_nonneg _) hπ
      _ ≤ ‖fderiv ℝ (gradient (field c J)) x‖ * ‖π‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ (gradient (field c J)) x‖ :=
        mul_le_of_le_one_right (norm_nonneg _) hπ
      _ ≤ derivativeConstant c := hH'
  have hrπ : ‖(inner ℝ x (gradient (field c J) x) / (N : ℝ)) • π‖ ≤ derivativeConstant c := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg _) hπ).trans hradial
  constructor
  · unfold tangentGradient
    exact ((π.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hπ)).trans hg
  · change ‖π.comp ((fderiv ℝ (gradient (field c J)) x).comp π) -
        (inner ℝ x (gradient (field c J) x) / (N : ℝ)) • π‖ ≤ _
    exact (norm_sub_le _ _).trans ((add_le_add hphp hrπ).trans_eq (by ring))

/-- A literal measurable Gaussian disorder event proving all the regularity
bounds in the manuscript for every finite mixture, including degree two and
odd degrees. The rate `c = 1` is valid with the constants constructed above. -/
theorem pre_field_regularity (μ : SlowEquilibration.FiniteMixture) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 2 ≤ N →
      ∃ A : Set (Disorder N μ.maxDegree), MeasurableSet A ∧
        (disorderLaw N μ.maxDegree).real Aᶜ ≤ Real.exp (-(N : ℝ)) ∧
        (∀ J ∈ A, ∀ x : Vector N, ‖x‖ ≤ Real.sqrt (N : ℝ) →
          |fieldOfMixture μ J x| ≤ K * (N : ℝ) ∧
          ‖gradient (fieldOfMixture μ J) x‖ ≤ K * Real.sqrt (N : ℝ) ∧
          ‖iteratedFDeriv ℝ 2 (fieldOfMixture μ J) x‖ ≤ K ∧
          ‖iteratedFDeriv ℝ 3 (fieldOfMixture μ J) x‖ ≤ K / Real.sqrt (N : ℝ)) ∧
        (∀ J ∈ A, ∀ x : Vector N, ‖x‖ ^ 2 = (N : ℝ) →
          ‖tangentGradient (mixtureCoefficients μ) J x‖ ≤ K * Real.sqrt (N : ℝ) ∧
          ‖tangentHessian (mixtureCoefficients μ) J x‖ ≤ 2 * K) := by
  refine ⟨derivativeConstant (mixtureCoefficients μ),
    derivativeConstant_pos _, ?_⟩
  intro N hN
  refine ⟨regularDisorder, regularDisorder_measurable _ _,
    regularDisorder_failure_probability hN, ?_, ?_⟩
  · intro J hJ x hx
    exact field_regularDisorder_ball_bounds (by omega) _ J hJ x hx
  · intro J hJ x hx
    exact field_regularDisorder_sphere_bounds (by omega) _ J hJ x hx
end
end SlowEquilibration.SphericalModel

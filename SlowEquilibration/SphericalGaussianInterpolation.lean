-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianSpinInterpolation
public import SlowEquilibration.SphericalParisiBound

@[expose] public section

namespace SlowEquilibration.SphericalModel

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The literal tensor feature as a continuous linear functional of the
flattened disorder. -/
def sphereLinear {N P : ℕ} (c : Degree P → ℝ) (x : Vector N) : EuclideanDisorder N P →L[ℝ] ℝ :=
  innerSL ℝ (fieldFeature c x)

theorem fieldFeature_continuous {N P : ℕ} (c : Degree P → ℝ) : Continuous (fieldFeature (N := N) c) := by
  unfold fieldFeature SphericalAging.FiniteModel.tensorMonomial
  fun_prop

theorem sphereLinear_measurable {N P : ℕ} (c : Degree P → ℝ) :
    Measurable (sphereLinear (N := N) c) :=
  ((innerSL ℝ).continuous.comp (fieldFeature_continuous c)).measurable

theorem sphereLinear_apply {N P : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (g : EuclideanDisorder N P) : sphereLinear c x g = field c (unpackDisorder g) x := by
  rw [sphereLinear, innerSL_apply_apply, real_inner_comm, fieldFeature_inner]

theorem sphereLinear_bound {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) : ∀ᵐ x ∂sphereLaw N,
      ‖sphereLinear c x‖ ≤ Real.sqrt ((N : ℝ) * covariancePolynomial c 1) := by
  filter_upwards [sphereLaw_support hN] with x hx
  rw [sphereLinear, innerSL_apply_norm, fieldFeature_norm hN c hc x hx]

theorem gaussianMoment_eq_partition {N P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (g : EuclideanDisorder N P) :
    GaussianSpinInterpolation.moment (sphereLaw N) (fun _ => 1) (sphereLinear c) (β • g) =
      partition N β (field c (unpackDisorder g)) := by
  unfold GaussianSpinInterpolation.moment partition
  apply integral_congr_ae
  exact .of_forall fun x => by
    simp only [GaussianSpinInterpolation.weight, one_mul, map_smul, smul_eq_mul, sphereLinear_apply]

theorem gaussianGibbs_eq_gibbsLaw {N P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (g : EuclideanDisorder N P) :
    GaussianSpinInterpolation.gibbsMeasure (sphereLaw N) (sphereLinear c) (β • g) =
      gibbsLaw N β (field c (unpackDisorder g)) := by
  unfold GaussianSpinInterpolation.gibbsMeasure gibbsLaw gibbsDensity
  simp only [gaussianMoment_eq_partition, map_smul, smul_eq_mul, sphereLinear_apply]

theorem gaussianMeanLogPartition_eq {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (β : ℝ) :
    GaussianSpinInterpolation.averagedLogPartition (sphereLaw N) (sphereLinear c) β =
      ∫ J : Disorder N P, Real.log (partition N β (field c J)) ∂disorderLaw N P := by
  have hm := GaussianSpinInterpolation.logPartition_radial_gaussian_integrable (sphereLaw N) (sphereLinear c)
    (sphereLinear_measurable c) (Real.sqrt_nonneg _) (sphereLinear_bound hN c hc) β
  have h := (euclideanDisorder_hasLaw N P).integral_comp hm.aestronglyMeasurable
  rw [GaussianSpinInterpolation.averagedLogPartition]
  rw [← h]
  apply integral_congr_ae
  exact .of_forall fun J => by
    simp only [Function.comp_apply, GaussianSpinInterpolation.logPartition, gaussianMoment_eq_partition,
      unpack_euclideanDisorder]

/-- Integrability of the physical spherical log partition at every real
inverse temperature, including zero. -/
theorem sphericalLogPartition_integrable {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (β : ℝ) :
    Integrable (fun J : Disorder N P => Real.log (partition N β (field c J))) (disorderLaw N P) := by
  have hm := GaussianSpinInterpolation.logPartition_radial_gaussian_integrable (sphereLaw N) (sphereLinear c)
    (sphereLinear_measurable c) (Real.sqrt_nonneg _) (sphereLinear_bound hN c hc) β
  have h := (euclideanDisorder_hasLaw N P).integrable_comp hm
  convert h using 1
  funext J
  simp only [Function.comp_apply, GaussianSpinInterpolation.logPartition, gaussianMoment_eq_partition,
    unpack_euclideanDisorder]

theorem gaussianMeanLogPartition_eq_quenchedPressure {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) :
    GaussianSpinInterpolation.averagedLogPartition (sphereLaw N) (sphereLinear (mixtureCoefficients μ)) β / (N : ℝ) =
      quenchedPressure N μ β := by
  rw [gaussianMeanLogPartition_eq hN (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ)]
  rfl

/-- The disorder-averaged physical spherical pressure is differentiable.
No thermodynamic limit is assumed to justify this finite-dimensional claim. -/
theorem quenchedPressure_differentiable {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture) :
    Differentiable ℝ (quenchedPressure N μ) := by
  intro β
  have hd := GaussianSpinInterpolation.averagedLogPartition_hasDerivAt (sphereLaw N)
    (sphereLinear (mixtureCoefficients μ)) (sphereLinear_measurable _)
    (Real.sqrt_nonneg _) (sphereLinear_bound hN _ (mixtureCoefficients_nonnegative μ)) β
  have heq : (fun u => GaussianSpinInterpolation.averagedLogPartition (sphereLaw N)
      (sphereLinear (mixtureCoefficients μ)) u / (N : ℝ)) = quenchedPressure N μ :=
    funext (gaussianMeanLogPartition_eq_quenchedPressure hN μ)
  rw [← heq]
  exact (hd.div_const (N : ℝ)).differentiableAt

/-- The exact finite-volume Gaussian interpolation identity, with the
covariance response expressed as variances under the actual sphere Gibbs law. -/
theorem sphericalMeanLogPartition_hasDerivAt_variance {N P : ℕ}
    (hN : 1 ≤ N) (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ) :
    HasDerivAt (fun b => ∫ J : Disorder N P, Real.log (partition N b (field c J)) ∂disorderLaw N P)
      (β * ∑ i : Coordinate N P, ∫ g : EuclideanDisorder N P,
        variance (fun x => sphereLinear c x (EuclideanSpace.single i 1))
          (gibbsLaw N β (field c (unpackDisorder g)))
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N P)) β := by
  classical
  have hb := sphereLinear_bound hN c hc
  have hd := GaussianSpinInterpolation.averagedLogPartition_hasDerivAt_covarianceTrace (sphereLaw N)
    (sphereLinear c) (sphereLinear_measurable c) (Real.sqrt_nonneg _) hb β
  have hF : GaussianSpinInterpolation.averagedLogPartition (sphereLaw N) (sphereLinear c) =
      (fun b => ∫ J : Disorder N P, Real.log (partition N b (field c J)) ∂disorderLaw N P) :=
    funext (gaussianMeanLogPartition_eq hN c hc)
  rw [hF] at hd
  convert hd using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  exact .of_forall fun g => by
    let e : EuclideanDisorder N P := EuclideanSpace.single i 1
    have hρ : Measurable (fun x => sphereLinear c x e) :=
      (ContinuousLinearMap.apply ℝ ℝ e).continuous.measurable.comp (sphereLinear_measurable c)
    have hp : ∀ᵐ x ∂sphereLaw N,
        |sphereLinear c x e| ≤ Real.sqrt ((N : ℝ)*covariancePolynomial c 1) ∧
        ‖sphereLinear c x‖ ≤ Real.sqrt ((N : ℝ)*covariancePolynomial c 1) := by
      filter_upwards [hb] with x hx
      have hh := (sphereLinear c x).le_opNorm e
      have he : ‖e‖ = 1 := by simp [e]
      rw [Real.norm_eq_abs, he, mul_one] at hh
      exact ⟨hh.trans hx, hx⟩
    change variance (fun x => sphereLinear c x e) (gibbsLaw N β (field c (unpackDisorder g))) =
      GaussianSpinInterpolation.expectation (sphereLaw N) (fun x => (sphereLinear c x e)^2) (sphereLinear c) (β • g) -
        (GaussianSpinInterpolation.expectation (sphereLaw N) (fun x => sphereLinear c x e) (sphereLinear c) (β • g))^2
    rw [← gaussianGibbs_eq_gibbsLaw]
    exact (GaussianSpinInterpolation.expectation_variance (sphereLaw N) _ _ hρ (sphereLinear_measurable c) hp (β • g)).symm

/-- The feature Gram matrix is the manuscript covariance kernel, on the
actual ambient vectors. -/
theorem fieldFeature_inner_gram {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (x y : Vector N) :
    inner ℝ (fieldFeature c x) (fieldFeature c y) =
      (N : ℝ) * covariancePolynomial c (overlap x y) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, fieldFeature]
  rw [Fintype.sum_sigma]
  unfold covariancePolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  have hsqrt := Real.sq_sqrt (hc p)
  have hscale := SphericalAging.FiniteModel.dimension_covariance_scale N p.val.val
    (lt_of_lt_of_le Nat.zero_lt_one hN) (by omega : 1 ≤ p.val.val) (inner ℝ x y)
  rw [← SphericalAging.FiniteModel.normalization_sq N p.val.val
    (lt_of_lt_of_le Nat.zero_lt_one hN)] at hscale
  calc
    _ = (Real.sqrt (c p))^2 * SphericalAging.FiniteModel.normalization N p.val.val^2 *
        ∑ I, SphericalAging.FiniteModel.tensorMonomial x I * SphericalAging.FiniteModel.tensorMonomial y I := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I _
      ring
    _ = c p * (SphericalAging.FiniteModel.normalization N p.val.val^2 * (inner ℝ x y)^p.val.val) := by
      rw [hsqrt, SphericalAging.FiniteModel.tensorMonomial_gram]
      ring
    _ = _ := by rw [hscale]; simp only [overlap]; ring

theorem sphereLinear_coordinate {N P : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (i : Coordinate N P) : sphereLinear c x (EuclideanSpace.single i 1) = fieldFeature c x i := by
  rw [sphereLinear, innerSL_apply_apply, EuclideanSpace.inner_single_right]
  simp only [conj_trivial, one_mul]

/-- The literal covariance polynomial evaluated on two independent replicas
drawn from the realized physical Gibbs measure. -/
def replicaCovariance {N P : ℕ} (c : Degree P → ℝ) (β : ℝ) (g : EuclideanDisorder N P) : ℝ :=
  ∫ z : Vector N × Vector N, covariancePolynomial c (overlap z.1 z.2)
    ∂(gibbsLaw N β (field c (unpackDisorder g))).prod (gibbsLaw N β (field c (unpackDisorder g)))

/-- The diagonal covariance minus the genuine independent-replica covariance
is exactly the sum of Gibbs coordinate variances. -/
theorem gibbs_variance_trace_eq_replicaCovariance {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ) (g : EuclideanDisorder N P) :
    (∑ i : Coordinate N P, variance (fun x => sphereLinear c x (EuclideanSpace.single i 1))
      (gibbsLaw N β (field c (unpackDisorder g)))) =
      (N : ℝ)*covariancePolynomial c 1 - (N : ℝ)*replicaCovariance c β g := by
  classical
  let G := gibbsLaw N β (field c (unpackDisorder g))
  have : IsProbabilityMeasure G := gibbsLaw_probability hN β (field_contDiff c _).continuous
  let F : Coordinate N P → Vector N → ℝ := fun i x => fieldFeature c x i
  let K := Real.sqrt ((N : ℝ)*covariancePolynomial c 1)
  have hFm (i : Coordinate N P) : Measurable (F i) :=
    (PiLp.continuous_apply 2 (fun _ : Coordinate N P => ℝ) i |>.comp (fieldFeature_continuous c)).measurable
  have hFb (i : Coordinate N P) : ∀ᵐ x ∂G, ‖F i x‖ ≤ K := by
    filter_upwards [gibbsLaw_support hN β (field c (unpackDisorder g))] with x hx
    exact (PiLp.norm_apply_le (fieldFeature c x) i).trans (by
      rw [fieldFeature_norm hN c hc x hx])
  have hFLp (i : Coordinate N P) : MemLp (F i) 2 G :=
    MemLp.of_bound (hFm i).aestronglyMeasurable K (hFb i)
  have hvar (i : Coordinate N P) :
      variance (F i) G = (∫ x, (F i x)^2 ∂G) - (∫ x, F i x ∂G)^2 := by
    rw [← covariance_self (hFLp i).aemeasurable, covariance_eq_sub (hFLp i) (hFLp i)]
    simp only [Pi.mul_apply, pow_two]
  have hdiag : (∑ i : Coordinate N P, ∫ x, (F i x)^2 ∂G) =
      (N : ℝ)*covariancePolynomial c 1 := by
    rw [← integral_finsetSum Finset.univ (fun i _ => (hFLp i).integrable_sq)]
    have heq : (fun x => ∑ i : Coordinate N P, (F i x)^2) =ᵐ[G]
        fun _ => (N : ℝ)*covariancePolynomial c 1 := by
      filter_upwards [gibbsLaw_support hN β (field c (unpackDisorder g))] with x hx
      rw [← EuclideanSpace.real_norm_sq_eq (fieldFeature c x), fieldFeature_norm_sq hN c hc x hx]
    rw [integral_congr_ae heq]
    simp only [integral_const, probReal_univ, one_smul]
  have hoff : (∑ i : Coordinate N P, (∫ x, F i x ∂G)^2) = (N : ℝ)*replicaCovariance c β g := by
    simp only [pow_two]
    simp_rw [← integral_prod_mul (F _) (F _)]
    rw [← integral_finsetSum Finset.univ (fun i _ =>
      ((hFLp i).integrable (by norm_num)).mul_prod ((hFLp i).integrable (by norm_num)))]
    have heq : (fun z : Vector N × Vector N => ∑ i : Coordinate N P, F i z.1 * F i z.2) =
        fun z => (N : ℝ)*covariancePolynomial c (overlap z.1 z.2) := by
      funext z
      have hgram := fieldFeature_inner_gram hN c hc z.1 z.2
      simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, F, mul_comm] using hgram
    rw [heq, integral_const_mul]
    rfl
  simp only [sphereLinear_coordinate]
  change (∑ i, variance (F i) G) = (N : ℝ)*covariancePolynomial c 1 - (N : ℝ)*replicaCovariance c β g
  simp_rw [hvar]
  rw [Finset.sum_sub_distrib, hdiag, hoff]

theorem spherical_coordinate_variance_integrable {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ) (i : Coordinate N P) :
    Integrable (fun g : EuclideanDisorder N P =>
      variance (fun x => sphereLinear c x (EuclideanSpace.single i 1))
        (gibbsLaw N β (field c (unpackDisorder g))))
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N P)) := by
  classical
  let e : EuclideanDisorder N P := EuclideanSpace.single i 1
  let ρ : Vector N → ℝ := fun x => sphereLinear c x e
  let L : Vector N → EuclideanDisorder N P →L[ℝ] ℝ := sphereLinear c
  let K := Real.sqrt ((N : ℝ)*covariancePolynomial c 1)
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hLm : Measurable L := sphereLinear_measurable c
  have hρ : Measurable ρ := (ContinuousLinearMap.apply ℝ ℝ e).continuous.measurable.comp hLm
  have hb : ∀ᵐ x ∂sphereLaw N, |ρ x| ≤ K ∧ ‖L x‖ ≤ K := by
    filter_upwards [sphereLinear_bound hN c hc] with x hx
    have hh := (L x).le_opNorm e
    have he : ‖e‖ = 1 := by simp [e]
    rw [Real.norm_eq_abs, he, mul_one] at hh
    exact ⟨hh.trans hx, hx⟩
  have hb2 : ∀ᵐ x ∂sphereLaw N, |(ρ x)^2| ≤ K^2 ∧ ‖L x‖ ≤ K := by
    filter_upwards [hb] with x hx
    exact ⟨by simpa only [abs_pow, sq_abs] using
      (sq_le_sq₀ (abs_nonneg (ρ x)) hK).mpr hx.1, hx.2⟩
  have h1c := (GaussianSpinInterpolation.expectation_contDiff (sphereLaw N) ρ L hρ hLm hK hK hb).continuous
  have h2c := (GaussianSpinInterpolation.expectation_contDiff (sphereLaw N) (fun x => (ρ x)^2) L
    (hρ.pow_const 2) hLm (sq_nonneg K) hK hb2).continuous
  have h1b (g : EuclideanDisorder N P) :=
    GaussianSpinInterpolation.norm_expectation_le (sphereLaw N) ρ L hρ hLm hK hb (β • g)
  have h2b (g : EuclideanDisorder N P) :=
    GaussianSpinInterpolation.norm_expectation_le (sphereLaw N) (fun x => (ρ x)^2) L
      (hρ.pow_const 2) hLm (sq_nonneg K) hb2 (β • g)
  have hi1 : Integrable (fun g : EuclideanDisorder N P =>
      (GaussianSpinInterpolation.expectation (sphereLaw N) ρ L (β • g))^2)
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N P)) :=
    Integrable.of_bound ((h1c.comp (continuous_id.const_smul β)).pow 2).aestronglyMeasurable
      (K^2) (.of_forall fun g => by
        rw [norm_pow]
        exact (sq_le_sq₀ (norm_nonneg _) hK).mpr (h1b g))
  have hi2 : Integrable (fun g : EuclideanDisorder N P =>
      GaussianSpinInterpolation.expectation (sphereLaw N) (fun x => (ρ x)^2) L (β • g))
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N P)) :=
    Integrable.of_bound (h2c.comp (continuous_id.const_smul β)).aestronglyMeasurable
      (K^2) (.of_forall h2b)
  apply (hi2.sub hi1).congr
  exact .of_forall fun g => by
    change GaussianSpinInterpolation.expectation (sphereLaw N) (fun x => (ρ x)^2) L (β • g) -
      (GaussianSpinInterpolation.expectation (sphereLaw N) ρ L (β • g))^2 =
      variance ρ (gibbsLaw N β (field c (unpackDisorder g)))
    rw [← gaussianGibbs_eq_gibbsLaw]
    exact GaussianSpinInterpolation.expectation_variance (sphereLaw N) ρ L hρ hLm hb (β • g)

theorem replicaCovariance_gaussian_integrable {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ) :
    Integrable (replicaCovariance c β)
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N P)) := by
  have hi := integrable_finsetSum Finset.univ (fun i _ =>
    spherical_coordinate_variance_integrable hN c hc β i)
  apply ((integrable_const (covariancePolynomial c 1)).sub (hi.div_const (N : ℝ))).congr
  exact .of_forall fun g => by
    have h := gibbs_variance_trace_eq_replicaCovariance hN c hc β g
    have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    change covariancePolynomial c 1 -
      (∑ i : Coordinate N P, variance (fun x => sphereLinear c x (EuclideanSpace.single i 1))
        (gibbsLaw N β (field c (unpackDisorder g)))) / (N : ℝ) = replicaCovariance c β g
    rw [h]
    field_simp
    ring

/-- The standard exact finite-dimensional interpolation identity for the
physical spherical mixed field. The overlap term uses actual Gibbs replicas. -/
theorem sphericalMeanLogPartition_hasDerivAt_replicaCovariance {N P : ℕ}
    (hN : 1 ≤ N) (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ) :
    HasDerivAt (fun b => ∫ J : Disorder N P, Real.log (partition N b (field c J)) ∂disorderLaw N P)
      (β*(N : ℝ)*(covariancePolynomial c 1 -
        ∫ g : EuclideanDisorder N P, replicaCovariance c β g
          ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N P))) β := by
  have hd := sphericalMeanLogPartition_hasDerivAt_variance hN c hc β
  convert hd using 1
  rw [← integral_finsetSum Finset.univ (fun i _ => spherical_coordinate_variance_integrable hN c hc β i),
    integral_congr_ae (.of_forall (gibbs_variance_trace_eq_replicaCovariance hN c hc β))]
  rw [integral_sub (integrable_const _) ((replicaCovariance_gaussian_integrable hN c hc β).const_mul _),
    integral_const_mul]
  simp only [integral_const_mul, integral_const, probReal_univ, one_smul]
  ring

theorem quenchedPressure_hasDerivAt_replicaCovariance {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) :
    HasDerivAt (quenchedPressure N μ)
      (β*(μ.xi 1 - ∫ g : EuclideanDisorder N μ.maxDegree,
        replicaCovariance (mixtureCoefficients μ) β g
          ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree))) β := by
  have hd := (sphericalMeanLogPartition_hasDerivAt_replicaCovariance hN
    (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ) β).div_const (N : ℝ)
  convert hd using 1
  · funext b
    rfl
  · rw [covariancePolynomial_mixture]
    field_simp

theorem quenchedPressure_deriv_replicaCovariance {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) :
    deriv (quenchedPressure N μ) β =
      β*(μ.xi 1 - ∫ g : EuclideanDisorder N μ.maxDegree,
        replicaCovariance (mixtureCoefficients μ) β g
          ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)) :=
  (quenchedPressure_hasDerivAt_replicaCovariance hN μ β).deriv

theorem quenchedPressure_hasDerivAt_variance {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) :
    HasDerivAt (quenchedPressure N μ)
      ((β * ∑ i : Coordinate N μ.maxDegree, ∫ g : EuclideanDisorder N μ.maxDegree,
        variance (fun x => sphereLinear (mixtureCoefficients μ) x (EuclideanSpace.single i 1))
          (gibbsLaw N β (field (mixtureCoefficients μ) (unpackDisorder g)))
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)) / (N : ℝ)) β := by
  have hd := (sphericalMeanLogPartition_hasDerivAt_variance hN
    (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ) β).div_const (N : ℝ)
  convert hd using 1
  funext b
  rfl

theorem quenchedPressure_deriv_nonneg {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 ≤ β) : 0 ≤ deriv (quenchedPressure N μ) β := by
  rw [(quenchedPressure_hasDerivAt_variance hN μ β).deriv]
  apply div_nonneg
  · apply mul_nonneg hβ
    exact Finset.sum_nonneg fun i _ => integral_nonneg fun _ => variance_nonneg _ _
  · exact Nat.cast_nonneg N

/-- Finite-dimensional monotonicity in nonnegative inverse temperature,
deduced from the genuine Gaussian covariance interpolation response. -/
theorem quenchedPressure_monotoneOn {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture) :
    MonotoneOn (quenchedPressure N μ) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (quenchedPressure_differentiable hN μ).continuous.continuousOn
    (quenchedPressure_differentiable hN μ).differentiableOn
  intro β hβ
  exact quenchedPressure_deriv_nonneg hN μ (mem_Ici.mp (interior_subset hβ))

theorem quenchedPressure_nonneg {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    {β : ℝ} (hβ : 0 ≤ β) : 0 ≤ quenchedPressure N μ β := by
  have h := quenchedPressure_monotoneOn hN μ (mem_Ici.mpr (le_refl 0)) (mem_Ici.mpr hβ) hβ
  simpa only [quenchedPressure_zero] using h

theorem quenchedPressure_mem_annealed_interval {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    {β : ℝ} (hβ : 0 ≤ β) : quenchedPressure N μ β ∈ Icc 0 (β^2*μ.xi 1/2) := by
  refine ⟨quenchedPressure_nonneg hN μ hβ, ?_⟩
  rcases hβ.eq_or_lt with hzero | hpos
  · subst β
    simp only [quenchedPressure_zero, zero_pow (by norm_num : 2 ≠ 0), zero_mul, zero_div, le_refl]
  · exact quenchedPressure_le_annealed hN μ hpos

end
end SlowEquilibration.SphericalModel

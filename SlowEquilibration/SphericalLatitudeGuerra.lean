-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitude
public import SlowEquilibration.SphericalGuerraBound

@[expose] public section

/-! Actual finite-volume Guerra interpolation on the affine latitude law.
The tensor field keeps its genuine (n+1)-dimensional disorder; the tangent
linear trial uses independent n-dimensional Gaussian coordinates. -/

namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

abbrev LatitudeGuerraCoordinate (n P : ℕ) := Sum (Coordinate (n+1) P) (Fin n)
abbrev LatitudeGuerraDisorder (n P : ℕ) := EuclideanSpace ℝ (LatitudeGuerraCoordinate n P)

def latitudeGuerraLabel {n P : ℕ} : LatitudeGuerraCoordinate n P → Bool
  | Sum.inl _ => true
  | Sum.inr _ => false

def latitudeGuerraFeature {n P : ℕ} (c : Degree P → ℝ) (β κ : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ)
    (x : Vector n) : LatitudeGuerraDisorder n P :=
  WithLp.toLp 2 (fun i => match i with
    | Sum.inl j => β*fieldFeature c (latitudeMap u e q x) j
    | Sum.inr j => Real.sqrt κ*x j)

def latitudeGuerraLinear {n P : ℕ} (c : Degree P → ℝ) (β κ : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ)
    (x : Vector n) : LatitudeGuerraDisorder n P →L[ℝ] ℝ :=
  innerSL ℝ (latitudeGuerraFeature c β κ u e q x)

theorem latitudeGuerraFeature_continuous {n P : ℕ} (c : Degree P → ℝ) (β κ : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) :
    Continuous (latitudeGuerraFeature c β κ u e q) := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : LatitudeGuerraCoordinate n P => ℝ)).symm.continuous.comp
  apply continuous_pi
  intro i
  cases i with
  | inl j => exact continuous_const.mul ((PiLp.continuous_apply 2 (fun _ : Coordinate (n+1) P => ℝ) j).comp
      ((fieldFeature_continuous c).comp (latitudeMap_continuous u e q)))
  | inr j => exact continuous_const.mul (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j)

theorem latitudeGuerraLinear_measurable {n P : ℕ} (c : Degree P → ℝ) (β κ : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) :
    Measurable (latitudeGuerraLinear c β κ u e q) :=
  ((innerSL ℝ).continuous.comp (latitudeGuerraFeature_continuous c β κ u e q)).measurable

theorem latitudeGuerraFeature_norm_sq {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0)
    {q : ℝ} (hq : |q| ≤ 1) (x : Vector n) (hx : ‖x‖^2=(n : ℝ)) :
    ‖latitudeGuerraFeature c β κ u e q x‖^2 =
      β^2*((n+1 : ℕ) : ℝ)*covariancePolynomial c 1+κ*(n : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [latitudeGuerraFeature, Fintype.sum_sum_type, mul_pow, Real.sq_sqrt hκ]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq,
    ← EuclideanSpace.real_norm_sq_eq, fieldFeature_norm_sq (by omega) c hc _
      (latitudeMap_norm_sq hn u hu e he hq x hx), hx]
  ring

theorem latitudeGuerraLinear_bound {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0)
    {q : ℝ} (hq : |q| ≤ 1) :
    ∀ᵐ x ∂sphereLaw n, ‖latitudeGuerraLinear c β κ u e q x‖ ≤
      Real.sqrt (β^2*((n+1 : ℕ) : ℝ)*covariancePolynomial c 1+κ*(n : ℝ)) := by
  filter_upwards [sphereLaw_support hn] with x hx
  rw [latitudeGuerraLinear, innerSL_apply_norm,
    ← latitudeGuerraFeature_norm_sq hn c hc β hκ u hu e he hq x hx,
    Real.sqrt_sq (norm_nonneg _)]

theorem latitudeGuerra_coordinateObservable {n P : ℕ} (c : Degree P → ℝ) (β κ : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ)
    (x : Vector n) (i : LatitudeGuerraCoordinate n P) :
    GaussianSpinComparison.coordinateObservable (latitudeGuerraLinear c β κ u e q) i x =
      latitudeGuerraFeature c β κ u e q x i := by
  rw [GaussianSpinComparison.coordinateObservable, latitudeGuerraLinear, innerSL_apply_apply,
    EuclideanSpace.inner_single_right]
  simp only [conj_trivial, one_mul]

theorem latitudeGuerra_signedKernel {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0)
    {q : ℝ} (hq : |q| ≤ 1) (x y : Vector n) :
    GaussianSpinComparison.signedKernel (latitudeGuerraLinear c β κ u e q) latitudeGuerraLabel x y =
      κ*(n : ℝ)*overlap x y-β^2*((n+1 : ℕ) : ℝ)*
        covariancePolynomial c (q^2+(1-q^2)*overlap x y) := by
  unfold GaussianSpinComparison.signedKernel
  simp only [latitudeGuerra_coordinateObservable, Fintype.sum_sum_type, GaussianSpinComparison.covarianceSign,
    latitudeGuerraLabel, latitudeGuerraFeature, Bool.false_eq_true, ite_true, ite_false]
  have hm : (∑ i : Coordinate (n+1) P,
      -1*((β*fieldFeature c (latitudeMap u e q x) i)*(β*fieldFeature c (latitudeMap u e q y) i))) =
      -β^2*inner ℝ (fieldFeature c (latitudeMap u e q x)) (fieldFeature c (latitudeMap u e q y)) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hl : (∑ i : Fin n, 1*((Real.sqrt κ*x i)*(Real.sqrt κ*y i))) = κ*inner ℝ x y := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = (Real.sqrt κ)^2*(y i*x i) := by ring
      _ = _ := by rw [Real.sq_sqrt hκ]
  rw [hm, hl, fieldFeature_inner_gram (by omega) c hc, overlap_latitude_pair hn u hu e he hq]
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [overlap]
  field_simp
  ring

theorem latitudeGuerraLinear_rotation_zero {n P : ℕ} (c : Degree P → ℝ) (β κ : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ)
    (x : Vector n) (g : LatitudeGuerraDisorder n P) :
    latitudeGuerraLinear c β κ u e q x (GaussianSpinComparison.rotation latitudeGuerraLabel 0 g) =
      β*field c (unpackDisorder (projectGaussian Sum.inl g)) (latitudeMap u e q x) := by
  rw [latitudeGuerraLinear, innerSL_apply_apply, ← fieldFeature_inner]
  simp [PiLp.inner_apply, RCLike.inner_apply, latitudeGuerraFeature, Fintype.sum_sum_type,
    GaussianSpinComparison.rotation_apply, GaussianSpinComparison.rotationCoefficient, latitudeGuerraLabel,
    projectGaussian, Finset.mul_sum, mul_assoc, mul_comm]

theorem latitudeGuerraLinear_rotation_pi_div_two {n P : ℕ} (c : Degree P → ℝ) (β κ : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ)
    (x : Vector n) (g : LatitudeGuerraDisorder n P) :
    latitudeGuerraLinear c β κ u e q x (GaussianSpinComparison.rotation latitudeGuerraLabel (Real.pi/2) g) =
      Real.sqrt κ*inner ℝ (projectGaussian Sum.inr g) x := by
  rw [latitudeGuerraLinear, innerSL_apply_apply]
  simp [PiLp.inner_apply, RCLike.inner_apply, latitudeGuerraFeature, Fintype.sum_sum_type,
    GaussianSpinComparison.rotation_apply, GaussianSpinComparison.rotationCoefficient, latitudeGuerraLabel,
    projectGaussian, Finset.mul_sum, mul_assoc, mul_comm]

def latitudePhysicalLinear {n P : ℕ} (c : Degree P → ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) (x : Vector n) :
    EuclideanDisorder (n+1) P →L[ℝ] ℝ := sphereLinear c (latitudeMap u e q x)

theorem latitudePhysicalLinear_measurable {n P : ℕ} (c : Degree P → ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) :
    Measurable (latitudePhysicalLinear c u e q) :=
  (sphereLinear_measurable c).comp (latitudeMap_continuous u e q).measurable

theorem latitudePhysicalLinear_bound {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0)
    {q : ℝ} (hq : |q| ≤ 1) :
    ∀ᵐ x ∂sphereLaw n, ‖latitudePhysicalLinear c u e q x‖ ≤
      Real.sqrt (((n+1 : ℕ) : ℝ)*covariancePolynomial c 1) := by
  filter_upwards [sphereLaw_support hn] with x hx
  rw [latitudePhysicalLinear, sphereLinear, innerSL_apply_norm,
    fieldFeature_norm (by omega) c hc _ (latitudeMap_norm_sq hn u hu e he hq x hx)]

theorem latitude_gaussianMoment_eq_partition {n P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ)
    (g : EuclideanDisorder (n+1) P) :
    GaussianSpinInterpolation.moment (sphereLaw n) (fun _ => 1)
      (latitudePhysicalLinear c u e q) (β • g) =
      partitionAgainst (latitudeLaw u e q) β (field c (unpackDisorder g)) := by
  unfold partitionAgainst latitudeLaw
  have hc : Continuous (fun x : Vector (n+1) => Real.exp (β*field c (unpackDisorder g) x)) :=
    Real.continuous_exp.comp ((field_contDiff c (unpackDisorder g)).continuous.const_mul β)
  rw [integral_map (f := fun x : Vector (n+1) => Real.exp (β*field c (unpackDisorder g) x))
    (latitudeMap_continuous u e q).measurable.aemeasurable hc.aestronglyMeasurable]
  unfold GaussianSpinInterpolation.moment
  apply integral_congr_ae
  exact .of_forall fun x => by
    simp only [GaussianSpinInterpolation.weight, one_mul, map_smul, smul_eq_mul,
      latitudePhysicalLinear, sphereLinear_apply]

theorem latitude_gaussianMean_eq {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0)
    {q : ℝ} (hq : |q| ≤ 1) :
    GaussianSpinInterpolation.averagedLogPartition (sphereLaw n) (latitudePhysicalLinear c u e q) β =
      ∫ J : Disorder (n+1) P, Real.log (partitionAgainst (latitudeLaw u e q) β (field c J))
        ∂disorderLaw (n+1) P := by
  have hi := GaussianSpinInterpolation.logPartition_radial_gaussian_integrable (sphereLaw n)
    (latitudePhysicalLinear c u e q) (latitudePhysicalLinear_measurable c u e q)
    (Real.sqrt_nonneg _) (latitudePhysicalLinear_bound hn c hc u hu e he hq) β
  have hh := (euclideanDisorder_hasLaw (n+1) P).integral_comp hi.aestronglyMeasurable
  rw [GaussianSpinInterpolation.averagedLogPartition, ← hh]
  apply integral_congr_ae
  exact .of_forall fun J => by
    simp only [Function.comp_apply, GaussianSpinInterpolation.logPartition,
      latitude_gaussianMoment_eq_partition, unpack_euclideanDisorder]

theorem latitudeGuerraMean_zero_eq_physical {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β κ : ℝ)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0)
    {q : ℝ} (hq : |q| ≤ 1) :
    GaussianSpinComparison.averagedRotatedLogPartition (sphereLaw n)
      (latitudeGuerraLinear c β κ u e q) latitudeGuerraLabel 0 =
      ∫ J : Disorder (n+1) P, Real.log (partitionAgainst (latitudeLaw u e q) β (field c J))
        ∂disorderLaw (n+1) P := by
  let f := fun g : EuclideanDisorder (n+1) P =>
    Real.log (partitionAgainst (latitudeLaw u e q) β (field c (unpackDisorder g)))
  have hi : Integrable f (SYK.standardGaussianMeasureOnEuclidean (Coordinate (n+1) P)) := by
    have hh := GaussianSpinInterpolation.logPartition_radial_gaussian_integrable (sphereLaw n)
      (latitudePhysicalLinear c u e q) (latitudePhysicalLinear_measurable c u e q)
      (Real.sqrt_nonneg _) (latitudePhysicalLinear_bound hn c hc u hu e he hq) β
    convert hh using 1
    funext g
    simp only [f, GaussianSpinInterpolation.logPartition, latitude_gaussianMoment_eq_partition]
  have hm := (projectGaussian_hasLaw
    (Sum.inl : Coordinate (n+1) P → LatitudeGuerraCoordinate n P) Sum.inl_injective).integral_comp
      hi.aestronglyMeasurable
  calc
    _ = ∫ g : LatitudeGuerraDisorder n P, f (projectGaussian Sum.inl g)
        ∂SYK.standardGaussianMeasureOnEuclidean (LatitudeGuerraCoordinate n P) := by
      apply integral_congr_ae
      exact .of_forall fun g => by
        change Real.log (GaussianSpinInterpolation.moment (sphereLaw n) (fun _ => 1)
          (latitudeGuerraLinear c β κ u e q) (GaussianSpinComparison.rotation latitudeGuerraLabel 0 g)) =
          f (projectGaussian Sum.inl g)
        rw [show f (projectGaussian Sum.inl g) = Real.log (GaussianSpinInterpolation.moment (sphereLaw n)
          (fun _ => 1) (latitudePhysicalLinear c u e q) (β • projectGaussian Sum.inl g)) by
            rw [latitude_gaussianMoment_eq_partition]]
        congr 1
        apply integral_congr_ae
        exact .of_forall fun x => by
          simp only [GaussianSpinInterpolation.weight, one_mul, latitudeGuerraLinear_rotation_zero,
            map_smul, smul_eq_mul, latitudePhysicalLinear, sphereLinear_apply]
    _ = ∫ g : EuclideanDisorder (n+1) P, f g
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate (n+1) P) := hm
    _ = _ := by
      rw [← latitude_gaussianMean_eq hn c hc β u hu e he hq]
      apply integral_congr_ae
      exact .of_forall fun g => by
        simp only [f, GaussianSpinInterpolation.logPartition, latitude_gaussianMoment_eq_partition]

theorem latitudeGuerraMean_pi_div_two_eq_linear {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (β : ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) :
    GaussianSpinComparison.averagedRotatedLogPartition (sphereLaw n)
      (latitudeGuerraLinear c β κ u e q) latitudeGuerraLabel (Real.pi/2) =
      (n : ℝ)*linearSphereQuenchedPressure n κ := by
  have hh := (projectGaussian_hasLaw (Sum.inr : Fin n → LatitudeGuerraCoordinate n P)
    Sum.inr_injective).integral_comp (linearSphereLogPartition_integrable hn hκ).aestronglyMeasurable
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [linearSphereQuenchedPressure, mul_div_cancel₀ _ hne]
  calc
    _ = ∫ g : LatitudeGuerraDisorder n P,
        Real.log (partition n 1 (fun x => Real.sqrt κ*inner ℝ (projectGaussian Sum.inr g) x))
        ∂SYK.standardGaussianMeasureOnEuclidean (LatitudeGuerraCoordinate n P) := by
      apply integral_congr_ae
      exact .of_forall fun g => by
        change Real.log (GaussianSpinInterpolation.moment (sphereLaw n) (fun _ => 1)
          (latitudeGuerraLinear c β κ u e q)
          (GaussianSpinComparison.rotation latitudeGuerraLabel (Real.pi/2) g)) =
          Real.log (partition n 1 (fun x => Real.sqrt κ*inner ℝ (projectGaussian Sum.inr g) x))
        congr 1
        apply integral_congr_ae
        exact .of_forall fun x => by
          simp only [GaussianSpinInterpolation.weight, one_mul, latitudeGuerraLinear_rotation_pi_div_two]
    _ = _ := hh

def latitudeQuenchedPressure (n : ℕ) (μ : FiniteMixture) (β : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) : ℝ :=
  (∫ J : Disorder (n+1) μ.maxDegree,
    Real.log (partitionAgainst (latitudeLaw u e q) β (fieldOfMixture μ J))
      ∂disorderLaw (n+1) μ.maxDegree) / ((n+1 : ℕ) : ℝ)

def latitudeLinearVariance (n : ℕ) (μ : FiniteMixture) (β q : ℝ) : ℝ :=
  β^2*((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-q^2)*μ.xi1 q

theorem latitudeLinearVariance_nonneg (n : ℕ) (μ : FiniteMixture) (β : ℝ)
    {q : ℝ} (hq : q ∈ Icc 0 1) : 0 ≤ latitudeLinearVariance n μ β q := by
  have hs : 0 ≤ 1-q^2 := by nlinarith [hq.1, hq.2]
  exact mul_nonneg (mul_nonneg
    (div_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) hs)
    (mixture_first_derivative_nonneg μ hq.1)

theorem latitudeLinearVariance_mul_dim {n : ℕ} (hn : 1 ≤ n) (μ : FiniteMixture) (β q : ℝ) :
    latitudeLinearVariance n μ β q*(n : ℝ) =
      β^2*((n+1 : ℕ) : ℝ)*(1-q^2)*μ.xi1 q := by
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold latitudeLinearVariance
  field_simp

/-- A finite-volume comparison for the genuine latitude pressure. The only
comparison input is a scalar supporting-line inequality for its actual
covariance polynomial; no pressure bound or asymptotic premise is assumed. -/
theorem latitudeQuenchedPressure_le_linearTrial {n : ℕ} (hn : 1 ≤ n)
    (μ : FiniteMixture) (β : ℝ) {q : ℝ} (hq : q ∈ Icc 0 1)
    (htangent : ∀ t ∈ Icc (-1 : ℝ) 1,
      μ.xi q+μ.xi1 q*(q^2+(1-q^2)*t-q) ≤ μ.xi (q^2+(1-q^2)*t))
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0) :
    latitudeQuenchedPressure n μ β u e q ≤
      (n : ℝ)/((n+1 : ℕ) : ℝ)*linearSphereQuenchedPressure n (latitudeLinearVariance n μ β q)+
        β^2/2*(μ.xi 1-μ.xi q-(1-q)*μ.xi1 q) := by
  let κ := latitudeLinearVariance n μ β q
  have hκ : 0 ≤ κ := latitudeLinearVariance_nonneg n μ β hq
  have hqabs : |q| ≤ 1 := abs_le.mpr ⟨by linarith [hq.1], hq.2⟩
  have hdiag : ∀ᵐ x ∂sphereLaw n,
      GaussianSpinComparison.signedKernel
        (latitudeGuerraLinear (mixtureCoefficients μ) β κ u e q) latitudeGuerraLabel x x =
          κ*(n : ℝ)-β^2*((n+1 : ℕ) : ℝ)*μ.xi 1 := by
    filter_upwards [sphereLaw_support hn] with x hx
    rw [latitudeGuerra_signedKernel hn _ (mixtureCoefficients_nonnegative μ) β hκ u hu e he hqabs,
      overlap_self (by omega) x hx, covariancePolynomial_mixture]
    rw [show q^2+(1-q^2)*(1 : ℝ) = 1 by ring, mul_one]
  have hpair : ∀ᵐ z : Vector n × Vector n ∂(sphereLaw n).prod (sphereLaw n),
      GaussianSpinComparison.signedKernel
        (latitudeGuerraLinear (mixtureCoefficients μ) β κ u e q) latitudeGuerraLabel z.1 z.2 ≤
          β^2*((n+1 : ℕ) : ℝ)*((q-q^2)*μ.xi1 q-μ.xi q) := by
    filter_upwards [sphereLaw_prod_support hn] with z hz
    rw [latitudeGuerra_signedKernel hn _ (mixtureCoefficients_nonnegative μ) β hκ u hu e he hqabs,
      covariancePolynomial_mixture, show κ*(n : ℝ) = _ from latitudeLinearVariance_mul_dim hn μ β q]
    have ht := htangent (overlap z.1 z.2) (overlap_mem_Icc_of_norm_sq hn _ _ hz.1 hz.2)
    have hh := mul_le_mul_of_nonneg_left ht
      (mul_nonneg (sq_nonneg β) (Nat.cast_nonneg (n+1)))
    nlinarith
  have hmain := GaussianSpinComparison.gaussian_covariance_comparison (sphereLaw n)
    (latitudeGuerraLinear (mixtureCoefficients μ) β κ u e q)
    (latitudeGuerraLinear_measurable _ β κ u e q) (Real.sqrt_nonneg _)
    (latitudeGuerraLinear_bound hn _ (mixtureCoefficients_nonnegative μ) β hκ u hu e he hqabs)
    latitudeGuerraLabel hdiag hpair
  rw [latitudeGuerraMean_zero_eq_physical hn _ (mixtureCoefficients_nonnegative μ) β κ u hu e he hqabs,
    latitudeGuerraMean_pi_div_two_eq_linear hn _ β hκ u e q] at hmain
  have hN0 : 0 < ((n+1 : ℕ) : ℝ) := by positivity
  have hh := div_le_div_of_nonneg_right hmain hN0.le
  change (∫ J, Real.log (partitionAgainst (latitudeLaw u e q) β
    (field (mixtureCoefficients μ) J)) ∂disorderLaw (n+1) μ.maxDegree) / ((n+1 : ℕ) : ℝ) ≤ _ at hh
  convert hh using 1
  · rfl
  · rw [show κ*(n : ℝ) = β^2*((n+1 : ℕ) : ℝ)*(1-q^2)*μ.xi1 q from
      latitudeLinearVariance_mul_dim hn μ β q]
    field_simp
    ring

end
end SlowEquilibration.SphericalModel

-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitude
public import SlowEquilibration.SphericalGaussianInterpolation

@[expose] public section

/-!
# Genuine latitude feature field for Gaussian interpolation

The bounded measurable feature CLMs below are restrictions of the actual
ordered-tensor field. Their Gaussian averaged log partition is identified
with the physical latitude partition, and their exact Gram kernel is proved.
-/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology InnerProductSpace

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def latitudeLinear {n P : ℕ} (c : Degree P → ℝ) (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) (x : Vector n) :
    EuclideanDisorder (n+1) P →L[ℝ] ℝ := sphereLinear c (latitudeMap u e q x)

theorem latitudeLinear_measurable {n P : ℕ} (c : Degree P → ℝ) (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) :
    Measurable (latitudeLinear c u e q) :=
  (sphereLinear_measurable c).comp (latitudeMap_continuous u e q).measurable

theorem latitudeLinear_apply {n P : ℕ} (c : Degree P → ℝ) (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) (x : Vector n)
    (g : EuclideanDisorder (n+1) P) :
    latitudeLinear c u e q x g = field c (unpackDisorder g) (latitudeMap u e q x) :=
  sphereLinear_apply c _ g

theorem latitudeLinear_bound {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ x, inner ℝ (e x) u=0) {q : ℝ} (hq : |q| ≤ 1) :
    ∀ᵐ x ∂sphereLaw n, ‖latitudeLinear c u e q x‖ ≤
      Real.sqrt (((n+1 : ℕ) : ℝ)*covariancePolynomial c 1) := by
  filter_upwards [sphereLaw_support hn] with x hx
  rw [latitudeLinear,sphereLinear,innerSL_apply_norm,
    fieldFeature_norm (by omega) c hc _ (latitudeMap_norm_sq hn u hu e he hq x hx)]

/-- The actual feature Gram kernel, including its constant and linear parts. -/
theorem latitudeFeature_inner_gram {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ x, inner ℝ (e x) u=0) {q : ℝ} (hq : |q| ≤ 1) (x y : Vector n) :
    inner ℝ (fieldFeature c (latitudeMap u e q x)) (fieldFeature c (latitudeMap u e q y)) =
      ((n+1 : ℕ) : ℝ)*covariancePolynomial c (q^2+(1-q^2)*overlap x y) := by
  rw [fieldFeature_inner_gram (by omega) c hc,overlap_latitude_pair hn u hu e he hq]

theorem latitudeGaussianMoment_eq_partition {n P : ℕ} (c : Degree P → ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q β : ℝ)
    (g : EuclideanDisorder (n+1) P) :
    GaussianSpinInterpolation.moment (sphereLaw n) (fun _ => 1) (latitudeLinear c u e q) (β • g) =
      partitionAgainst (latitudeLaw u e q) β (field c (unpackDisorder g)) := by
  unfold partitionAgainst latitudeLaw
  have hf : Continuous (fun x : Vector (n+1) => Real.exp (β*field c (unpackDisorder g) x)) :=
    Real.continuous_exp.comp (continuous_const.mul (field_contDiff c (unpackDisorder g)).continuous)
  rw [integral_map (latitudeMap_continuous u e q).measurable.aemeasurable hf.aestronglyMeasurable]
  unfold GaussianSpinInterpolation.moment
  apply integral_congr_ae
  exact .of_forall fun x => by
    simp only [GaussianSpinInterpolation.weight,one_mul,map_smul,smul_eq_mul,latitudeLinear_apply]

/-- The interpolation endpoint is the actual physical quenched latitude
pressure under the original tensor-disorder law. -/
theorem latitudeGaussianMeanLogPartition_eq {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ x, inner ℝ (e x) u=0) {q : ℝ} (hq : |q| ≤ 1) (β : ℝ) :
    GaussianSpinInterpolation.averagedLogPartition (sphereLaw n) (latitudeLinear c u e q) β =
      ∫ J : Disorder (n+1) P, Real.log (partitionAgainst (latitudeLaw u e q) β (field c J))
        ∂disorderLaw (n+1) P := by
  have hi := GaussianSpinInterpolation.logPartition_radial_gaussian_integrable (sphereLaw n)
    (latitudeLinear c u e q) (latitudeLinear_measurable c u e q)
    (Real.sqrt_nonneg _) (latitudeLinear_bound hn c hc u hu e he hq) β
  have h := (euclideanDisorder_hasLaw (n+1) P).integral_comp hi.aestronglyMeasurable
  unfold GaussianSpinInterpolation.averagedLogPartition
  rw [← h]
  apply integral_congr_ae
  exact .of_forall fun J => by
    simp only [Function.comp_apply,GaussianSpinInterpolation.logPartition,
      latitudeGaussianMoment_eq_partition,unpack_euclideanDisorder]

end SlowEquilibration.SphericalModel

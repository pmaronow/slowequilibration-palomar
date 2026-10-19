-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlantedShift
public import SlowEquilibration.ConstrainedConcentration

@[expose] public section

/-!
# Actual latitude restrictions of the mixed spherical Gaussian field

A latitude law is constructed by transporting the genuine uniform sphere law
through an orthonormal tangent frame and the affine latitude map. The exact
restricted covariance and planted translation are proved on these points.
The ordinary latitude log partition then inherits the sharp Gaussian tail.
-/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology InnerProductSpace

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A tangent orthonormal frame constructed at every nonzero center. -/
def latitudeTangentFrame {n : ℕ} (u : Vector (n+1)) (hu : u ≠ 0) :
    Vector n →ₗᵢ[ℝ] Vector (n+1) :=
  letI : Fact (Module.finrank ℝ (Vector (n+1))=n+1) := ⟨by simp [Vector,SphericalAging.FiniteModel.Vector]⟩
  ((ℝ ∙ u)ᗮ).subtypeₗᵢ.comp
    (OrthonormalBasis.fromOrthogonalSpanSingleton n hu).repr.symm.toLinearIsometry

theorem latitudeTangentFrame_orthogonal {n : ℕ} (u : Vector (n+1)) (hu : u ≠ 0)
    (x : Vector n) : inner ℝ (latitudeTangentFrame u hu x) u=0 := by
  let : Fact (Module.finrank ℝ (Vector (n+1))=n+1) := ⟨by simp [Vector,SphericalAging.FiniteModel.Vector]⟩
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp
    ((OrthonormalBasis.fromOrthogonalSpanSingleton n hu).repr.symm x).property

/-- A literal latitude in dimension n+1, parametrized by a tangent n-sphere. -/
def latitudeMap {n : ℕ} (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) (x : Vector n) : Vector (n+1) :=
  q • u+Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-q^2)) • e x

theorem latitudeMap_continuous {n : ℕ} (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) : Continuous (latitudeMap u e q) :=
by
  unfold latitudeMap
  fun_prop

/-- The actual normalized latitude measure. -/
def latitudeLaw {n : ℕ} (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) : Measure (Vector (n+1)) :=
  (sphereLaw n).map (latitudeMap u e q)

instance latitudeLaw_probability {n : ℕ} (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) : IsProbabilityMeasure (latitudeLaw u e q) := by
  unfold latitudeLaw
  exact (Measure.isProbabilityMeasure_map_iff (latitudeMap_continuous u e q).measurable.aemeasurable).mpr inferInstance

theorem overlap_latitude_center {n : ℕ} (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ x, inner ℝ (e x) u=0) (q : ℝ) (x : Vector n) :
    overlap (latitudeMap u e q x) u = q := by
  have hN : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [overlap,latitudeMap,inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq,hu,he,
    mul_zero,add_zero]
  exact mul_div_cancel_right₀ q hN

/-- The exact affine overlap identity on a genuine latitude, including the
finite-dimensional normalization from the tangent n-sphere. -/
theorem overlap_latitude_pair {n : ℕ} (hn : 1 ≤ n) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ x, inner ℝ (e x) u=0) {q : ℝ} (hq : |q| ≤ 1) (x y : Vector n) :
    overlap (latitudeMap u e q x) (latitudeMap u e q y) =
      q^2+(1-q^2)*overlap x y := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hN : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hq2 : 0 ≤ 1-q^2 := by nlinarith [abs_le.mp hq]
  have hs : (Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-q^2)))^2 =
      ((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-q^2) := Real.sq_sqrt (by positivity)
  have he' : ∀ x, inner ℝ u (e x)=0 := fun x => by rw [real_inner_comm,he]
  simp only [overlap,latitudeMap,inner_add_left,inner_add_right,real_inner_smul_left,
    real_inner_smul_right,real_inner_self_eq_norm_sq,he,he',e.inner_map_map,
    mul_zero,zero_add,add_zero]
  have hnormq : ‖q • u‖^2 = q^2*((n+1 : ℕ) : ℝ) := by
    simp [norm_smul,mul_pow,Real.norm_eq_abs,hu]
  rw [hnormq]
  have hr : (q^2*((n+1 : ℕ) : ℝ)+
      Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-q^2))*
        (Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-q^2))*inner ℝ x y)) =
      q^2*((n+1 : ℕ) : ℝ)+
        (Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-q^2)))^2*inner ℝ x y := by ring
  rw [hr,hs]
  field_simp

theorem latitudeMap_norm_sq {n : ℕ} (hn : 1 ≤ n) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ x, inner ℝ (e x) u=0) {q : ℝ} (hq : |q| ≤ 1)
    (x : Vector n) (hx : ‖x‖^2=(n : ℝ)) :
    ‖latitudeMap u e q x‖^2=((n+1 : ℕ) : ℝ) := by
  have h := overlap_latitude_pair hn u hu e he hq x x
  rw [overlap_self (by omega) x hx] at h
  simp only [overlap,real_inner_self_eq_norm_sq] at h
  have hN : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  apply (div_eq_one_iff_eq hN).mp
  convert h using 1; ring

theorem latitudeLaw_support {n : ℕ} (hn : 1 ≤ n) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ x, inner ℝ (e x) u=0) {q : ℝ} (hq : |q| ≤ 1) :
    ∀ᵐ v ∂latitudeLaw u e q, ‖v‖^2=((n+1 : ℕ) : ℝ) ∧ overlap v u=q := by
  unfold latitudeLaw
  apply (ae_map_iff (latitudeMap_continuous u e q).measurable.aemeasurable (by
    exact (isClosed_eq (continuous_norm.pow 2) continuous_const).measurableSet.inter
      (by
        exact (isClosed_eq ((continuous_id.inner continuous_const).div_const ((n+1 : ℕ) : ℝ))
          continuous_const).measurableSet))).mpr
  filter_upwards [sphereLaw_support hn] with x hx
  exact ⟨latitudeMap_norm_sq hn u hu e he hq x hx,overlap_latitude_center u hu e he q x⟩

/-- The actual latitude restriction has the covariance used in HS (3.2). -/
theorem latitude_field_product_integral {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ x, inner ℝ (e x) u=0) {q : ℝ} (hq : |q| ≤ 1) (x y : Vector n) :
    (∫ J : Disorder (n+1) P, field c J (latitudeMap u e q x)*field c J (latitudeMap u e q y)
      ∂disorderLaw (n+1) P) =
      ((n+1 : ℕ) : ℝ)*covariancePolynomial c (q^2+(1-q^2)*overlap x y) := by
  rw [field_product_integral (by omega) c hc,overlap_latitude_pair hn u hu e he hq]

/-- The planted latitude field has a deterministic constant shift, proved
from the actual disorder covariance translation. -/
theorem latitude_field_add_plantedShift {n P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (β : ℝ) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ x, inner ℝ (e x) u=0) (q : ℝ) (x : Vector n) (J : Disorder (n+1) P) :
    field c (J+plantedShift c β u) (latitudeMap u e q x) =
      field c J (latitudeMap u e q x)+β*((n+1 : ℕ) : ℝ)*covariancePolynomial c q := by
  rw [field_add_plantedShift (by omega) c hc β u,overlap_latitude_center u hu e he]

/-- The exact planted normalization of the literal latitude partition. -/
theorem latitude_partition_plantedShift {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ x, inner ℝ (e x) u=0) {q : ℝ} (hq : |q| ≤ 1) (J : Disorder (n+1) P) :
    partitionAgainst (latitudeLaw u e q) β (field c (J+plantedShift c β u)) =
      Real.exp (β^2*((n+1 : ℕ) : ℝ)*covariancePolynomial c q)*
        partitionAgainst (latitudeLaw u e q) β (field c J) := by
  unfold partitionAgainst
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [latitudeLaw_support hn u hu e he hq] with v hv
  rw [field_add_plantedShift (by omega) c hc β u v J,hv.2,← Real.exp_add]
  congr 1
  ring

/-- Planting adds precisely beta² xi(q) to the normalized latitude pressure. -/
theorem latitude_logPartition_plantedShift {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ) (u : Vector (n+1))
    (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ x, inner ℝ (e x) u=0) {q : ℝ} (hq : |q| ≤ 1) (J : Disorder (n+1) P) :
    Real.log (partitionAgainst (latitudeLaw u e q) β (field c (J+plantedShift c β u))) =
      β^2*((n+1 : ℕ) : ℝ)*covariancePolynomial c q+
        Real.log (partitionAgainst (latitudeLaw u e q) β (field c J)) := by
  have hpos := partitionAgainst_pos (latitudeLaw u e q)
    ((latitudeLaw_support hn u hu e he hq).mono (fun _ hx => hx.1)) β (field_contDiff c J).continuous
  rw [latitude_partition_plantedShift hn c hc β u hu e he hq J,
    Real.log_mul (Real.exp_pos _).ne' hpos.ne',Real.log_exp]

/-- Sharp actual disorder concentration for the literal latitude log partition. -/
theorem latitude_logPartition_concentration {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (hcov : 0 < covariancePolynomial c 1)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0)
    {q β t : ℝ} (hq : |q| ≤ 1) (hβ : 0 < β) (ht : 0 < t) :
    disorderLaw (n+1) P {J | t*((n+1 : ℕ) : ℝ) ≤
      |Real.log (partitionAgainst (latitudeLaw u e q) β (field c J))-
        (∫ K, Real.log (partitionAgainst (latitudeLaw u e q) β (field c K)) ∂disorderLaw (n+1) P)|} ≤
      ENNReal.ofReal (2*Real.exp (-(t^2*((n+1 : ℕ) : ℝ))/(2*β^2*covariancePolynomial c 1))) :=
  logPartitionAgainst_pressure_concentration (by omega) (latitudeLaw u e q)
    ((latitudeLaw_support hn u hu e he hq).mono (fun _ hx => hx.1)) c hc hcov hβ ht

end SlowEquilibration.SphericalModel

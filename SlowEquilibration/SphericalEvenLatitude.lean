-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlantedPoleUpper
public import SlowEquilibration.SphericalLatitudeTransport

@[expose] public section

/-!
# Exact antipodal symmetry of actual even-mixture latitude partitions

Evenness is proved term by term for the actual ordered tensor realization.
True sphere rotation invariance then identifies the two antipodal latitude
partitions and their exact sampled planted profiles.
-/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators ENNReal

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem tensorMonomial_neg_of_even {N p : ℕ} (hp : Even p) (x : Vector N)
    (I : SphericalAging.FiniteModel.TensorIndex N p) :
    SphericalAging.FiniteModel.tensorMonomial (-x) I =
      SphericalAging.FiniteModel.tensorMonomial x I := by
  simp only [SphericalAging.FiniteModel.tensorMonomial,PiLp.neg_apply,Finset.prod_neg,
    Finset.card_univ,Fintype.card_fin,hp.neg_one_pow,one_mul]

/-- Antipodal symmetry of every actual realization of an even mixture. -/
theorem fieldOfMixture_neg_of_even {N : ℕ} (μ : FiniteMixture)
    (heven : ∀ p ∈ μ.coeff.support, Even p) (J : Disorder N μ.maxDegree) (x : Vector N) :
    field (mixtureCoefficients μ) J (-x) = field (mixtureCoefficients μ) J x := by
  unfold field
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : μ.coeff p.val.val = 0
  · simp [mixtureCoefficients,hp]
  · have hpe := heven p.val.val (Finsupp.mem_support_iff.mpr hp)
    unfold blockField SphericalAging.FiniteModel.Hamiltonian
    simp only [tensorMonomial_neg_of_even hpe]

theorem latitudeMap_antipodal {n : ℕ} (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) (x : Vector n) :
    latitudeMap u e (-q) (-x) = -(latitudeMap u e q x) := by
  unfold latitudeMap
  rw [neg_sq,map_neg]
  module

theorem latitudePartition_neg_eq_of_even {n : ℕ} (μ : FiniteMixture)
    (heven : ∀ p ∈ μ.coeff.support, Even p) (β : ℝ) (J : Disorder (n+1) μ.maxDegree)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) :
    partitionAgainst (latitudeLaw u e (-q)) β (field (mixtureCoefficients μ) J) =
      partitionAgainst (latitudeLaw u e q) β (field (mixtureCoefficients μ) J) := by
  let U : Vector n ≃ₗᵢ[ℝ] Vector n := LinearIsometryEquiv.neg ℝ
  let F : Vector n → ℝ := fun x => Real.exp (β*field (mixtureCoefficients μ) J (latitudeMap u e (-q) x))
  have hF : Continuous F := Real.continuous_exp.comp (continuous_const.mul
    ((field_contDiff (mixtureCoefficients μ) J).continuous.comp (latitudeMap_continuous u e (-q))))
  have hmap := integral_map (μ := sphereLaw n) U.continuous.measurable.aemeasurable hF.aestronglyMeasurable
  rw [sphereLaw_rotation_invariant U] at hmap
  rw [latitudePartition_eq_sphereIntegral,latitudePartition_eq_sphereIntegral]
  change (∫ x, F x ∂sphereLaw n) = _
  rw [hmap]
  apply integral_congr_ae
  exact .of_forall fun x => by
    change Real.exp (β*field (mixtureCoefficients μ) J (latitudeMap u e (-q) (-x))) = _
    rw [latitudeMap_antipodal,fieldOfMixture_neg_of_even μ heven]

/-- The literal sampled planted profile of an even realization is
antipodally symmetric, including its exact finite-dimensional entropy. -/
theorem plantedLatitudeProfile_neg_of_even {n : ℕ} (μ : FiniteMixture)
    (heven : ∀ p ∈ μ.coeff.support, Even p) (β : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ)
    (J : Disorder (n+1) μ.maxDegree) :
    plantedLatitudeProfile n μ β u e (-q) J = plantedLatitudeProfile n μ β u e q J := by
  unfold plantedLatitudeProfile
  rw [latitudePartition_neg_eq_of_even μ heven,neg_sq]

end SlowEquilibration.SphericalModel

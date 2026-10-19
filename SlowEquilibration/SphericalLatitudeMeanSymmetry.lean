-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlantedProfile
public import SlowEquilibration.SphericalLatitudeRegularity
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Genuine mean latitude reflection for arbitrary spin parity

Reflection in the pole's orthogonal complement reverses the center and fixes
the tangent frame. The actual tensor action preserves the genuine Gaussian
disorder law. Consequently centered quenched latitude pressure is even in q
for every finite mixture, without assuming that its covariance is even.
-/

namespace SlowEquilibration.SphericalModel

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

def latitudePoleReflection {n : ℕ} (u : Vector (n+1)) :
    Vector (n+1) ≃ₗᵢ[ℝ] Vector (n+1) := (ℝ ∙ u)ᗮ.reflection

theorem latitudePoleReflection_pole {n : ℕ} (u : Vector (n+1)) :
    latitudePoleReflection u u = -u :=
  Submodule.reflection_orthogonalComplement_singleton_eq_neg u

theorem latitudePoleReflection_frame {n : ℕ} (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0) (x : Vector n) :
    latitudePoleReflection u (e x) = e x := by
  apply Submodule.reflection_mem_subspace_eq_self
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr (he x)

theorem latitudePoleReflection_latitudeMap {n : ℕ} (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0)
    (q : ℝ) (x : Vector n) :
    latitudePoleReflection u (latitudeMap u e q x) = latitudeMap u e (-q) x := by
  simp only [latitudeMap, map_add, map_smul, latitudePoleReflection_pole,
    latitudePoleReflection_frame u e he x, neg_sq, smul_neg, neg_smul]

/-- Actual joint measurability suffices for the law-preserving partition
change of variables, without any symmetry or optimality premise. -/
theorem latitudeLogPartition_measurable {n P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) :
    Measurable (latitudeLogPartition c β u e q) := by
  have hm : Measurable (fun z : Vector (n+1) × Disorder (n+1) P => field c z.2 z.1) := by
    change Measurable (Function.uncurry
      (fun (x : Vector (n+1)) (J : Disorder (n+1) P) => field c J x))
    apply measurable_uncurry_of_continuous_of_measurable
      (u := fun (x : Vector (n+1)) (J : Disorder (n+1) P) => field c J x)
    · intro J
      exact (field_contDiff c J).continuous
    · intro x
      have heq : (fun J : Disorder (n+1) P => field c J x) = fieldCLM c x := by
        funext J
        exact (fieldCLM_apply c x J).symm
      rw [heq]
      exact (fieldCLM c x).measurable
  have hf : Measurable (fun z : Disorder (n+1) P × Vector (n+1) =>
      Real.exp (β*field c z.1 z.2)) := (hm.comp measurable_swap).const_mul β |>.exp
  have hi := hf.stronglyMeasurable.integral_prod_right' (ν := latitudeLaw u e q)
  exact hi.measurable.log

theorem latitudeLogPartition_reflected_disorder {n P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ x, inner ℝ (e x) u=0) (q : ℝ) (J : Disorder (n+1) P) :
    latitudeLogPartition c β u e (-q) (rotatedDisorder (latitudePoleReflection u) J) =
      latitudeLogPartition c β u e q J := by
  unfold latitudeLogPartition
  congr 1
  rw [latitudePartition_eq_sphereIntegral, latitudePartition_eq_sphereIntegral]
  apply integral_congr_ae
  exact .of_forall fun x => by
    dsimp only
    rw [← latitudePoleReflection_latitudeMap u e he q x, field_rotated]

/-- Centered latitude quenched pressure is genuinely even for every finite
mixture, including mixtures with arbitrary odd degrees. -/
theorem latitudeQuenchedPressure_neg {n : ℕ} (μ : FiniteMixture) (β : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ x, inner ℝ (e x) u=0) (q : ℝ) :
    latitudeQuenchedPressure n μ β u e (-q) = latitudeQuenchedPressure n μ β u e q := by
  have hm : AEStronglyMeasurable (latitudeLogPartition (mixtureCoefficients μ) β u e (-q))
      (disorderLaw (n+1) μ.maxDegree) :=
    (latitudeLogPartition_measurable (mixtureCoefficients μ) β u e (-q)).aestronglyMeasurable
  have h := (rotatedDisorder_hasLaw (P := μ.maxDegree) (latitudePoleReflection u)).integral_comp hm
  dsimp only [Function.comp_def] at h
  have heq := integral_congr_ae (μ := disorderLaw (n+1) μ.maxDegree)
    (.of_forall fun J => latitudeLogPartition_reflected_disorder (mixtureCoefficients μ) β u e he q J)
  rw [heq] at h
  unfold latitudeQuenchedPressure fieldOfMixture
  change (∫ J, latitudeLogPartition (mixtureCoefficients μ) β u e (-q) J
    ∂disorderLaw (n+1) μ.maxDegree)/((n+1 : ℕ) : ℝ) =
      (∫ J, latitudeLogPartition (mixtureCoefficients μ) β u e q J
        ∂disorderLaw (n+1) μ.maxDegree)/((n+1 : ℕ) : ℝ)
  rw [h]

theorem latitudeQuenchedPressure_abs {n : ℕ} (μ : FiniteMixture) (β : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ x, inner ℝ (e x) u=0) (q : ℝ) :
    latitudeQuenchedPressure n μ β u e |q| = latitudeQuenchedPressure n μ β u e q := by
  rcases le_or_gt 0 q with hq | hq
  · rw [abs_of_nonneg hq]
  · rw [abs_of_neg hq, latitudeQuenchedPressure_neg μ β u e he q]

/-- Nonnegative polynomial coefficients compare the two overlap signs
without assuming parity. -/
theorem mixture_xi_neg_le (μ : FiniteMixture) {q : ℝ} (hq : 0 ≤ q) : μ.xi (-q) ≤ μ.xi q := by
  unfold FiniteMixture.xi
  apply Finset.sum_le_sum
  intro p hp
  apply mul_le_mul_of_nonneg_left _ (μ.nonneg p)
  calc
    (-q)^p ≤ |(-q)^p| := le_abs_self _
    _ = q^p := by rw [abs_pow, abs_neg, abs_of_nonneg hq]

/-- The literal planted mean profile at a negative overlap is bounded by
its positive counterpart for every canonical mixture. -/
theorem plantedLatitudeMeanProfile_neg_le {n : ℕ} (hn : 1 ≤ n)
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    plantedLatitudeMeanProfile n μ β u e (-q) ≤ plantedLatitudeMeanProfile n μ β u e q := by
  have hqabs : |q| ≤ 1 := by rw [abs_of_nonneg hq.1]; exact hq.2
  have hnqabs : |-q| ≤ 1 := by simpa only [abs_neg] using hqabs
  unfold plantedLatitudeMeanProfile
  rw [plantedLatitudeQuenchedPressure_eq hn μ hβ u hu e he hnqabs,
    plantedLatitudeQuenchedPressure_eq hn μ hβ u hu e he hqabs,
    latitudeQuenchedPressure_neg μ β u e he q, neg_sq]
  have h := mul_le_mul_of_nonneg_left (mixture_xi_neg_le μ hq.1) (sq_nonneg β)
  linarith

/-- Every admissible overlap is dominated by its nonnegative absolute
overlap at the level of the actual planted mean profile. -/
theorem plantedLatitudeMeanProfile_le_abs {n : ℕ} (hn : 1 ≤ n)
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x, inner ℝ (e x) u=0)
    {q : ℝ} (hq : |q| ≤ 1) :
    plantedLatitudeMeanProfile n μ β u e q ≤ plantedLatitudeMeanProfile n μ β u e |q| := by
  rcases le_or_gt 0 q with hq0 | hq0
  · rw [abs_of_nonneg hq0]
  · have hqn : -q ∈ Icc (0 : ℝ) 1 := by
      constructor
      · linarith
      · simpa only [abs_of_neg hq0] using hq
    rw [abs_of_neg hq0]
    simpa only [neg_neg] using plantedLatitudeMeanProfile_neg_le hn μ hβ u hu e he hqn

end
end SlowEquilibration.SphericalModel

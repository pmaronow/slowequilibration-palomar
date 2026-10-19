-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeCubeRegularity
public import SlowEquilibration.GaussianThreeBlockReplicaError
public import SlowEquilibration.GaussianIndependentBankPositivity

@[expose] public section

/-! # Genuine uniform positivity of the actual latitude three-bank Gibbs law

The original/trial Gaussian coordinates and held tensor bank are literal.
Their coefficient map, normalized Gibbs law, sphere radius and cube average
are identified internally with the proved independent-bank positivity model.
-/
namespace SlowEquilibration.SphericalModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalPositivePerturbation GaussianSpinInterpolation
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n P K : ℕ}

def latitudeCubeRealization (n P K : ℕ) (θ : ℝ)
    (z : (Fin K → ℝ) × LatitudeThreeDisorder n P (TensorCoordinate n K)) :
    LatitudeThreeDisorder n P (TensorCoordinate n K) :=
  GaussianThreeBlockComparison.rotation latitudeThreeLabel θ (latitudeCubeOperator z.1 z.2)

theorem latitudeCubeRealization_continuous (n P K : ℕ) (θ : ℝ) :
    Continuous (latitudeCubeRealization n P K θ) :=
  (GaussianThreeBlockComparison.rotation latitudeThreeLabel θ).continuous.comp
    (latitudeCubeOperator_joint_continuous n P K)

/-- Equality of the actual normalized Gibbs laws under the literal cube
coordinate map. It uses ordinary pointwise exponent equality only. -/
theorem latitudePositivity_gibbs_cube (c : Degree P → ℝ) (β κ : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q v θ : ℝ)
    (cube : Fin K → ℝ) (D : LatitudeThreeDisorder n P (TensorCoordinate n K)) :
    gibbsMeasure (sphereLaw n)
      (GaussianThreeBlockComparison.rotatedLinear
        (latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v cube)) latitudeThreeLabel θ) D=
      gibbsMeasure (sphereLaw n)
        (latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v (fun _ => 1)))
        (latitudeCubeRealization n P K θ (cube,D)) := by
  apply gibbsMeasure_congr_field
  exact .of_forall fun x => by
    rw [GaussianThreeBlockComparison.rotatedLinear,ContinuousLinearMap.comp_apply,
      latitudeThreeLinear_positivity_cube,← latitudeCubeOperator_rotation]
    rfl

theorem latitudePositivity_pairMass_cube (c : Degree P → ℝ) (β κ : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q v θ : ℝ)
    (cube : Fin K → ℝ) (D : LatitudeThreeDisorder n P (TensorCoordinate n K))
    (E : Set (Vector n × Vector n)) :
    GaussianThreeBlockComparison.pairEventMass (sphereLaw n)
      (latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v cube)) latitudeThreeLabel θ E D=
      realizedPairMass (sphereLaw n)
        (latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v (fun _ => 1)))
        (latitudeCubeRealization n P K θ) E (cube,D) := by
  unfold GaussianThreeBlockComparison.pairEventMass realizedPairMass
  rw [latitudePositivity_gibbs_cube]

/-- Actual cube-averaged Gaussian replica-event masses are integrable,
with their domination by one derived from the true Gibbs probability. -/
theorem latitudePositivity_meanEventMass_integrable (hn : 1 ≤ n) (c : Degree P → ℝ) (β κ : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q v θ : ℝ)
    (E : Set (Vector n × Vector n)) (hE : MeasurableSet E) :
    Integrable (fun cube : Fin K → ℝ => ∫D,
      GaussianThreeBlockComparison.pairEventMass (sphereLaw n)
        (latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v cube)) latitudeThreeLabel θ E D
      ∂SYK.standardGaussianMeasureOnEuclidean (LatitudeThreeCoordinate n P (TensorCoordinate n K)))
      (positiveCubeLaw K) := by
  let T := latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v (fun _ => 1))
  obtain ⟨B,hB,hbound⟩ := exists_latitudeThreeLinear_sphere_bound c β κ u e q
    (latitudePositivityFeature n K v (fun _ => 1)) (latitudePositivityFeature_continuous n K v _)
  have hTb : ∀ᵐ x ∂sphereLaw n,‖T x‖ ≤ B := (sphereLaw_support hn).mono fun x hx => hbound x hx
  have hT : Measurable T := (latitudeThreeLinear_continuous c β κ u e q _
    (latitudePositivityFeature_continuous n K v _)).measurable
  let F := realizedPairMass (sphereLaw n) T (latitudeCubeRealization n P K θ) E
  have hF : Measurable F := realizedPairMass_measurable (sphereLaw n) T hT hB hTb _
    (latitudeCubeRealization_continuous n P K θ).measurable E hE
  have hm := hF.stronglyMeasurable.integral_prod_right'
    (ν := SYK.standardGaussianMeasureOnEuclidean (LatitudeThreeCoordinate n P (TensorCoordinate n K))) |>.measurable
  have hboundF (cube : Fin K → ℝ) :
      ‖∫D,F (cube,D) ∂SYK.standardGaussianMeasureOnEuclidean
        (LatitudeThreeCoordinate n P (TensorCoordinate n K))‖ ≤ 1 := by
    have hh := norm_integral_le_of_norm_le_const
      (μ := SYK.standardGaussianMeasureOnEuclidean (LatitudeThreeCoordinate n P (TensorCoordinate n K)))
      (.of_forall fun D => realizedPairMass_norm_le_one (sphereLaw n) T hT hTb (latitudeCubeRealization n P K θ) E (cube,D))
    simpa only [probReal_univ,mul_one] using hh
  have hi : Integrable (fun cube => ∫D,F (cube,D)
      ∂SYK.standardGaussianMeasureOnEuclidean (LatitudeThreeCoordinate n P (TensorCoordinate n K)))
      (positiveCubeLaw K) := Integrable.of_bound hm.aestronglyMeasurable 1 (.of_forall hboundF)
  convert hi using 1
  funext cube
  apply integral_congr_ae
  exact .of_forall fun D => latitudePositivity_pairMass_cube c β κ u e q v θ cube D E

/-- True finite tensor positivity, uniform before dimension, actual
latitude, original covariance, reference and frame are selected. -/
theorem exists_uniform_latitudeCube_positivity {ε η : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) :
    ∃ K : ℕ,∃ V : ℝ,0<K ∧ 1≤V ∧
      ∀ (n P : ℕ),1≤n → ∀ (c : Degree P → ℝ),(∀ p,0≤c p) →
      ∀ (β κ : ℝ),0≤κ → ∀ (u : Vector (n+1)),‖u‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),(∀ x,inner ℝ (e x) u=0) →
      ∀ (q : ℝ),|q|≤1 → ∀ (v : ℝ),V≤v → ∀ (θ : ℝ),
        (∫cube,∫D,GaussianThreeBlockComparison.pairEventMass (sphereLaw n)
          (latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v cube)) latitudeThreeLabel θ
          {z : Vector n × Vector n | overlap z.1 z.2≤-ε} D
          ∂SYK.standardGaussianMeasureOnEuclidean (LatitudeThreeCoordinate n P (TensorCoordinate n K))
          ∂positiveCubeLaw K)≤η := by
  obtain ⟨K,V,hK,hV,hPos⟩ := exists_uniform_independent_bank_positivity hε hε1 hη
  refine ⟨K,V,hK,hV,?_⟩
  intro n P hn c hc β κ hκ u hu e he q hq v hv θ
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0<n by omega)
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hμ : ∀ᵐ x ∂sphereLaw n,‖x‖=Real.sqrt (n : ℝ) :=
    (sphereLaw_support hn).mono fun x hx => norm_eq_sqrt_of_norm_sq x hx
  let L := GaussianSpinComparison.rotatedLinear (latitudeGuerraLinear c β κ u e q) latitudeGuerraLabel θ
  have hL : Measurable L := GaussianSpinComparison.rotatedLinear_measurable _
    (latitudeGuerraLinear_measurable c β κ u e q) latitudeGuerraLabel θ
  have hLb := GaussianSpinComparison.rotatedLinear_bound (sphereLaw n) _ (Real.sqrt_nonneg _)
    (latitudeGuerraLinear_bound hn c hc β hκ u hu e he hq) latitudeGuerraLabel θ
  let T := latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v (fun _ => 1))
  obtain ⟨B,hB,hbound⟩ := exists_latitudeThreeLinear_sphere_bound c β κ u e q
    (latitudePositivityFeature n K v (fun _ => 1)) (latitudePositivityFeature_continuous n K v _)
  have hTb : ∀ᵐ x ∂sphereLaw n,‖T x‖ ≤ B := (sphereLaw_support hn).mono fun x hx => hbound x hx
  have hT : Measurable T := (latitudeThreeLinear_continuous c β κ u e q _
    (latitudePositivityFeature_continuous n K v _)).measurable
  have hsplit (cube : Fin K → ℝ) (D : LatitudeThreeDisorder n P (TensorCoordinate n K)) :
      ∀ᵐ x ∂sphereLaw n,T x (latitudeCubeRealization n P K θ (cube,D))=
        L x (GaussianCompactFeatureComparison.sumSplit D).1+
          radialPerturbation (coefficients v cube) (Real.sqrt (n : ℝ)) x
            (GaussianCompactFeatureComparison.sumSplit D).2 := by
    exact .of_forall fun x => by
      dsimp only [T,latitudeCubeRealization]
      rw [latitudeCubeOperator_rotation,← latitudeThreeLinear_positivity_cube,latitudeThreeLinear_rotation]
      rfl
  have hp := hPos (sphereLaw n) hr hμ (LatitudeGuerraCoordinate n P) L hL hLb v hv T hT hB hTb
    (latitudeCubeRealization n P K θ) (latitudeCubeRealization_continuous n P K θ).measurable hsplit
  have hE : {z : Vector n × Vector n | radiusOverlap (Real.sqrt (n : ℝ)) z.1 z.2≤-ε}=
      {z : Vector n × Vector n | overlap z.1 z.2≤-ε} := by
    ext z
    unfold radiusOverlap overlap
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [hE] at hp
  convert hp using 1
  apply integral_congr_ae
  exact .of_forall fun cube => by
    apply integral_congr_ae
    exact .of_forall fun D => latitudePositivity_pairMass_cube c β κ u e q v θ cube D _

end
end SlowEquilibration.SphericalModel

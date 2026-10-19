-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudePositivityFeature
public import SlowEquilibration.GaussianThreeBlockMeanComparison

@[expose] public section

/-! # Genuine cube parameter regularity of the latitude interpolation

The held coefficients act on the actual Gaussian bank through a continuous
coordinate operator. This proves measurability of both the literal quenched
pressure and the actual averaged replica covariance, including all cube
parameters before restricting to the positive cube law.
-/
namespace SlowEquilibration.SphericalModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalPositivePerturbation
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n P K : ℕ}

theorem latitudePositivity_logPartition_cube (c : Degree P → ℝ) (β κ : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q v : ℝ)
    (cube : Fin K → ℝ) (θ : ℝ) (D : LatitudeThreeDisorder n P (TensorCoordinate n K)) :
    GaussianSpinInterpolation.logPartition (sphereLaw n)
      (latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v cube))
      (GaussianThreeBlockComparison.rotation latitudeThreeLabel θ D)=
      GaussianSpinInterpolation.logPartition (sphereLaw n)
        (latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v (fun _ => 1)))
        (GaussianThreeBlockComparison.rotation latitudeThreeLabel θ (latitudeCubeOperator cube D)) := by
  unfold GaussianSpinInterpolation.logPartition
  congr 1
  unfold GaussianSpinInterpolation.moment GaussianSpinInterpolation.weight
  apply integral_congr_ae
  exact .of_forall fun x => by
    dsimp only
    rw [latitudeThreeLinear_positivity_cube,latitudeCubeOperator_rotation]

theorem latitudePositivity_expectation_cube (c : Degree P → ℝ) (β κ : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q v : ℝ)
    (cube : Fin K → ℝ) (θ : ℝ) (D : LatitudeThreeDisorder n P (TensorCoordinate n K))
    (ρ : Vector n → ℝ) :
    GaussianSpinInterpolation.expectation (sphereLaw n) ρ
      (GaussianThreeBlockComparison.rotatedLinear
        (latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v cube)) latitudeThreeLabel θ) D=
      GaussianSpinInterpolation.expectation (sphereLaw n) ρ
        (latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v (fun _ => 1)))
        (GaussianThreeBlockComparison.rotation latitudeThreeLabel θ (latitudeCubeOperator cube D)) := by
  unfold GaussianSpinInterpolation.expectation
  congr 1 <;> unfold GaussianSpinInterpolation.moment GaussianSpinInterpolation.weight
  all_goals
    apply integral_congr_ae
    exact .of_forall fun x => by
      dsimp only
      rw [GaussianThreeBlockComparison.rotatedLinear,ContinuousLinearMap.comp_apply,
        latitudeThreeLinear_positivity_cube,latitudeCubeOperator_rotation]

/-- Genuine Borel measurability of the actual quenched pressure for all
finite cube parameters. The Gaussian bank and physical sphere are literal. -/
theorem latitudePositivity_pressure_measurable (hn : 1 ≤ n) (c : Degree P → ℝ) (β κ : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q v θ : ℝ) :
    Measurable (fun cube : Fin K → ℝ =>
      GaussianThreeBlockComparison.averagedRotatedLogPartition (sphereLaw n)
        (latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v cube)) latitudeThreeLabel θ) := by
  let L := latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v (fun _ => 1))
  obtain ⟨B,hB,hbound⟩ := exists_latitudeThreeLinear_sphere_bound c β κ u e q
    (latitudePositivityFeature n K v (fun _ => 1)) (latitudePositivityFeature_continuous n K v _)
  have hLb : ∀ᵐ x ∂sphereLaw n,‖L x‖ ≤ B := (sphereLaw_support hn).mono fun x hx => hbound x hx
  have hL : Measurable L := (latitudeThreeLinear_continuous c β κ u e q _
    (latitudePositivityFeature_continuous n K v _)).measurable
  have hc : Continuous (fun z : (Fin K → ℝ) × LatitudeThreeDisorder n P (TensorCoordinate n K) =>
      GaussianSpinInterpolation.logPartition (sphereLaw n) L
        (GaussianThreeBlockComparison.rotation latitudeThreeLabel θ (latitudeCubeOperator z.1 z.2))) :=
    (GaussianSpinInterpolation.logPartition_contDiff (sphereLaw n) L hL hB hLb).continuous.comp
      ((GaussianThreeBlockComparison.rotation latitudeThreeLabel θ).continuous.comp
        (latitudeCubeOperator_joint_continuous n P K))
  have hm := hc.measurable.stronglyMeasurable.integral_prod_right'
    (ν := SYK.standardGaussianMeasureOnEuclidean (LatitudeThreeCoordinate n P (TensorCoordinate n K))) |>.measurable
  convert hm using 1
  funext cube
  unfold GaussianThreeBlockComparison.averagedRotatedLogPartition
  apply integral_congr_ae
  exact .of_forall (latitudePositivity_logPartition_cube c β κ u e q v cube θ)

/-- The literal signed pair covariance contains only the original and
linear coordinates; every held cube coordinate has zero sign. -/
theorem latitudePositivity_pairKernel_cube (hn : 1 ≤ n) (c : Degree P → ℝ) (β κ : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q v : ℝ)
    (cube : Fin K → ℝ) (θ : ℝ) (D : LatitudeThreeDisorder n P (TensorCoordinate n K)) :
    GaussianThreeBlockComparison.pairKernelExpectation (sphereLaw n)
      (latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v cube)) latitudeThreeLabel θ D=
      ∑ i : LatitudeGuerraCoordinate n P,GaussianThreeBlockComparison.covarianceSign (latitudeThreeLabel (ι := TensorCoordinate n K)) (Sum.inl i)*
        (GaussianSpinInterpolation.expectation (sphereLaw n)
          (GaussianThreeBlockComparison.coordinateObservable
            (latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v (fun _ => 1))) (Sum.inl i))
          (latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v (fun _ => 1)))
          (GaussianThreeBlockComparison.rotation latitudeThreeLabel θ (latitudeCubeOperator cube D)))^2 := by
  let L := latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v cube)
  obtain ⟨B,hB,hbound⟩ := exists_latitudeThreeLinear_sphere_bound c β κ u e q
    (latitudePositivityFeature n K v cube) (latitudePositivityFeature_continuous n K v cube)
  have hLb : ∀ᵐ x ∂sphereLaw n,‖L x‖ ≤ B := (sphereLaw_support hn).mono fun x hx => hbound x hx
  have hL : Measurable L := (latitudeThreeLinear_continuous c β κ u e q _
    (latitudePositivityFeature_continuous n K v cube)).measurable
  rw [GaussianThreeBlockComparison.pairKernelExpectation_eq_coordinate_sum (sphereLaw n) L hL hB hLb]
  conv_lhs =>
    rw [Fintype.sum_sum_type]
    arg 2
    simp [GaussianThreeBlockComparison.covarianceSign,latitudeThreeLabel]
  rw [add_zero]
  apply Finset.sum_congr rfl
  intro i _
  have hobs : GaussianThreeBlockComparison.coordinateObservable L (Sum.inl i)=
      GaussianThreeBlockComparison.coordinateObservable
        (latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v (fun _ => 1))) (Sum.inl i) := by
    funext x
    rw [latitudeThree_coordinateObservable,latitudeThree_coordinateObservable]
    rfl
  rw [hobs,latitudePositivity_expectation_cube]

/-- Genuine Borel measurability of the actual disorder-averaged replica
kernel as a function of every finite cube parameter. -/
theorem latitudePositivity_meanPair_measurable (hn : 1 ≤ n) (c : Degree P → ℝ) (β κ : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q v θ : ℝ) :
    Measurable (fun cube : Fin K → ℝ =>
      GaussianThreeBlockComparison.meanPairKernel (sphereLaw n)
        (latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v cube)) latitudeThreeLabel θ) := by
  let L := latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v (fun _ => 1))
  obtain ⟨B,hB,hbound⟩ := exists_latitudeThreeLinear_sphere_bound c β κ u e q
    (latitudePositivityFeature n K v (fun _ => 1)) (latitudePositivityFeature_continuous n K v _)
  have hLb : ∀ᵐ x ∂sphereLaw n,‖L x‖ ≤ B := (sphereLaw_support hn).mono fun x hx => hbound x hx
  have hL : Measurable L := (latitudeThreeLinear_continuous c β κ u e q _
    (latitudePositivityFeature_continuous n K v _)).measurable
  let f := fun z : (Fin K → ℝ) × LatitudeThreeDisorder n P (TensorCoordinate n K) =>
    ∑ i : LatitudeGuerraCoordinate n P,GaussianThreeBlockComparison.covarianceSign (latitudeThreeLabel (ι := TensorCoordinate n K)) (Sum.inl i)*
      (GaussianSpinInterpolation.expectation (sphereLaw n)
        (GaussianThreeBlockComparison.coordinateObservable L (Sum.inl i)) L
        (GaussianThreeBlockComparison.rotation latitudeThreeLabel θ (latitudeCubeOperator z.1 z.2)))^2
  have hc : Continuous f := by
    apply continuous_finsetSum
    intro i _
    apply Continuous.const_mul
    apply Continuous.pow
    exact (GaussianSpinInterpolation.expectation_contDiff (sphereLaw n)
      (GaussianThreeBlockComparison.coordinateObservable L (Sum.inl i)) L
      (GaussianThreeBlockComparison.coordinateObservable_measurable L hL _) hL hB hB
      ((GaussianThreeBlockComparison.coordinateObservable_bound (sphereLaw n) L hLb _).and hLb)).continuous.comp
      ((GaussianThreeBlockComparison.rotation latitudeThreeLabel θ).continuous.comp
        (latitudeCubeOperator_joint_continuous n P K))
  have hm := hc.measurable.stronglyMeasurable.integral_prod_right'
    (ν := SYK.standardGaussianMeasureOnEuclidean (LatitudeThreeCoordinate n P (TensorCoordinate n K))) |>.measurable
  convert hm using 1
  funext cube
  unfold GaussianThreeBlockComparison.meanPairKernel
  apply integral_congr_ae
  exact .of_forall (latitudePositivity_pairKernel_cube hn c β κ u e q v cube θ)

end
end SlowEquilibration.SphericalModel

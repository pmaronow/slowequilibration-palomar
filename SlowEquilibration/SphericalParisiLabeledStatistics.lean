-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiLabeledRealization
public import SlowEquilibration.GaussianThreeBlockParameterComparison
public import SlowEquilibration.GaussianThreeBlockKernelBudget
public import Mathlib.Probability.Kernel.MeasurableIntegral

@[expose] public section

/-! Genuine external-parameter pressure and replica covariance statistics
for the original finite spherical spin-label model. Every domination is
derived from its literal compact features and actual perturbation budget. -/

namespace SlowEquilibration.SphericalParisiLabeledStatistics
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel FiniteTensorMixtureMaximum PureTensorJetBounds
open SphericalParisiLabeledCovariance SphericalParisiLabeledThreeBlock
open SphericalParisiLabeledTrace SphericalParisiLabeledRealization
open SphericalPositivePerturbation GaussianCompactFeatureComparison GaussianSpinInterpolation
open GaussianThreeBlockComparison
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

private theorem join_norm_sq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : EuclideanSpace ℝ ι) (w : EuclideanSpace ℝ κ) :
    ‖sumJoin (u,w)‖^2=‖u‖^2+‖w‖^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq,Fintype.sum_sum_type]
  rfl

omit [DecidableEq σ] in
theorem actual_threeFeature_norm_sq_parameter {N k K : ℕ} (d : σ → ℕ) (c : σ → ℝ)
    (β q0 q1 v : ℝ) (x : Fin K → ℝ) (z : UnitSphere N × Fin k) :
    ‖threeFeature d c β q0 q1 v x z‖^2=
      ‖threeFeature d c β q0 q1 v (fun _ : Fin K => 0) z‖^2+
        ∑ p : Fin K,(coefficients v x p)^2 := by
  simp only [threeFeature,join_norm_sq,SphericalPositivePerturbation.feature_norm_sq _ _ (unit_norm z.1)]
  simp only [coefficients,mul_zero,zero_pow (by norm_num : 2 ≠ 0),Finset.sum_const_zero,add_zero]

omit [DecidableEq σ] in
/-- The actual positive-cube bank has one true feature bound selected before
all external coefficient vectors. -/
theorem actual_uniform_threeLinear_cube_bound {N k K : ℕ} (d : σ → ℕ) (c : σ → ℝ)
    (β q0 q1 v : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (x : Fin K → ℝ),(∀ p,|x p| ≤ 2) →
      ∀ z : UnitSphere N × Fin k,‖threeLinear d c β q0 q1 v x z‖ ≤ C := by
  obtain ⟨B,hB,hbound⟩ := actual_threeLinear_bounded (N := N) (k := k) d c β q0 q1 v (fun _ : Fin K => 0)
  refine ⟨Real.sqrt (B^2+(2*v)^2),Real.sqrt_nonneg _,?_⟩
  intro x hx z
  rw [threeLinear,innerSL_apply_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity),actual_threeFeature_norm_sq_parameter]
  have hbz := hbound z
  rw [threeLinear,innerSL_apply_norm] at hbz
  exact add_le_add ((sq_le_sq₀ (norm_nonneg _) hB).mpr hbz) (coefficients_budget v x hx)

omit [DecidableEq σ] in
theorem actual_three_logPartition_realization {N k K : ℕ}
    (ν : Measure (UnitSphere N × Fin k)) (d : σ → ℕ) (c : σ → ℝ)
    (β q0 q1 v θ : ℝ) (x : Fin K → ℝ) (D : EuclideanSpace ℝ (ThreeCoordinate N k K d)) :
    logPartition ν (threeLinear d c β q0 q1 v x) (rotation threeLabel θ D)=
      logPartition ν (threeLinear d c β q0 q1 v (fun _ => 1)) (realizedDisorder N k K d θ (x,D)) := by
  unfold logPartition
  congr 1
  unfold GaussianSpinInterpolation.moment weight
  apply integral_congr_ae
  exact .of_forall fun z => by
    dsimp only
    rw [actual_threeLinear_parameter_realization,← parameterDisorder_rotation]
    rfl

omit [DecidableEq σ] in
theorem actual_three_pressure_measurable {N k K : ℕ}
    (ν : Measure (UnitSphere N × Fin k)) [IsProbabilityMeasure ν]
    (d : σ → ℕ) (c : σ → ℝ) (β q0 q1 v θ : ℝ) :
    Measurable (fun x : Fin K → ℝ => averagedRotatedLogPartition ν
      (threeLinear d c β q0 q1 v x) threeLabel θ) := by
  let T := threeLinear (N := N) (k := k) d c β q0 q1 v (fun _ : Fin K => 1)
  obtain ⟨C,hC,hbound⟩ := actual_threeLinear_bounded (N := N) (k := k) d c β q0 q1 v (fun _ : Fin K => 1)
  have hT : Measurable T := (actual_threeLinear_continuous d c β q0 q1 v _).measurable
  have hb : ∀ᵐ z ∂ν,‖T z‖ ≤ C := .of_forall hbound
  have hm := (((logPartition_contDiff ν T hT hC hb).continuous.comp
    (realizedDisorder_continuous N k K d θ)).measurable.stronglyMeasurable.integral_prod_right'
      (ν := SYK.standardGaussianMeasureOnEuclidean (ThreeCoordinate N k K d))).measurable
  convert hm using 1
  funext x
  unfold averagedRotatedLogPartition
  apply integral_congr_ae
  exact .of_forall fun D => actual_three_logPartition_realization ν d c β q0 q1 v θ x D

omit [DecidableEq σ] in
theorem actual_three_meanPair_measurable {N k K : ℕ}
    (ν : Measure (UnitSphere N × Fin k)) [IsProbabilityMeasure ν]
    (d : σ → ℕ) (c : σ → ℝ) (β q0 q1 v θ : ℝ) :
    Measurable (fun x : Fin K → ℝ => meanPairKernel ν
      (threeLinear d c β q0 q1 v x) threeLabel θ) := by
  let T := threeLinear (N := N) (k := k) d c β q0 q1 v (fun _ : Fin K => 1)
  obtain ⟨C,hC,hbound⟩ := actual_threeLinear_bounded (N := N) (k := k) d c β q0 q1 v (fun _ : Fin K => 1)
  have hT : Measurable T := (actual_threeLinear_continuous d c β q0 q1 v _).measurable
  have hb : ∀ᵐ z ∂ν,‖T z‖ ≤ C := .of_forall hbound
  have := gibbsKernel_markov ν T hT hC hb
  let G := (gibbsKernel ν T).comap (realizedDisorder N k K d θ)
    (realizedDisorder_continuous N k K d θ).measurable
  let χ : (UnitSphere N × Fin k) × (UnitSphere N × Fin k) → ℝ :=
    fun z => signedKernel T threeLabel z.1 z.2
  have hχ : Continuous χ := by
    unfold χ signedKernel
    apply continuous_finsetSum
    intro i _
    have hi : Continuous (coordinateObservable T i) :=
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).continuous.comp
        (actual_threeLinear_continuous d c β q0 q1 v _)
    exact continuous_const.mul ((hi.comp continuous_fst).mul (hi.comp continuous_snd))
  have hj : Measurable (fun p => ∫ z,χ z ∂(G ×ₖ G) p) :=
    hχ.measurable.stronglyMeasurable.integral_kernel.measurable
  have hm := hj.stronglyMeasurable.integral_prod_right'
    (ν := SYK.standardGaussianMeasureOnEuclidean (ThreeCoordinate N k K d)) |>.measurable
  convert hm using 1
  funext x
  unfold meanPairKernel
  apply integral_congr_ae
  exact .of_forall fun D => by
    rw [pairKernelExpectation,actual_three_gibbs_realization]
    dsimp only
    rw [Kernel.prod_apply]
    change (∫ z,signedKernel (threeLinear d c β q0 q1 v x) threeLabel z.1 z.2
      ∂(gibbsMeasure ν T (realizedDisorder N k K d θ (x,D))).prod
        (gibbsMeasure ν T (realizedDisorder N k K d θ (x,D))))=
      ∫ z,χ z ∂(gibbsKernel ν T (realizedDisorder N k K d θ (x,D))).prod
        (gibbsKernel ν T (realizedDisorder N k K d θ (x,D)))
    rw [gibbsKernel_apply ν T hT hC hb]
    apply integral_congr_ae
    exact .of_forall fun z => by
      dsimp only [χ,T]
      rw [actual_three_signedKernel_difference,actual_three_signedKernel_difference]

omit [DecidableEq σ] in
theorem actual_three_pressure_integrable {N k K : ℕ}
    (ν : Measure (UnitSphere N × Fin k)) [IsProbabilityMeasure ν]
    (d : σ → ℕ) (c : σ → ℝ) (β q0 q1 v θ : ℝ) :
    Integrable (fun x : Fin K → ℝ => averagedRotatedLogPartition ν
      (threeLinear d c β q0 q1 v x) threeLabel θ) (positiveCubeLaw K) := by
  obtain ⟨C,hC,hbound⟩ := actual_uniform_threeLinear_cube_bound (N := N) (k := k) d c β q0 q1 v
  apply Integrable.of_bound (actual_three_pressure_measurable ν d c β q0 q1 v θ).aestronglyMeasurable
    (C*(∫ D : EuclideanSpace ℝ (ThreeCoordinate N k K d),‖D‖
      ∂SYK.standardGaussianMeasureOnEuclidean (ThreeCoordinate N k K d)))
  filter_upwards [positiveCubeLaw_abs_le_two K] with x hx
  exact norm_averagedRotatedLogPartition_le_gaussianNorm ν _
    (actual_threeLinear_continuous d c β q0 q1 v x).measurable hC
    (.of_forall (hbound x hx)) threeLabel θ

omit [DecidableEq σ] in
theorem actual_three_meanPair_integrable {N k K : ℕ}
    (ν : Measure (UnitSphere N × Fin k)) [IsProbabilityMeasure ν]
    (d : σ → ℕ) (c : σ → ℝ) (β q0 q1 v θ : ℝ) :
    Integrable (fun x : Fin K → ℝ => meanPairKernel ν
      (threeLinear d c β q0 q1 v x) threeLabel θ) (positiveCubeLaw K) := by
  obtain ⟨C,hC,hbound⟩ := actual_uniform_threeLinear_cube_bound (N := N) (k := k) d c β q0 q1 v
  apply Integrable.of_bound (actual_three_meanPair_measurable ν d c β q0 q1 v θ).aestronglyMeasurable
    ((Fintype.card (ThreeCoordinate N k K d) : ℝ)*C^2)
  filter_upwards [positiveCubeLaw_abs_le_two K] with x hx
  exact norm_meanPairKernel_le ν _ (actual_threeLinear_continuous d c β q0 q1 v x).measurable hC
    (.of_forall (hbound x hx)) threeLabel θ

end
end SlowEquilibration.SphericalParisiLabeledStatistics

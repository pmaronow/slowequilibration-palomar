-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGuerraBound
public import SlowEquilibration.SphericalParisiLabeledComparison
public import SlowEquilibration.SphericalParisiLabeledHeldPressure

@[expose] public section

/-! Actual finite one-step comparison after removal of the held Gaussian
perturbation. Both endpoints are original ordinary Gaussian base-bank
partition integrals on the true sphere-label reference probability. -/

namespace SlowEquilibration.SphericalParisiLabeledUnheldComparison
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel FiniteTensorMixtureMaximum PureTensorJetBounds
open SphericalParisiLabeledCovariance SphericalParisiLabeledThreeBlock
open SphericalParisiLabeledTrace SphericalParisiLabeledRealization
open SphericalParisiLabeledStatistics SphericalParisiLabeledComparison SphericalParisiLabeledHeldPressure
open SphericalPositivePerturbation GaussianSpinInterpolation GaussianThreeBlockComparison
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def unheldPressure {N k : ℕ} (ν : Measure (UnitSphere N × Fin k))
    (d : σ → ℕ) (c : σ → ℝ) (β q0 q1 θ : ℝ) : ℝ :=
  ∫ D,logPartition ν (baseLinear d c β q0 q1 θ) D
    ∂SYK.standardGaussianMeasureOnEuclidean (BaseCoordinate N k d)

omit [DecidableEq σ] in
theorem actual_base_logPartition_integrable {N k : ℕ}
    (ν : Measure (UnitSphere N × Fin k)) [IsProbabilityMeasure ν]
    (d : σ → ℕ) (c : σ → ℝ) (β q0 q1 θ : ℝ) :
    Integrable (logPartition ν (baseLinear d c β q0 q1 θ))
      (SYK.standardGaussianMeasureOnEuclidean (BaseCoordinate N k d)) := by
  let L := baseLinear (N := N) (k := k) d c β q0 q1 θ
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (baseLinear_continuous (N := N) (k := k) d c β q0 q1 θ).continuousOn
  let C := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  have hb : ∀ᵐ z ∂ν,‖L z‖ ≤ C := .of_forall fun z => (hB z (mem_univ z)).trans (le_max_left _ _)
  have hL : Measurable L := (baseLinear_continuous d c β q0 q1 θ).measurable
  apply ((gaussian_norm_integrable (ι := BaseCoordinate N k d)).const_mul C).mono'
    (logPartition_contDiff ν L hL hC hb).continuous.aestronglyMeasurable
  exact .of_forall fun D => by
    rw [Real.norm_eq_abs]
    exact abs_logPartition_le ν L hL hb D

omit [DecidableEq σ] in
theorem actual_unheld_field_eq_base_projection {N k K : ℕ}
    (d : σ → ℕ) (c : σ → ℝ) (β q0 q1 v θ : ℝ)
    (z : UnitSphere N × Fin k) (D : EuclideanSpace ℝ (ThreeCoordinate N k K d)) :
    threeLinear d c β q0 q1 v (fun _ : Fin K => 0) z (rotation threeLabel θ D)=
      baseLinear d c β q0 q1 θ z (projectGaussian Sum.inl D) := by
  rw [actual_threeLinear_rotation_split]
  have hz : SphericalParisiUnitSpherePositivity.unitSphereLinear
      (coefficients v (fun _ : Fin K => 0)) z.1 (GaussianCompactFeatureComparison.sumSplit D).2=0 := by
    simp [SphericalParisiUnitSpherePositivity.unitSphereLinear,SphericalPositivePerturbation.linear,
      innerSL_apply_apply,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,
      SphericalPositivePerturbation.feature,coefficients]
  rw [hz,add_zero]
  rfl

omit [DecidableEq σ] in
/-- The original unheld endpoint is an actual smaller Gaussian bank;
coordinate projection removes the unused perturbation coordinates exactly. -/
theorem actual_unheld_mean_eq_basePressure {N k K : ℕ}
    (ν : Measure (UnitSphere N × Fin k)) [IsProbabilityMeasure ν]
    (d : σ → ℕ) (c : σ → ℝ) (β q0 q1 v θ : ℝ) :
    averagedRotatedLogPartition ν (threeLinear d c β q0 q1 v (fun _ : Fin K => 0)) threeLabel θ=
      unheldPressure ν d c β q0 q1 θ := by
  have hi := actual_base_logPartition_integrable ν d c β q0 q1 θ
  have H := (projectGaussian_hasLaw
    (Sum.inl : BaseCoordinate N k d → ThreeCoordinate N k K d) Sum.inl_injective).integral_comp hi.aestronglyMeasurable
  have he (D : EuclideanSpace ℝ (ThreeCoordinate N k K d)) :
      logPartition ν (threeLinear d c β q0 q1 v (fun _ : Fin K => 0)) (rotation threeLabel θ D)=
        logPartition ν (baseLinear d c β q0 q1 θ) (projectGaussian Sum.inl D) := by
    unfold logPartition
    congr 1
    unfold GaussianSpinInterpolation.moment weight
    apply integral_congr_ae
    exact .of_forall fun z => by
      dsimp only
      rw [actual_unheld_field_eq_base_projection]
  unfold averagedRotatedLogPartition unheldPressure
  rw [integral_congr_ae (.of_forall he)]
  exact H

/-- Genuine finite unperturbed one-step comparison. The fixed physical
perturbation costs only2v², independently of dimension and label count. -/
theorem exists_actual_unheld_finite_one_step_comparison {ε η : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) :
    ∃ V : ℝ,1 ≤ V ∧
      ∀ (N k : ℕ) (ν : Measure (UnitSphere N × Fin k)) [IsProbabilityMeasure ν]
        (σ : Type*) [Fintype σ] [DecidableEq σ]
        (d : σ → ℕ) (c : σ → ℝ),
        (∀ i,0 ≤ c i) → (∀ i,1 ≤ d i) →
        ∀ (β q0 q1 v : ℝ),0 ≤ q0 → q0 ≤ q1 → V ≤ v →
        unheldPressure ν d c β q0 q1 0 ≤ unheldPressure ν d c β q0 q1 (Real.pi/2)+2*v^2+
          ((N : ℝ)*β^2/2)*(bregmanGap d c 1 q1+SphericalParisiLabeledBregman.covarianceBudget c*(ε+η)) := by
  obtain ⟨K,V,_hK,hV,hCompare⟩ := exists_actual_finite_labeled_one_step_comparison hε hε1 hη
  refine ⟨V,hV,?_⟩
  intro N k ν _ σ _ _ d c hc hd β q0 q1 v hq0 hqq hv
  have H := hCompare N k ν σ d c hc hd β q0 q1 v hq0 hqq hv
  have h0 := actual_parameter_held_pressure_increment_mem_Icc (K := K) ν d c β q0 q1 v 0
  have h1 := actual_parameter_held_pressure_increment_mem_Icc (K := K) ν d c β q0 q1 v (Real.pi/2)
  rw [actual_unheld_mean_eq_basePressure] at h0 h1
  nlinarith [h0.1,h1.2,H]

/-- With top trial overlap one, the true diagonal Bregman term vanishes.
All remaining extensive error is the actual tunable positivity error. -/
theorem exists_actual_unheld_unit_top_comparison {ε η : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) :
    ∃ V : ℝ,1 ≤ V ∧
      ∀ (N k : ℕ) (ν : Measure (UnitSphere N × Fin k)) [IsProbabilityMeasure ν]
        (σ : Type*) [Fintype σ] [DecidableEq σ]
        (d : σ → ℕ) (c : σ → ℝ),
        (∀ i,0 ≤ c i) → (∀ i,1 ≤ d i) →
        ∀ (β q0 v : ℝ),0 ≤ q0 → q0 ≤ 1 → V ≤ v →
        unheldPressure ν d c β q0 1 0 ≤ unheldPressure ν d c β q0 1 (Real.pi/2)+2*v^2+
          ((N : ℝ)*β^2/2)*SphericalParisiLabeledBregman.covarianceBudget c*(ε+η) := by
  obtain ⟨V,hV,H⟩ := exists_actual_unheld_finite_one_step_comparison hε hε1 hη
  refine ⟨V,hV,?_⟩
  intro N k ν _ σ _ _ d c hc hd β q0 v hq0 hq1 hv
  have h := H N k ν σ d c hc hd β q0 1 v hq0 hq1 hv
  simpa only [bregmanGap,sub_self,mul_zero,zero_sub,sub_zero,zero_add,mul_assoc] using h

end
end SlowEquilibration.SphericalParisiLabeledUnheldComparison

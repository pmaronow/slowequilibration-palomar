-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiLabeledTrialPressure
public import SlowEquilibration.SphericalParisiLabeledOriginalPressure
public import SlowEquilibration.SphericalParisiOneStepDualScalar

@[expose] public section

/-! True finite one-step physical pressure upper chain. The original
sphere-spin partition, independent iid scalar REM and common/fresh linear
trial are actual Gaussian integrals. All positivity, covariance rotation,
held deletion and endpoint bounds are proved, not supplied conclusions. -/

namespace SlowEquilibration.SphericalParisiOneStepPressureUpper
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel FiniteTensorMixtureMaximum PureTensorJetBounds
open SphericalParisiLabeledCovariance SphericalParisiLabeledRealization SphericalParisiLabeledThreeBlock
open SphericalParisiLabeledUnheldComparison SphericalParisiLabeledOriginalEndpoint
open SphericalParisiLabeledOriginalPressure SphericalParisiLabeledTrialEndpoint SphericalParisiLabeledTrialPressure
open SphericalParisiGaussianREM GaussianCompactFeatureComparison GaussianSpinInterpolation
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

private theorem join_inner {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u u' : EuclideanSpace ℝ ι) (w w' : EuclideanSpace ℝ κ) :
    inner ℝ (sumJoin (u,w)) (sumJoin (u',w'))=inner ℝ u u'+inner ℝ w w' := by
  simp only [PiLp.inner_apply,Fintype.sum_sum_type]
  rfl

omit [DecidableEq σ] in
theorem actual_base_trial_field {N k : ℕ} (d : σ → ℕ) (c : σ → ℝ) (β q0 q1 : ℝ)
    (z : UnitSphere N × Fin k) (D : EuclideanSpace ℝ (BaseCoordinate N k d)) :
    baseLinear d c β q0 q1 (Real.pi/2) z D=
      trialLinear β (xi1 d c q0) (xi1 d c q1-xi1 d c q0) z (projectGaussian Sum.inr D) := by
  unfold baseLinear baseFeature trialLinear
  simp only [Real.cos_pi_div_two,Real.sin_pi_div_two,mul_zero,mul_one,zero_smul]
  rw [innerSL_apply_apply,innerSL_apply_apply,← sumJoin_sumSplit D,join_inner,inner_zero_left,zero_add]
  rfl

omit [DecidableEq σ] in
theorem actual_unheld_trial_pressure {N k : ℕ} [NeZero k]
    (μ : Measure (UnitSphere N)) [IsProbabilityMeasure μ]
    (d : σ → ℕ) (c : σ → ℝ) (β q0 q1 : ℝ) :
    unheldPressure (μ.prod (labelLaw k)) d c β q0 q1 (Real.pi/2)=
      trialPressure (k := k) μ β (xi1 d c q0) (xi1 d c q1-xi1 d c q0) := by
  have hi := actual_trial_log_partition_integrable (k := k) μ β (xi1 d c q0) (xi1 d c q1-xi1 d c q0)
  have H := (projectGaussian_hasLaw
    (Sum.inr : TrialCoordinate N k → BaseCoordinate N k d) Sum.inr_injective).integral_comp hi.aestronglyMeasurable
  have he (D : EuclideanSpace ℝ (BaseCoordinate N k d)) :
      logPartition (μ.prod (labelLaw k)) (baseLinear d c β q0 q1 (Real.pi/2)) D=
        logPartition (μ.prod (labelLaw k)) (trialLinear β (xi1 d c q0) (xi1 d c q1-xi1 d c q0))
          (projectGaussian Sum.inr D) := by
    unfold logPartition
    apply congrArg Real.log
    unfold GaussianSpinInterpolation.moment weight
    apply integral_congr_ae
    exact .of_forall fun z => by
      dsimp only
      rw [actual_base_trial_field]
  unfold unheldPressure trialPressure
  rw [integral_congr_ae (.of_forall he)]
  exact H

def trialQuadraticExpression (N k : ℕ) (β a0 a m b : ℝ) : ℝ :=
  -((N : ℝ)/2)*Real.log (1-(m*(β*Real.sqrt (N : ℝ)))*a/b)/m+
    (β*Real.sqrt (N : ℝ))*b/2+
    (β*Real.sqrt (N : ℝ))*a0*(N : ℝ)/(2*(b-(m*(β*Real.sqrt (N : ℝ)))*a))+
    (1-m)*Real.log (k : ℝ)/m

/-- Complete genuine finite one-step pressure upper, retaining the actual
independent scalar REM term before its true limit is evaluated. -/
theorem exists_actual_finite_one_step_pressure_upper {ε η : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) :
    ∃ V : ℝ,1 ≤ V ∧
      ∀ (N k : ℕ) [NeZero k] (μ : Measure (UnitSphere N)) [IsProbabilityMeasure μ]
        (σ : Type*) [Fintype σ] [DecidableEq σ]
        (d : σ → ℕ) (c : σ → ℝ),
        (∀ i,0 ≤ c i) → (∀ i,1 ≤ d i) →
        ∀ (β q v m b : ℝ),0 ≤ β → 0 ≤ q → q ≤ 1 → V ≤ v →
          0 < m → m ≤ 1 → 0 < b →
          0 < b-(m*(β*Real.sqrt (N : ℝ)))*(xi1 d c 1-xi1 d c q) →
        originalSpinPressure μ d c β+
          (∫ y,remLogAverage N k (β*Real.sqrt (theta d c 1-theta d c q)) y
            ∂SYK.standardGaussianMeasureOnEuclidean (Fin k)) ≤
          trialQuadraticExpression N k β (xi1 d c q) (xi1 d c 1-xi1 d c q) m b+2*v^2+
            ((N : ℝ)*β^2/2)*SphericalParisiLabeledBregman.covarianceBudget c*(ε+η) := by
  obtain ⟨V,hV,H⟩ := exists_actual_unheld_unit_top_comparison hε hε1 hη
  refine ⟨V,hV,?_⟩
  intro N k _ μ _ σ _ _ d c hc hd β q v m b hβ hq hq1 hv hm hm1 hb hmargin
  have hCompare := H N k (μ.prod (labelLaw k)) σ d c hc hd β q v hq hq1 hv
  rw [actual_unheld_original_pressure μ d c hβ q 1,
    actual_original_pressure_eq_spin_add_rem μ d c hβ q 1,
    actual_unheld_trial_pressure] at hCompare
  have hA0 : 0 ≤ xi1 d c q := xi1_nonnegative d c hc hq
  have hA : 0 ≤ xi1 d c 1-xi1 d c q := sub_nonneg.mpr (xi1_monotone_positive d c hc hq hq1)
  have hTrial := actual_trial_pressure_quadratic_upper (k := k) μ hβ hA0 hA hm hm1 hb hmargin
  change trialPressure (k := k) μ β (xi1 d c q) (xi1 d c 1-xi1 d c q) ≤
    trialQuadraticExpression N k β (xi1 d c q) (xi1 d c 1-xi1 d c q) m b at hTrial
  linarith

end
end SlowEquilibration.SphericalParisiOneStepPressureUpper

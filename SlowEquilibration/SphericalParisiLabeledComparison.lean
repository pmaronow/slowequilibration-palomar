-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiLabeledStatistics
public import SlowEquilibration.SphericalParisiLabeledPhysicalPositivity
public import SlowEquilibration.GaussianThreeBlockReplicaError

@[expose] public section

/-! Genuine finite ordinary-Gaussian spin-label one-step comparison, for
all parities. The actual negative-overlap probability is proved uniformly
small before the interpolation; no pressure bound, REM limit, Parisi/TAP
formula or desired concentration conclusion appears as an assumption. -/

namespace SlowEquilibration.SphericalParisiLabeledComparison
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel FiniteTensorMixtureMaximum PureTensorJetBounds
open SphericalParisiLabeledCovariance SphericalParisiLabeledThreeBlock
open SphericalParisiLabeledTrace SphericalParisiLabeledStatistics
open SphericalParisiLabeledPhysicalPositivity SphericalParisiLabeledBregman
open SphericalPositivePerturbation GaussianThreeBlockComparison
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Actual averaged replica covariance with the true Gaussian event mass. -/
theorem actual_meanPair_indicator_upper {N k K : ℕ}
    (ν : Measure (UnitSphere N × Fin k)) [IsProbabilityMeasure ν]
    (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i,0 ≤ c i) (hd : ∀ i,1 ≤ d i)
    (β v : ℝ) {q0 q1 ε : ℝ} (hq0 : 0 ≤ q0) (hqq : q0 ≤ q1) (hε : 0 ≤ ε)
    (x : Fin K → ℝ) (θ : ℝ) :
    meanPairKernel ν (threeLinear d c β q0 q1 v x) threeLabel θ ≤
      (N : ℝ)*β^2*(theta d c q0+covarianceBudget c*ε)+
        ((N : ℝ)*β^2*covarianceBudget c)*
          (∫ D,actualNegativePairMass ν d c β q0 q1 v x θ D ε
            ∂SYK.standardGaussianMeasureOnEuclidean (ThreeCoordinate N k K d)) := by
  obtain ⟨C,hC,hbound⟩ := actual_threeLinear_bounded (N := N) (k := k) d c β q0 q1 v x
  have hL := (actual_threeLinear_continuous (N := N) (k := k) d c β q0 q1 v x).measurable
  exact meanPairKernel_le_of_indicator ν _ hL hC (.of_forall hbound) threeLabel
    (negativePairSet N k ε) (negativePairSet_measurable N k ε)
    (.of_forall fun z => actual_three_signedKernel_error_bound d c hc hd β v hq0 hqq hε x z.1 z.2) θ

omit [DecidableEq σ] in
/-- The true parameter/Gaussian average of the negative pair event is an
integrable real function, before any covariance estimate is applied. -/
theorem actual_meanNegativePair_integrable {N k K : ℕ}
    (ν : Measure (UnitSphere N × Fin k)) [IsProbabilityMeasure ν]
    (d : σ → ℕ) (c : σ → ℝ) (β q0 q1 v θ ε : ℝ) :
    Integrable (fun x : Fin K → ℝ => ∫ D,
      actualNegativePairMass ν d c β q0 q1 v x θ D ε
        ∂SYK.standardGaussianMeasureOnEuclidean (ThreeCoordinate N k K d)) (positiveCubeLaw K) :=
  (actual_negative_pair_mass_joint_integrable ν d c β q0 q1 v θ ε).integral_prod_left

/-- Actual one-step covariance comparison at every finite dimension and
finite label count. Every perturbation constant is chosen before the
original mixture, physical reference probability and temperature. -/
theorem exists_actual_finite_labeled_one_step_comparison {ε η : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) :
    ∃ K : ℕ,∃ V : ℝ,0 < K ∧ 1 ≤ V ∧
      ∀ (N k : ℕ) (ν : Measure (UnitSphere N × Fin k)) [IsProbabilityMeasure ν]
        (σ : Type*) [Fintype σ] [DecidableEq σ]
        (d : σ → ℕ) (c : σ → ℝ),
        (∀ i,0 ≤ c i) → (∀ i,1 ≤ d i) →
        ∀ (β q0 q1 v : ℝ),0 ≤ q0 → q0 ≤ q1 → V ≤ v →
        parameterAveragedPressure (positiveCubeLaw K) ν (threeLinear d c β q0 q1 v) threeLabel 0 ≤
          parameterAveragedPressure (positiveCubeLaw K) ν (threeLinear d c β q0 q1 v) threeLabel (Real.pi/2)+
            ((N : ℝ)*β^2/2)*(bregmanGap d c 1 q1+covarianceBudget c*(ε+η)) := by
  obtain ⟨K,V,hK,hV,hPos⟩ := exists_uniform_actual_three_bank_pair_positivity hε hε1 hη
  refine ⟨K,V,hK,hV,?_⟩
  intro N k ν _ σ _ _ d c hc hd β q0 q1 v hq0 hqq hv
  let L := threeLinear (N := N) (k := k) (K := K) d c β q0 q1 v
  obtain ⟨C,hC,hbound⟩ := actual_uniform_threeLinear_cube_bound (N := N) (k := k) (K := K) d c β q0 q1 v
  have hL : ∀ x : Fin K → ℝ,Measurable (L x) :=
    fun x => (actual_threeLinear_continuous d c β q0 q1 v x).measurable
  have hb : ∀ᵐ x ∂positiveCubeLaw K,∀ᵐ z ∂ν,‖L x z‖ ≤ C :=
    (positiveCubeLaw_abs_le_two K).mono fun x hx => .of_forall (hbound x hx)
  have hdiag : ∀ᵐ x ∂positiveCubeLaw K,∀ᵐ z ∂ν,
      signedKernel (L x) threeLabel z z=(N : ℝ)*β^2*(theta d c q0-bregmanGap d c 1 q1) :=
    .of_forall fun x => .of_forall (actual_three_signedKernel_diagonal d c hc hd β v hq0 hqq x)
  have hpm (θ : ℝ) : AEStronglyMeasurable (fun x => averagedRotatedLogPartition ν (L x) threeLabel θ)
      (positiveCubeLaw K) := (actual_three_pressure_measurable ν d c β q0 q1 v θ).aestronglyMeasurable
  have hpi (θ : ℝ) : Integrable (fun x => meanPairKernel ν (L x) threeLabel θ) (positiveCubeLaw K) :=
    actual_three_meanPair_integrable ν d c β q0 q1 v θ
  have hpair (θ : ℝ) (_hθ : θ ∈ Icc (0 : ℝ) (Real.pi/2)) :
      parameterAveragedPairKernel (positiveCubeLaw K) ν L threeLabel θ ≤
        (N : ℝ)*β^2*(theta d c q0+covarianceBudget c*(ε+η)) := by
    have hi := actual_meanNegativePair_integrable (K := K) ν d c β q0 q1 v θ ε
    have H := integral_mono (hpi θ) ((integrable_const _).add (hi.const_mul _))
      (fun x => actual_meanPair_indicator_upper ν d c hc hd β v hq0 hqq hε.le x θ)
    rw [integral_add' (integrable_const _) (hi.const_mul _),
      integral_const_mul ((N : ℝ)*β^2*covarianceBudget c) _] at H
    simp only [integral_const,probReal_univ,one_smul] at H
    have hcoef : 0 ≤ (N : ℝ)*β^2*covarianceBudget c :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg β)) (covarianceBudget_nonnegative c hc)
    have hErr := mul_le_mul_of_nonneg_left (hPos N k ν σ d c β q0 q1 v hv θ) hcoef
    change (∫ x,meanPairKernel ν (L x) threeLabel θ ∂positiveCubeLaw K) ≤ _
    nlinarith [H,hErr]
  have H := gaussian_covariance_comparison_of_parameter_mean_pair (positiveCubeLaw K) ν L hL hC hb
    threeLabel hdiag hpm hpi hpair
  change parameterAveragedPressure (positiveCubeLaw K) ν L threeLabel 0 ≤ _ at H ⊢
  apply H.trans_eq
  ring

end
end SlowEquilibration.SphericalParisiLabeledComparison

-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureHorizonHitFibers
public import SlowEquilibration.SphericalTripleProductReal

/-! A posterior-path hit probability through H is independent of which
continuous-path horizon S≥H represents the same literal Brownian solution. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalPosteriorGradientIndependence
open MeasureTheory ProbabilityTheory SphericalModel SphericalPosteriorMaps
open SphericalTripleProductReal SphericalAging HardSphereDynamics
open scoped NNReal
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem valuePosterior_overlap_horizon_probability_extension
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (u : Vector (n+1))
    (mark : ℝ) (β : ℝ)
    (H S S' : ℝ≥0) (hS : H ≤ S) (hS' : H ≤ S') (a : ℝ) :
    (posteriorTrajectoryLaw n μ).real {q | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |valuePosteriorOverlapScore n μ Q u mark β S t q|} =
    (posteriorTrajectoryLaw n μ).real {q | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |valuePosteriorOverlapScore n μ Q u mark β S' t q|} := by
  let E : Set (EuclideanDisorder (n+1) μ.maxDegree ×
      (Vector (n+1) × VectorBrownian.Space (n+1))) :=
    {q | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |valuePosteriorOverlapScore n μ Q u mark β S t q|}
  let E' : Set (EuclideanDisorder (n+1) μ.maxDegree ×
      (Vector (n+1) × VectorBrownian.Space (n+1))) :=
    {q | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |valuePosteriorOverlapScore n μ Q u mark β S' t q|}
  have hE : MeasurableSet E :=
    valuePosterior_overlap_horizon_hit_measurable n μ Q u mark β S H a
  have hE' : MeasurableSet E' :=
    valuePosterior_overlap_horizon_hit_measurable n μ Q u mark β S' H a
  change ((stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)).prod
      ((sphereLaw (n+1)).prod (VectorBrownian.law (n+1)))).real E =
    ((stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)).prod
      ((sphereLaw (n+1)).prod (VectorBrownian.law (n+1)))).real E'
  rw [triple_prod_real_eq_integral_fibers _ _ _ E hE,
    triple_prod_real_eq_integral_fibers _ _ _ E' hE']
  apply integral_congr_ae
  apply ae_of_all
  intro g
  apply integral_congr_ae
  apply ae_of_all
  intro x
  exact (valuePosterior_overlap_horizon_fiber_eq_actual
    n μ Q u mark β S H hS a g x).trans
      (valuePosterior_overlap_horizon_fiber_eq_actual
        n μ Q u mark β S' H hS' a g x).symm

end SlowEquilibration.SphericalPosteriorGradientIndependence

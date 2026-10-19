-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureTruePosteriorPointwise
public import SlowEquilibration.ConditionedEntrancePureTrueRate
public import SlowEquilibration.ConditionedEntranceSourceTrueRateBridge
public import SlowEquilibration.ConditionedEntrancePureHorizonHitFibers
public import SlowEquilibration.SphericalTripleProductReal
public import SlowEquilibration.SphericalNormalizedLikelihoodLowerTail

/-! Equality of the actual value-posterior path-hit law and the original
tensor source Hamiltonian with constant cutoff one. This identifies the
probability observable needed by the centered critical-point transfer. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalPosteriorMaps SphericalDynamics
open SphericalPosteriorGradientIndependence SphericalOverlapExponential
open SphericalSmoothParameter SphericalTripleProductReal
open SphericalAging HardSphereDynamics WholeFieldRegression
open scoped NNReal
set_option autoImplicit false
set_option maxHeartbeats 900000

theorem valuePosterior_originalTrueCapHit_integral_eq_path_event
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) (mark : ℝ)
    (β : ℝ) (H S : ℝ≥0) (hHS : H ≤ S) (a : ℝ) :
    (∫ g, originalTrueCapHitProbability μ β H a u
      (unpackDisorder (valuePosterior n μ Q u mark g))
      ∂stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)) =
    (posteriorTrajectoryLaw n μ).real {q | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |valuePosteriorOverlapScore n μ Q u mark β S t q|} := by
  let E : Set (EuclideanDisorder (n+1) μ.maxDegree ×
      (Vector (n+1) × VectorBrownian.Space (n+1))) :=
    {q | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |valuePosteriorOverlapScore n μ Q u mark β S t q|}
  have hE : MeasurableSet E :=
    valuePosterior_overlap_horizon_hit_measurable n μ Q u mark β S H a
  change (∫ g, originalTrueCapHitProbability μ β H a u
    (unpackDisorder (valuePosterior n μ Q u mark g))
    ∂stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)) =
    ((stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)).prod
      ((sphereLaw (n+1)).prod (VectorBrownian.law (n+1)))).real E
  rw [triple_prod_real_eq_integral_fibers _ _ _ E hE]
  apply integral_congr_ae
  apply ae_of_all
  intro g
  change originalTrueCapHitProbability μ β H a u
      (unpackDisorder (valuePosterior n μ Q u mark g)) =
    ∫ x : Vector (n+1), (VectorBrownian.law (n+1)).real
      {ω | (g,(x,ω)) ∈ E} ∂sphereLaw (n+1)
  rw [originalTrueCapHitProbability_eq_mixedProcess_uniform]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  exact (valuePosterior_overlap_horizon_fiber_eq_actual
    n μ Q u mark β S H hHS a g x).symm

theorem pureSourceUncutCapHit_integral_eq_valuePosterior_path_event
    (n d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) {Q : ℝ} (hQ : 0 < Q)
    (u : Vector (n+1)) (hu : OnSphere u)
    (e a β : ℝ) (H S : ℝ≥0) (hHS : H ≤ S) :
    (∫ J, pureSourceCapHitProbability d hd c hc Q (2*a)
      (fun _ => 1) contDiff_const β H (J,(u,(e,0)))
      ∂disorderLaw (n+1) (FiniteMixture.pure d hd c hc).maxDegree) =
    (posteriorTrajectoryLaw n (FiniteMixture.pure d hd c hc)).real {q | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |valuePosteriorOverlapScore n (FiniteMixture.pure d hd c hc) Q u
        e β S t q|} := by
  let f : Disorder (n+1) (FiniteMixture.pure d hd c hc).maxDegree → ℝ := fun J =>
    pureSourceCapHitProbability d hd c hc Q (2*a) (fun _ => 1)
      contDiff_const β H (J,(u,(e,0)))
  have hfm : Measurable f := by
    exact (pureSourceCapHitProbability_measurable d hd c hc Q (2*a)
      (fun _ => 1) contDiff_const β H).comp
      (measurable_id.prodMk (measurable_const.prodMk
        (measurable_const.prodMk measurable_const)))
  calc
    (∫ J, f J ∂disorderLaw (n+1) (FiniteMixture.pure d hd c hc).maxDegree) =
        ∫ g, f (unpackDisorder g)
          ∂stdGaussian (EuclideanDisorder (n+1) (FiniteMixture.pure d hd c hc).maxDegree) := by
      simpa only [SYK.standardGaussianMeasureOnEuclidean,
        map_pi_eq_stdGaussian,Function.comp_def] using
        (unpackDisorder_hasLaw (n+1) (FiniteMixture.pure d hd c hc).maxDegree).integral_comp
          hfm.aestronglyMeasurable |>.symm
    _ = ∫ g, originalTrueCapHitProbability (FiniteMixture.pure d hd c hc) β H a u
          (unpackDisorder (valuePosterior n (FiniteMixture.pure d hd c hc) Q u
            e g))
          ∂stdGaussian (EuclideanDisorder (n+1) (FiniteMixture.pure d hd c hc).maxDegree) := by
      apply integral_congr_ae
      apply ae_of_all
      intro g
      simpa only [f,show (2*a)/2 = a by ring,unpackCLM_apply] using
        (originalTrueCapHitProbability_pureValuePosterior_eq_source_one
        n d hd c hc hQ u ((onSphere_iff_norm_sq u).mp hu)
        e (2*a) β H g).symm
    _ = _ := valuePosterior_originalTrueCapHit_integral_eq_path_event
      n (FiniteMixture.pure d hd c hc) Q u e β H S hHS a

end SlowEquilibration.ConditionedEntrance

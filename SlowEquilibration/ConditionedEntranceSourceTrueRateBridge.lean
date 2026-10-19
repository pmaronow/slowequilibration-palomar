-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceTruePosteriorPointwise
public import SlowEquilibration.ConditionedEntranceSourceTrueRate
public import SlowEquilibration.SphericalPosteriorHorizonHitFibers
public import SlowEquilibration.SphericalTripleProductReal
public import SlowEquilibration.SphericalNormalizedLikelihoodLowerTail

/-! Equality of the actual mixed-posterior path-hit law and the original
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

theorem originalTrueCapHitProbability_eq_mixedProcess_uniform
    (n : ℕ) (μ : FiniteMixture) (β : ℝ) (H : ℝ≥0) (a : ℝ)
    (u : Vector (n+1)) (J : Disorder (n+1) μ.maxDegree) :
    originalTrueCapHitProbability μ β H a u J =
      ∫ x : Vector (n+1), (VectorBrownian.law (n+1)).real
        {ω | ∃ t : ℝ≥0, t ≤ H ∧ a ≤
          |overlapValue u (mixedProcess μ J β x t ω)|}
        ∂sphereLaw (n+1) := by
  rw [originalTrueCapHitProbability,uniformCapHitProbability_eq_actual]
  apply integral_congr_ae
  filter_upwards [sphereLaw_support (by omega : 1 ≤ n+1)] with x hx
  apply measureReal_congr
  filter_upwards [mixedProcess_ae_C1Process (by omega : 1 ≤ n+1)
    μ J β x ((onSphere_iff_norm_sq x).mpr hx)] with ω he
  apply propext
  constructor <;> rintro ⟨t,ht,hh⟩ <;> refine ⟨t,ht,?_⟩
  · rw [he t,overlapValue_eq]
    exact hh
  · rw [he t,overlapValue_eq] at hh
    exact hh

theorem mixedPosterior_originalTrueCapHit_integral_eq_path_event
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) (marks : EuclideanSpace ℝ (Fin 2))
    (β : ℝ) (H S : ℝ≥0) (hHS : H ≤ S) (a : ℝ) :
    (∫ g, originalTrueCapHitProbability μ β H a u
      (unpackDisorder (mixedPosterior n μ Q u marks g))
      ∂stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)) =
    (posteriorTrajectoryLaw n μ).real {q | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |mixedPosteriorOverlapScore n μ Q u marks β S t q|} := by
  let E : Set (EuclideanDisorder (n+1) μ.maxDegree ×
      (Vector (n+1) × VectorBrownian.Space (n+1))) :=
    {q | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |mixedPosteriorOverlapScore n μ Q u marks β S t q|}
  have hE : MeasurableSet E :=
    mixedPosterior_overlap_horizon_hit_measurable n μ Q u marks β S H a
  change (∫ g, originalTrueCapHitProbability μ β H a u
    (unpackDisorder (mixedPosterior n μ Q u marks g))
    ∂stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)) =
    ((stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)).prod
      ((sphereLaw (n+1)).prod (VectorBrownian.law (n+1)))).real E
  rw [triple_prod_real_eq_integral_fibers _ _ _ E hE]
  apply integral_congr_ae
  apply ae_of_all
  intro g
  change originalTrueCapHitProbability μ β H a u
      (unpackDisorder (mixedPosterior n μ Q u marks g)) =
    ∫ x : Vector (n+1), (VectorBrownian.law (n+1)).real
      {ω | (g,(x,ω)) ∈ E} ∂sphereLaw (n+1)
  rw [originalTrueCapHitProbability_eq_mixedProcess_uniform]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  exact (mixedPosterior_overlap_horizon_fiber_eq_actual
    n μ Q u marks β S H hHS a g x).symm

theorem sourceUncutCapHit_integral_eq_mixedPosterior_path_event
    (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector (n+1)) (hu : OnSphere u)
    (e k a β : ℝ) (H S : ℝ≥0) (hHS : H ≤ S) :
    (∫ J, sourceCapHitProbability μ Q hQ hnp (2*a)
      (fun _ => 1) contDiff_const β H (J,(u,(e,k)))
      ∂disorderLaw (n+1) μ.maxDegree) =
    (posteriorTrajectoryLaw n μ).real {q | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |mixedPosteriorOverlapScore n μ Q u
        (SphericalMarkedWindows.scorePairEquiv (e,k)) β S t q|} := by
  let f : Disorder (n+1) μ.maxDegree → ℝ := fun J =>
    sourceCapHitProbability μ Q hQ hnp (2*a) (fun _ => 1)
      contDiff_const β H (J,(u,(e,k)))
  have hfm : Measurable f := by
    exact (sourceCapHitProbability_measurable μ Q hQ hnp (2*a)
      (fun _ => 1) contDiff_const β H).comp
      (measurable_id.prodMk (measurable_const.prodMk
        (measurable_const.prodMk measurable_const)))
  calc
    (∫ J, f J ∂disorderLaw (n+1) μ.maxDegree) =
        ∫ g, f (unpackDisorder g)
          ∂stdGaussian (EuclideanDisorder (n+1) μ.maxDegree) := by
      simpa only [SYK.standardGaussianMeasureOnEuclidean,
        map_pi_eq_stdGaussian,Function.comp_def] using
        (unpackDisorder_hasLaw (n+1) μ.maxDegree).integral_comp
          hfm.aestronglyMeasurable |>.symm
    _ = ∫ g, originalTrueCapHitProbability μ β H a u
          (unpackDisorder (mixedPosterior n μ Q u
            (SphericalMarkedWindows.scorePairEquiv (e,k)) g))
          ∂stdGaussian (EuclideanDisorder (n+1) μ.maxDegree) := by
      apply integral_congr_ae
      apply ae_of_all
      intro g
      simpa only [f,show (2*a)/2 = a by ring,unpackCLM_apply] using
        (originalTrueCapHitProbability_mixedPosterior_eq_source_one
        n μ hQ hnp u ((onSphere_iff_norm_sq u).mp hu)
        e k (2*a) β H g).symm
    _ = _ := mixedPosterior_originalTrueCapHit_integral_eq_path_event
      n μ Q u (SphericalMarkedWindows.scorePairEquiv (e,k)) β H S hHS a

end SlowEquilibration.ConditionedEntrance

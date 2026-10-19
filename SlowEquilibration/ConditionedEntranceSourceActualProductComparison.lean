-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceActualHitComparison
public import SlowEquilibration.ConditionedEntranceSourceCutoffFibre
public import SlowEquilibration.SphericalPosteriorHorizonHitFibers
public import SlowEquilibration.SphericalTripleProductFiberComparison
public import SlowEquilibration.SphericalNormalizedLikelihoodLowerTail

/-! The true posterior cap event is bounded under original Gaussian
coefficients, uniform sphere start, and Wiener noise by the source cutoff
cap probability and the original center-gradient exit event. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalPosteriorMaps SphericalMarkedWindows
open WholeFieldRegression
open SphericalPosteriorGradientIndependence SphericalOverlapExponential
open SphericalTripleProductReal SphericalAging HardSphereDynamics
open scoped NNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem actual_mixedPosterior_joint_cap_hit_le_sourceCutoff_add_gradient
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector (n+1)) (hu : OnSphere u)
    (e k a : ℝ) (ha : 0 < a) (β : ℝ) (H S : ℝ≥0) (hHS : H ≤ S) :
    (posteriorTrajectoryLaw n μ).real {q | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |mixedPosteriorOverlapScore n μ Q u (scorePairEquiv (e,k)) β S t q|} ≤
      (∫ J, sourceCapHitProbability μ Q hQ hnp (2*a)
          sourceScalarCutoff sourceScalarCutoff_contDiff_two β H
          (J,(u,(e,k))) ∂disorderLaw (n+1) μ.maxDegree) +
      (posteriorTrajectoryLaw n μ).real {q | ∃ t : ℝ≥0, t ≤ H ∧
        2*a ≤ |mixedPosteriorOriginalGradientScore n μ Q u
          (scorePairEquiv (e,k)) β S t q|} := by
  let marks := scorePairEquiv (e,k)
  let E : Set (EuclideanDisorder (n+1) μ.maxDegree ×
      (Vector (n+1) × VectorBrownian.Space (n+1))) :=
    {q | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |mixedPosteriorOverlapScore n μ Q u marks β S t q|}
  let G : Set (EuclideanDisorder (n+1) μ.maxDegree ×
      (Vector (n+1) × VectorBrownian.Space (n+1))) :=
    {q | ∃ t : ℝ≥0, t ≤ H ∧
      2*a ≤ |mixedPosteriorOriginalGradientScore n μ Q u marks β S t q|}
  let C : EuclideanDisorder (n+1) μ.maxDegree × Vector (n+1) → ℝ :=
    fun q => sourceCapHitFibre μ Q hQ hnp (2*a) sourceScalarCutoff
      sourceScalarCutoff_contDiff_two β H
      ((unpackDisorder q.1,(u,(e,k))),q.2)
  have hE : MeasurableSet E :=
    mixedPosterior_overlap_horizon_hit_measurable n μ Q u marks β S H a
  have hG : MeasurableSet G :=
    mixedPosterior_gradient_horizon_hit_measurable n μ Q u marks β S H (2*a)
  have hCm : Measurable C := by
    exact (sourceCapHitFibre_measurable μ Q hQ hnp (2*a)
      sourceScalarCutoff sourceScalarCutoff_contDiff_two β H).comp
        ((((unpackCLM (n+1) μ.maxDegree).continuous.measurable).comp measurable_fst).prodMk
          (measurable_const.prodMk (measurable_const.prodMk measurable_const)) |>.prodMk measurable_snd)
  have hCb (q : EuclideanDisorder (n+1) μ.maxDegree × Vector (n+1)) :
      ‖C q‖ ≤ 1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg
      (sourceCapHitFibre_mem_unit μ Q hQ hnp (2*a)
        sourceScalarCutoff sourceScalarCutoff_contDiff_two β H _).1]
    exact (sourceCapHitFibre_mem_unit μ Q hQ hnp (2*a)
      sourceScalarCutoff sourceScalarCutoff_contDiff_two β H _).2
  have hFiber (g : EuclideanDisorder (n+1) μ.maxDegree)
      (x : Vector (n+1)) (hx : OnSphere x) :
      (VectorBrownian.law (n+1)).real {ω | (g,(x,ω)) ∈ E} ≤
        C (g,x) + (VectorBrownian.law (n+1)).real {ω | (g,(x,ω)) ∈ G} := by
    have hTrue := mixedPosterior_overlap_horizon_fiber_eq_actual
      n μ Q u marks β S H hHS a g x
    have hGrad := mixedPosterior_gradient_horizon_fiber_eq_actual
      n μ Q u marks β S H hHS (2*a) g x
    have hCut := sourceCapHitFibre_eq_actual (by omega : 1 ≤ n+1)
      μ hnp Q hQ hQ1 (2*a) (mul_pos (by norm_num) ha)
      sourceScalarCutoff sourceScalarCutoff_contDiff_two β H
      (unpackDisorder g,(u,(e,k))) hu x
    have hPoint := actual_mixedPosterior_cap_hit_le_sourceCutoff_add_gradient
      n μ Q hQ hQ1 hnp g u hu e k a ha β x hx H
    have hCut' := by
      simpa only [show (2*a)/2 = a by ring] using hCut
    change (VectorBrownian.law (n+1)).real {ω | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |mixedPosteriorOverlapScore n μ Q u marks β S t (g,(x,ω))|} ≤
      sourceCapHitFibre μ Q hQ hnp (2*a) sourceScalarCutoff
        sourceScalarCutoff_contDiff_two β H ((unpackDisorder g,(u,(e,k))),x) +
      (VectorBrownian.law (n+1)).real {ω | ∃ t : ℝ≥0, t ≤ H ∧
        2*a ≤ |mixedPosteriorOriginalGradientScore n μ Q u marks β S t (g,(x,ω))|}
    rw [hTrue,hGrad,hCut']
    exact hPoint
  have hComparison := triple_prod_real_le_integral_add_of_fibers
    (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree))
    (sphereLaw (n+1)) (VectorBrownian.law (n+1))
    E G hE hG C hCm hCb {x | OnSphere x}
    ((sphereLaw_support (by omega : 1 ≤ n+1)).mono
      (fun x hx => (onSphere_iff_norm_sq x).mpr hx)) hFiber
  have hCutIntegral :
      (∫ g, ∫ x, C (g,x) ∂sphereLaw (n+1)
        ∂stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)) =
      ∫ J, sourceCapHitProbability μ Q hQ hnp (2*a)
        sourceScalarCutoff sourceScalarCutoff_contDiff_two β H
        (J,(u,(e,k))) ∂disorderLaw (n+1) μ.maxDegree := by
    let f : Disorder (n+1) μ.maxDegree → ℝ := fun J =>
      sourceCapHitProbability μ Q hQ hnp (2*a)
        sourceScalarCutoff sourceScalarCutoff_contDiff_two β H
        (J,(u,(e,k)))
    have hfm : Measurable f := by
      exact (sourceCapHitProbability_measurable μ Q hQ hnp (2*a)
        sourceScalarCutoff sourceScalarCutoff_contDiff_two β H).comp
        (measurable_id.prodMk (measurable_const.prodMk
          (measurable_const.prodMk measurable_const)))
    calc
      _ = ∫ g, f (unpackDisorder g)
          ∂stdGaussian (EuclideanDisorder (n+1) μ.maxDegree) := by
        apply integral_congr_ae
        apply ae_of_all
        intro g
        exact (sourceCapHitProbability_eq_integral_fibre μ Q hQ hnp (2*a)
          sourceScalarCutoff sourceScalarCutoff_contDiff_two β H
          (unpackDisorder g,(u,(e,k)))).symm
      _ = ∫ J, f J ∂disorderLaw (n+1) μ.maxDegree := by
        simpa only [SYK.standardGaussianMeasureOnEuclidean,
          map_pi_eq_stdGaussian,Function.comp_def] using
          (unpackDisorder_hasLaw (n+1) μ.maxDegree).integral_comp
            hfm.aestronglyMeasurable
  rw [hCutIntegral] at hComparison
  simpa only [posteriorTrajectoryLaw,marks,E,G] using hComparison

end SlowEquilibration.ConditionedEntrance

-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureActualHitComparison
public import SlowEquilibration.ConditionedEntrancePureCutoffFibre
public import SlowEquilibration.ConditionedEntrancePureHorizonHitFibers
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

theorem actual_pureValuePosterior_joint_cap_hit_le_sourceCutoff_add_gradient
    (n d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (Q : ℝ) (hQ : 0 < Q)
    (u : Vector (n+1)) (hu : OnSphere u)
    (e a : ℝ) (ha : 0 < a) (β : ℝ) (H S : ℝ≥0) (hHS : H ≤ S) :
    (posteriorTrajectoryLaw n (FiniteMixture.pure d hd c hc)).real {q | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |valuePosteriorOverlapScore n (FiniteMixture.pure d hd c hc) Q u e β S t q|} ≤
      (∫ J, pureSourceCapHitProbability d hd c hc Q (2*a)
          sourceScalarCutoff sourceScalarCutoff_contDiff_two β H
          (J,(u,(e,0))) ∂disorderLaw (n+1) (FiniteMixture.pure d hd c hc).maxDegree) +
      (posteriorTrajectoryLaw n (FiniteMixture.pure d hd c hc)).real {q | ∃ t : ℝ≥0, t ≤ H ∧
        2*a ≤ |valuePosteriorOriginalGradientScore n (FiniteMixture.pure d hd c hc) Q u
          e β S t q|} := by
  let E : Set (EuclideanDisorder (n+1) (FiniteMixture.pure d hd c hc).maxDegree ×
      (Vector (n+1) × VectorBrownian.Space (n+1))) :=
    {q | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |valuePosteriorOverlapScore n (FiniteMixture.pure d hd c hc) Q u e β S t q|}
  let G : Set (EuclideanDisorder (n+1) (FiniteMixture.pure d hd c hc).maxDegree ×
      (Vector (n+1) × VectorBrownian.Space (n+1))) :=
    {q | ∃ t : ℝ≥0, t ≤ H ∧
      2*a ≤ |valuePosteriorOriginalGradientScore n (FiniteMixture.pure d hd c hc) Q u e β S t q|}
  let C : EuclideanDisorder (n+1) (FiniteMixture.pure d hd c hc).maxDegree × Vector (n+1) → ℝ :=
    fun q => pureSourceCapHitFibre d hd c hc Q (2*a) sourceScalarCutoff
      sourceScalarCutoff_contDiff_two β H
      ((unpackDisorder q.1,(u,(e,0))),q.2)
  have hE : MeasurableSet E :=
    valuePosterior_overlap_horizon_hit_measurable n (FiniteMixture.pure d hd c hc) Q u e β S H a
  have hG : MeasurableSet G :=
    valuePosterior_gradient_horizon_hit_measurable n (FiniteMixture.pure d hd c hc) Q u e β S H (2*a)
  have hCm : Measurable C := by
    exact (pureSourceCapHitFibre_measurable d hd c hc Q (2*a)
      sourceScalarCutoff sourceScalarCutoff_contDiff_two β H).comp
        ((((unpackCLM (n+1) (FiniteMixture.pure d hd c hc).maxDegree).continuous.measurable).comp measurable_fst).prodMk
          (measurable_const.prodMk (measurable_const.prodMk measurable_const)) |>.prodMk measurable_snd)
  have hCb (q : EuclideanDisorder (n+1) (FiniteMixture.pure d hd c hc).maxDegree × Vector (n+1)) :
      ‖C q‖ ≤ 1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg
      (pureSourceCapHitFibre_mem_unit d hd c hc Q (2*a)
        sourceScalarCutoff sourceScalarCutoff_contDiff_two β H _).1]
    exact (pureSourceCapHitFibre_mem_unit d hd c hc Q (2*a)
      sourceScalarCutoff sourceScalarCutoff_contDiff_two β H _).2
  have hFiber (g : EuclideanDisorder (n+1) (FiniteMixture.pure d hd c hc).maxDegree)
      (x : Vector (n+1)) (hx : OnSphere x) :
      (VectorBrownian.law (n+1)).real {ω | (g,(x,ω)) ∈ E} ≤
        C (g,x) + (VectorBrownian.law (n+1)).real {ω | (g,(x,ω)) ∈ G} := by
    have hTrue := valuePosterior_overlap_horizon_fiber_eq_actual
      n (FiniteMixture.pure d hd c hc) Q u e β S H hHS a g x
    have hGrad := valuePosterior_gradient_horizon_fiber_eq_actual
      n (FiniteMixture.pure d hd c hc) Q u e β S H hHS (2*a) g x
    have hCut := pureSourceCapHitFibre_eq_actual (by omega : 1 ≤ n+1)
      d hd c hc Q (2*a) (mul_pos (by norm_num) ha)
      sourceScalarCutoff sourceScalarCutoff_contDiff_two β H
      (unpackDisorder g,(u,(e,0))) hu x
    have hPoint := actual_pureValuePosterior_cap_hit_le_sourceCutoff_add_gradient
      n d hd c hc Q hQ g u hu e a ha β x hx H
    have hCut' := by
      simpa only [show (2*a)/2 = a by ring] using hCut
    change (VectorBrownian.law (n+1)).real {ω | ∃ t : ℝ≥0, t ≤ H ∧
      a ≤ |valuePosteriorOverlapScore n (FiniteMixture.pure d hd c hc) Q u e β S t (g,(x,ω))|} ≤
      pureSourceCapHitFibre d hd c hc Q (2*a) sourceScalarCutoff
        sourceScalarCutoff_contDiff_two β H ((unpackDisorder g,(u,(e,0))),x) +
      (VectorBrownian.law (n+1)).real {ω | ∃ t : ℝ≥0, t ≤ H ∧
        2*a ≤ |valuePosteriorOriginalGradientScore n (FiniteMixture.pure d hd c hc) Q u e β S t (g,(x,ω))|}
    rw [hTrue,hGrad,hCut']
    exact hPoint
  have hComparison := triple_prod_real_le_integral_add_of_fibers
    (stdGaussian (EuclideanDisorder (n+1) (FiniteMixture.pure d hd c hc).maxDegree))
    (sphereLaw (n+1)) (VectorBrownian.law (n+1))
    E G hE hG C hCm hCb {x | OnSphere x}
    ((sphereLaw_support (by omega : 1 ≤ n+1)).mono
      (fun x hx => (onSphere_iff_norm_sq x).mpr hx)) hFiber
  have hCutIntegral :
      (∫ g, ∫ x, C (g,x) ∂sphereLaw (n+1)
        ∂stdGaussian (EuclideanDisorder (n+1) (FiniteMixture.pure d hd c hc).maxDegree)) =
      ∫ J, pureSourceCapHitProbability d hd c hc Q (2*a)
        sourceScalarCutoff sourceScalarCutoff_contDiff_two β H
        (J,(u,(e,0))) ∂disorderLaw (n+1) (FiniteMixture.pure d hd c hc).maxDegree := by
    let f : Disorder (n+1) (FiniteMixture.pure d hd c hc).maxDegree → ℝ := fun J =>
      pureSourceCapHitProbability d hd c hc Q (2*a)
        sourceScalarCutoff sourceScalarCutoff_contDiff_two β H
        (J,(u,(e,0)))
    have hfm : Measurable f := by
      exact (pureSourceCapHitProbability_measurable d hd c hc Q (2*a)
        sourceScalarCutoff sourceScalarCutoff_contDiff_two β H).comp
        (measurable_id.prodMk (measurable_const.prodMk
          (measurable_const.prodMk measurable_const)))
    calc
      _ = ∫ g, f (unpackDisorder g)
          ∂stdGaussian (EuclideanDisorder (n+1) (FiniteMixture.pure d hd c hc).maxDegree) := by
        apply integral_congr_ae
        apply ae_of_all
        intro g
        exact (pureSourceCapHitProbability_eq_integral_fibre d hd c hc Q (2*a)
          sourceScalarCutoff sourceScalarCutoff_contDiff_two β H
          (unpackDisorder g,(u,(e,0)))).symm
      _ = ∫ J, f J ∂disorderLaw (n+1) (FiniteMixture.pure d hd c hc).maxDegree := by
        simpa only [SYK.standardGaussianMeasureOnEuclidean,
          map_pi_eq_stdGaussian,Function.comp_def] using
          (unpackDisorder_hasLaw (n+1) (FiniteMixture.pure d hd c hc).maxDegree).integral_comp
            hfm.aestronglyMeasurable
  rw [hCutIntegral] at hComparison
  simpa only [posteriorTrajectoryLaw,E,G] using hComparison

end SlowEquilibration.ConditionedEntrance

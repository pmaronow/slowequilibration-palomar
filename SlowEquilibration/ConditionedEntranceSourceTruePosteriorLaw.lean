-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceTruePosteriorPointwise
public import SlowEquilibration.ConditionedDeterminantMoments
public import SlowEquilibration.SphericalNormalizedLikelihoodLowerTail

/-! Exact ordinary-posterior entrance probability transport: the true
original-field diffusion under the canonical mixed conditioned law has the
same expected cap hit as the unconditioned source corrected field. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet SphericalMarkedWindows
open SphericalPosteriorMaps WholeFieldRegression SphericalCriticalLatitude
open ConditionedDeterminantMoments
open scoped NNReal
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem originalTrueCapHitProbability_mixedPalm_integral_eq_source_one
    (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1:ℕ):ℝ))
    (e k α β : ℝ) (T : ℝ≥0) :
    (∫ J, originalTrueCapHitProbability μ β T (α/2) u J
      ∂mixedConditionedLaw
        (centerCoefficients (mixtureCoefficients μ) Q) u hu
        (scorePairEquiv (e,k))) =
    ∫ J, sourceCapHitProbability μ Q hQ hnp α (fun _ => 1)
      contDiff_const β T (J,(u,(e,k)))
      ∂disorderLaw (n+1) μ.maxDegree := by
  let b := scorePairEquiv (e,k)
  let F : Disorder (n+1) μ.maxDegree → ℝ :=
    originalTrueCapHitProbability μ β T (α/2) u
  let G : Disorder (n+1) μ.maxDegree → ℝ := fun J =>
    sourceCapHitProbability μ Q hQ hnp α (fun _ => 1)
      contDiff_const β T (J,(u,(e,k)))
  have hFm : Measurable F :=
    originalTrueCapHitProbability_measurable μ β T (α/2) u
  have hGm : Measurable G :=
    (sourceCapHitProbability_measurable μ Q hQ hnp α
      (fun _ => 1) contDiff_const β T).comp
      (measurable_id.prodMk (measurable_const.prodMk
        (measurable_const.prodMk measurable_const)))
  have hparam : Continuous (fun g : EuclideanDisorder (n+1) μ.maxDegree =>
      ((u,b),g)) := by fun_prop
  have hMap : Measurable (fun g : EuclideanDisorder (n+1) μ.maxDegree =>
      unpackCLM (n+1) μ.maxDegree (mixedPosterior n μ Q u b g)) := by
    exact ((unpackCLM _ _).continuous.comp
      ((mixedPosterior_continuous n μ Q).comp hparam)).measurable
  change (∫ J, F J ∂mixedConditionedLaw
    (centerCoefficients (mixtureCoefficients μ) Q) u hu b) =
    ∫ J, G J ∂disorderLaw (n+1) μ.maxDegree
  rw [mixedConditionedLaw_eq_map n μ hQ hnp u hu b,
    integral_map hMap.aemeasurable hFm.aestronglyMeasurable]
  have hPoint (g : EuclideanDisorder (n+1) μ.maxDegree) :
      F (unpackCLM (n+1) μ.maxDegree (mixedPosterior n μ Q u b g)) =
      G (unpackDisorder g) :=
    originalTrueCapHitProbability_mixedPosterior_eq_source_one
      n μ hQ hnp u hu e k α β T g
  calc
    (∫ g, F (unpackCLM (n+1) μ.maxDegree
        (mixedPosterior n μ Q u b g))
      ∂stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)) =
      ∫ g, G (unpackDisorder g)
        ∂stdGaussian (EuclideanDisorder (n+1) μ.maxDegree) :=
          integral_congr_ae (.of_forall hPoint)
    _ = ∫ J, G J ∂disorderLaw (n+1) μ.maxDegree := by
      simpa only [SYK.standardGaussianMeasureOnEuclidean,
        map_pi_eq_stdGaussian,Function.comp_def] using
        (unpackDisorder_hasLaw (n+1) μ.maxDegree).integral_comp
          hGm.aestronglyMeasurable

end SlowEquilibration.ConditionedEntrance

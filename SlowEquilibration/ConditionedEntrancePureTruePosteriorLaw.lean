-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureTruePosteriorPointwise
public import SlowEquilibration.ConditionedEntranceSourceTruePosteriorLaw

/-! The true original-field cap-hit expectation under the proper pure
value/tangent conditioned law equals the uncut pure source expectation. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet
open SphericalPosteriorMaps WholeFieldRegression SphericalMarkedWindows
open scoped NNReal
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem originalTrueCapHitProbability_pureValuePalm_integral_eq_source_one
    (n p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q : ℝ} (hQ : 0 < Q)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1:ℕ):ℝ))
    (e α β : ℝ) (T : ℝ≥0) :
    let μ := FiniteMixture.pure p hp c hc
    (∫ J, originalTrueCapHitProbability μ β T (α/2) u J
      ∂valueConditionedLaw
        (centerCoefficients (mixtureCoefficients μ) Q) u hu e) =
    ∫ J, pureSourceCapHitProbability p hp c hc Q α (fun _ => 1)
      contDiff_const β T (J,(u,(e,0)))
      ∂disorderLaw (n+1) μ.maxDegree := by
  dsimp only
  let μ := FiniteMixture.pure p hp c hc
  let F : Disorder (n+1) μ.maxDegree → ℝ :=
    originalTrueCapHitProbability μ β T (α/2) u
  let G : Disorder (n+1) μ.maxDegree → ℝ := fun J =>
    pureSourceCapHitProbability p hp c hc Q α (fun _ => 1)
      contDiff_const β T (J,(u,(e,0)))
  have hFm : Measurable F :=
    originalTrueCapHitProbability_measurable μ β T (α/2) u
  have hGm : Measurable G :=
    (pureSourceCapHitProbability_measurable p hp c hc Q α
      (fun _ => 1) contDiff_const β T).comp
      (measurable_id.prodMk (measurable_const.prodMk
        (measurable_const.prodMk measurable_const)))
  have hparam : Continuous (fun g : EuclideanDisorder (n+1) μ.maxDegree =>
      ((u,e),g)) := by fun_prop
  have hMap : Measurable (fun g : EuclideanDisorder (n+1) μ.maxDegree =>
      unpackCLM (n+1) μ.maxDegree (valuePosterior n μ Q u e g)) := by
    exact ((unpackCLM _ _).continuous.comp
      ((valuePosterior_continuous n μ Q).comp hparam)).measurable
  change (∫ J, F J ∂valueConditionedLaw
    (centerCoefficients (mixtureCoefficients μ) Q) u hu e) =
    ∫ J, G J ∂disorderLaw (n+1) μ.maxDegree
  rw [valueConditionedLaw_eq_map n μ hQ u hu e,
    integral_map hMap.aemeasurable hFm.aestronglyMeasurable]
  have hPoint (g : EuclideanDisorder (n+1) μ.maxDegree) :
      F (unpackCLM (n+1) μ.maxDegree (valuePosterior n μ Q u e g)) =
      G (unpackDisorder g) :=
    originalTrueCapHitProbability_pureValuePosterior_eq_source_one
      n p hp c hc hQ u hu e α β T g
  calc
    (∫ g, F (unpackCLM (n+1) μ.maxDegree
        (valuePosterior n μ Q u e g))
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

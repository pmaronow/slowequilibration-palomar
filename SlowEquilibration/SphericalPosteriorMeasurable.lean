-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPosteriorMaps

/-! Borel dependence of genuine full-field conditioned expectations on position and marks. -/

@[expose] public section
namespace SlowEquilibration.SphericalPosteriorMaps
open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalGaussianJet WholeFieldRegression IntrinsicGradientRegression
open SphericalMarkedWindows
open scoped ENNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

/-- Every Borel full-disorder mark has a jointly Borel mixed conditioned
expectation on the actual sphere and every physical score target. -/
theorem mixed_posterior_lintegral_measurable (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (psi : Disorder (n+1) μ.maxDegree → SpherePoint n → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder (n+1) μ.maxDegree × SpherePoint n => psi p.1 p.2) :
    Measurable (fun p : SpherePoint n × EuclideanSpace ℝ (Fin 2) =>
      ∫⁻ J, psi J p.1 ∂mixedConditionedLaw (n := n)
        (centerCoefficients (mixtureCoefficients μ) Q) (p.1 : Vector (n+1)) p.1.2 p.2) := by
  have hm : Measurable (fun p : (SpherePoint n × EuclideanSpace ℝ (Fin 2)) ×
      EuclideanDisorder (n+1) μ.maxDegree =>
      psi (unpackCLM (n+1) μ.maxDegree (mixedPosterior n μ Q p.1.1 p.1.2 p.2)) p.1.1) := by
    have hparam : Continuous (fun p : (SpherePoint n × EuclideanSpace ℝ (Fin 2)) ×
        EuclideanDisorder (n+1) μ.maxDegree => (((p.1.1 : Vector (n+1)), p.1.2), p.2)) := by
      fun_prop
    have hc := (mixedPosterior_continuous n μ Q).comp hparam
    have hJ : Measurable (fun p : (SpherePoint n × EuclideanSpace ℝ (Fin 2)) × EuclideanDisorder (n+1) μ.maxDegree =>
        unpackCLM (n+1) μ.maxDegree (mixedPosterior n μ Q p.1.1 p.1.2 p.2)) := by
      simpa only [Function.comp_def] using (unpackCLM _ _).continuous.measurable.comp hc.measurable
    simpa only [Function.comp_def] using hpsi.comp (hJ.prodMk measurable_fst.fst)
  have h := hm.lintegral_prod_right' (ν := stdGaussian (EuclideanDisorder (n+1) μ.maxDegree))
  convert h using 1
  funext p
  have hmark : Measurable (fun J => psi J p.1) := by
    simpa only [Function.comp_def, id_eq] using
      hpsi.comp (measurable_id.prodMk (measurable_const (a := p.1)))
  have hparam : Continuous (fun g : EuclideanDisorder (n+1) μ.maxDegree =>
      (((p.1 : Vector (n+1)), p.2), g)) := by fun_prop
  have hmap : Measurable (fun g => unpackCLM (n+1) μ.maxDegree
      (mixedPosterior n μ Q p.1 p.2 g)) := by
    simpa only [Function.comp_def] using ((unpackCLM _ _).continuous.comp
      ((mixedPosterior_continuous n μ Q).comp hparam)).measurable
  rw [mixedConditionedLaw_eq_map n μ hQ hnp p.1 p.1.2 p.2, lintegral_map hmark hmap]

/-- The proper scalar posterior is jointly Borel, including every pure mixture. -/
theorem value_posterior_lintegral_measurable (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q)
    (psi : Disorder (n+1) μ.maxDegree → SpherePoint n → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder (n+1) μ.maxDegree × SpherePoint n => psi p.1 p.2) :
    Measurable (fun p : SpherePoint n × ℝ =>
      ∫⁻ J, psi J p.1 ∂valueConditionedLaw (n := n)
        (centerCoefficients (mixtureCoefficients μ) Q) (p.1 : Vector (n+1)) p.1.2 p.2) := by
  have hm : Measurable (fun p : (SpherePoint n × ℝ) × EuclideanDisorder (n+1) μ.maxDegree =>
      psi (unpackCLM (n+1) μ.maxDegree (valuePosterior n μ Q p.1.1 p.1.2 p.2)) p.1.1) := by
    have hparam : Continuous (fun p : (SpherePoint n × ℝ) ×
        EuclideanDisorder (n+1) μ.maxDegree => (((p.1.1 : Vector (n+1)), p.1.2), p.2)) := by
      fun_prop
    have hc := (valuePosterior_continuous n μ Q).comp hparam
    have hJ : Measurable (fun p : (SpherePoint n × ℝ) × EuclideanDisorder (n+1) μ.maxDegree =>
        unpackCLM (n+1) μ.maxDegree (valuePosterior n μ Q p.1.1 p.1.2 p.2)) := by
      simpa only [Function.comp_def] using (unpackCLM _ _).continuous.measurable.comp hc.measurable
    simpa only [Function.comp_def] using hpsi.comp (hJ.prodMk measurable_fst.fst)
  have h := hm.lintegral_prod_right' (ν := stdGaussian (EuclideanDisorder (n+1) μ.maxDegree))
  convert h using 1
  funext p
  have hmark : Measurable (fun J => psi J p.1) := by
    simpa only [Function.comp_def, id_eq] using
      hpsi.comp (measurable_id.prodMk (measurable_const (a := p.1)))
  have hparam : Continuous (fun g : EuclideanDisorder (n+1) μ.maxDegree =>
      (((p.1 : Vector (n+1)), p.2), g)) := by fun_prop
  have hmap : Measurable (fun g => unpackCLM (n+1) μ.maxDegree
      (valuePosterior n μ Q p.1 p.2 g)) := by
    simpa only [Function.comp_def] using ((unpackCLM _ _).continuous.comp
      ((valuePosterior_continuous n μ Q).comp hparam)).measurable
  rw [valueConditionedLaw_eq_map n μ hQ p.1 p.1.2 p.2, lintegral_map hmark hmap]

/-- Borel dependence of literal zero-intrinsic-gradient conditioning on the
actual sphere, retaining arbitrary marks of all original tensor coefficients. -/
theorem zero_posterior_lintegral_measurable (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q)
    (psi : Disorder (n+1) μ.maxDegree → SpherePoint n → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder (n+1) μ.maxDegree × SpherePoint n => psi p.1 p.2) :
    Measurable (fun x : SpherePoint n =>
      ∫⁻ J, psi J x ∂coefficientKernel
        (intrinsicGamma (centerCoefficients (mixtureCoefficients μ) Q) x) 0) := by
  have hm : Measurable (fun p : SpherePoint n × EuclideanDisorder (n+1) μ.maxDegree =>
      psi (unpackCLM (n+1) μ.maxDegree (gradientResidual n μ Q p.1 p.2)) p.1) := by
    have hparam : Continuous (fun p : SpherePoint n × EuclideanDisorder (n+1) μ.maxDegree =>
        (p.1 : Vector (n+1))) := by fun_prop
    have hc := ((gradientResidual_continuous n μ Q).comp hparam).clm_apply continuous_snd
    have hJ : Measurable (fun p : SpherePoint n × EuclideanDisorder (n+1) μ.maxDegree =>
        unpackCLM (n+1) μ.maxDegree (gradientResidual n μ Q p.1 p.2)) := by
      simpa only [Function.comp_def] using (unpackCLM _ _).continuous.measurable.comp hc.measurable
    simpa only [Function.comp_def] using hpsi.comp (hJ.prodMk measurable_fst)
  have h := hm.lintegral_prod_right' (ν := stdGaussian (EuclideanDisorder (n+1) μ.maxDegree))
  convert h using 1
  funext x
  have hmark : Measurable (fun J => psi J x) := by
    simpa only [Function.comp_def, id_eq] using
      hpsi.comp (measurable_id.prodMk (measurable_const (a := x)))
  have hmap : Measurable (fun g => unpackCLM (n+1) μ.maxDegree
      (gradientResidual n μ Q x g)) := by
    simpa only [Function.comp_def] using ((unpackCLM _ _).continuous.comp
      (gradientResidual n μ Q x).continuous).measurable
  rw [intrinsic_zero_kernel_eq_map n μ hQ x x.2, lintegral_map hmark hmap]

end
end SlowEquilibration.SphericalPosteriorMaps

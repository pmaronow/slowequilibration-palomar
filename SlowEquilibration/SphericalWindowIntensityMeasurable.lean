-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCriticalDetMeasurable

/-! Borel determinant-weighted posterior expectations and physical window intensities. -/
@[expose] public section
namespace SlowEquilibration.SphericalMarkedWindows
open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalGaussianJet WholeFieldRegression IntrinsicGradientRegression
open SphereHessian SphericalForm SphericalPosteriorMaps SphericalSequentialRegression
open IntrinsicHessianLaw ConditionedIntrinsicHessian PureConditionedHessian
open scoped ENNReal Topology RealInnerProductSpace
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

lemma criticalDet_sphere_measurable {P : ℕ} (n : ℕ) (c : Degree P → ℝ) :
    Measurable (fun p : Disorder (n+1) P × SpherePoint n => criticalDet n c p.1 p.2) := by
  simpa only [Function.comp_def] using (criticalDet_measurable n c).comp
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))

/-- The actual determinant-weighted mixed posterior integral is jointly Borel. -/
theorem mixed_det_posterior_measurable (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (psi : Disorder (n+1) μ.maxDegree → SpherePoint n → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder (n+1) μ.maxDegree × SpherePoint n => psi p.1 p.2) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    Measurable (fun p : SpherePoint n × EuclideanSpace ℝ (Fin 2) =>
      ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) (p.1 : Vector (n+1))).det| * psi J p.1
        ∂mixedConditionedLaw (n := n) c p.1 p.1.2 p.2) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hm := (criticalDet_sphere_measurable n c).ennreal_ofReal.mul hpsi
  have h := mixed_posterior_lintegral_measurable n μ hQ hnp
    (fun J x => ENNReal.ofReal (criticalDet n c J x) * psi J x) hm
  convert h using 1
  funext p
  apply lintegral_congr_ae
  filter_upwards [conditioned_critical_ae (n := n) μ hQ hnp p.1 p.1.2
    (jointScoreTarget n (((n+1 : ℕ) : ℝ) • p.2)) (fun _ => rfl)] with J hJ
  rw [criticalDet_eq n c J p.1 p.1.2 hJ]

/-- The actual determinant-weighted proper value posterior integral is jointly Borel. -/
theorem value_det_posterior_measurable (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q)
    (psi : Disorder (n+1) μ.maxDegree → SpherePoint n → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder (n+1) μ.maxDegree × SpherePoint n => psi p.1 p.2) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    Measurable (fun p : SpherePoint n × ℝ =>
      ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) (p.1 : Vector (n+1))).det| * psi J p.1
        ∂valueConditionedLaw (n := n) c p.1 p.1.2 p.2) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hm := (criticalDet_sphere_measurable n c).ennreal_ofReal.mul hpsi
  have h := value_posterior_lintegral_measurable n μ hQ
    (fun J x => ENNReal.ofReal (criticalDet n c J x) * psi J x) hm
  convert h using 1
  funext p
  apply lintegral_congr_ae
  filter_upwards [valueTangent_conditioned_critical_ae (n := n) μ hQ p.1 p.1.2 p.2] with J hJ
  rw [criticalDet_eq n c J p.1 p.1.2 hJ]

/-- The actual determinant-weighted zero-gradient posterior is Borel in position. -/
theorem zero_det_posterior_measurable (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q)
    (psi : Disorder (n+1) μ.maxDegree → SpherePoint n → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder (n+1) μ.maxDegree × SpherePoint n => psi p.1 p.2) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    Measurable (fun x : SpherePoint n =>
      ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) (x : Vector (n+1))).det| * psi J x
        ∂coefficientKernel (intrinsicGamma c x) 0) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hm := (criticalDet_sphere_measurable n c).ennreal_ofReal.mul hpsi
  have h := zero_posterior_lintegral_measurable n μ hQ
    (fun J x => ENNReal.ofReal (criticalDet n c J x) * psi J x) hm
  convert h using 1
  funext x
  apply lintegral_congr_ae
  filter_upwards [intrinsicKernel_critical_ae (N := n+1) (by omega) μ hQ x x.2] with J hJ
  rw [criticalDet_eq n c J x x.2 hJ]

lemma physicalScorePdf_measurable (N : ℕ) (μ : FiniteMixture) (Q : ℝ) :
    Measurable (physicalScorePdf N μ Q) := by
  unfold physicalScorePdf scoreQuadratic dotProduct Matrix.mulVec
  fun_prop

lemma physicalValuePdf_measurable (N : ℕ) (μ : FiniteMixture) (Q : ℝ) :
    Measurable (physicalValuePdf N μ Q) := by
  unfold physicalValuePdf
  fun_prop

lemma spherePoint_measurableSet (n : ℕ) : MeasurableSet (SpherePoint n) :=
  measurableSet_eq_fun (by fun_prop) measurable_const

/-- The literal ambient version of the source's mixed window intensity is Borel. -/
theorem mixedWindowIntensity_measurable (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (K : Set (EuclideanSpace ℝ (Fin 2)))
    (psi : Disorder (n+1) μ.maxDegree → Vector (n+1) → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder (n+1) μ.maxDegree × Vector (n+1) => psi p.1 p.2) :
    Measurable (mixedWindowIntensity n μ Q K psi) := by
  have hmark : Measurable (fun p : Disorder (n+1) μ.maxDegree × SpherePoint n => psi p.1 p.2) := by
    simpa only [Function.comp_def] using hpsi.comp
      (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))
  have hpost := mixed_det_posterior_measurable n μ hQ hnp (fun J x => psi J x) hmark
  have hprod := ((physicalScorePdf_measurable (n+1) μ Q).comp measurable_snd).mul hpost
  exact (hprod.lintegral_prod_right' (ν := volume.restrict K)).dite measurable_const
    (spherePoint_measurableSet n)

/-- Proper scalar window intensities are Borel for every mixture. -/
theorem valueWindowIntensity_measurable (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (I : Set ℝ)
    (psi : Disorder (n+1) μ.maxDegree → Vector (n+1) → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder (n+1) μ.maxDegree × Vector (n+1) => psi p.1 p.2) :
    Measurable (valueWindowIntensity n μ Q I psi) := by
  have hmark : Measurable (fun p : Disorder (n+1) μ.maxDegree × SpherePoint n => psi p.1 p.2) := by
    simpa only [Function.comp_def] using hpsi.comp
      (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))
  have hpost := value_det_posterior_measurable n μ hQ (fun J x => psi J x) hmark
  have hprod := ((physicalValuePdf_measurable (n+1) μ Q).comp measurable_snd).mul hpost
  exact (hprod.lintegral_prod_right' (ν := volume.restrict I)).dite measurable_const
    (spherePoint_measurableSet n)

end
end SlowEquilibration.SphericalMarkedWindows

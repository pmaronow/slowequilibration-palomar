-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianVectorAffineMoments
public import SlowEquilibration.GaussianPosteriorIndependence

/-! Actual norm-moment transport through Gaussian posterior centering,
retaining the whole original coefficient field and deterministic mean. -/
@[expose] public section
namespace SlowEquilibration.GaussianVectorPolynomialMoments
noncomputable section
open Function MeasureTheory ProbabilityTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

lemma norm_shift_moment_of_norm_moment {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (r : ℕ) {C M : ℝ} (hInt : Integrable (fun x:E=>‖x‖^r) μ)
    (hMom : (∫ x,‖x‖^r ∂μ) ≤ C) (m : E) (hm : ‖m‖ ≤ M) :
    Integrable (fun x:E=>‖x+m‖^r) μ ∧
      (∫ x,‖x+m‖^r ∂μ) ≤ (2:ℝ)^r*(C+M^r) := by
  have hmPow : ‖m‖^r ≤ M^r:=pow_le_pow_left₀ (norm_nonneg _) hm _
  have hpoint (x:E) : ‖x+m‖^r ≤ (2:ℝ)^r*(‖x‖^r+M^r) :=
    (norm_add_power_le x m r).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hmPow) (by positivity))
  have hdom : Integrable (fun x:E=>(2:ℝ)^r*(‖x‖^r+M^r)) μ:=(hInt.add (integrable_const (M^r))).const_mul _
  have hi : Integrable (fun x:E=>‖x+m‖^r) μ:=hdom.mono'
    ((continuous_id.add continuous_const).norm.pow r).measurable.aestronglyMeasurable
    (ae_of_all _ (fun x=>by simpa only [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)] using hpoint x))
  refine ⟨hi,?_⟩
  have hh:=integral_mono_ae hi hdom (ae_of_all _ hpoint)
  change (∫ x,‖x+m‖^r ∂μ) ≤ ∫ x,(2:ℝ)^r*(‖x‖^r+M^r) ∂μ at hh
  rw [integral_const_mul,integral_add hInt (integrable_const _),integral_const,probReal_univ,one_smul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add hMom le_rfl) (by positivity))

end
end SlowEquilibration.GaussianVectorPolynomialMoments

namespace SlowEquilibration.SphericalConditionalMatrices
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel WholeFieldRegression GaussianRegression
open GaussianRegressionCovariance GaussianVectorPolynomialMoments
variable {N P : ℕ} {F G : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]

/-- Exact actual full-field posterior norm transport: true centered-law
moments give moments of the literal object, with the actual lift mean retained. -/
theorem coefficientKernel_norm_moment_of_centered_moment
    (A : EuclideanDisorder N P →L[ℝ] F) (B : EuclideanDisorder N P →L[ℝ] G) (w : F)
    (r : ℕ) {C M : ℝ}
    (hInt : Integrable (fun u:G=>‖u‖^r) (centeredLaw A B))
    (hMom : (∫ u,‖u‖^r ∂centeredLaw A B) ≤ C) (hm : ‖B (lift A w)‖ ≤ M) :
    Integrable (fun J:Disorder N P=>‖actualObservation B J‖^r) (coefficientKernel A w) ∧
      (∫ J,‖actualObservation B J‖^r ∂coefficientKernel A w) ≤ (2:ℝ)^r*(C+M^r) := by
  have h:=norm_shift_moment_of_norm_moment (centeredLaw A B) r hInt hMom (B (lift A w)) hm
  have hL:=centered_actualObservation_hasLaw A B w
  constructor
  · simpa only [sub_add_cancel] using hL.integrable_fun_comp h.1
  · have hPhi : Measurable (fun u:G=>‖u+B (lift A w)‖^r) :=
      ((continuous_id.add continuous_const).norm.pow r).measurable
    have he:=hL.integral_comp hPhi.aestronglyMeasurable
    simpa only [Function.comp_def,sub_add_cancel] using he.trans_le h.2

end
end SlowEquilibration.SphericalConditionalMatrices

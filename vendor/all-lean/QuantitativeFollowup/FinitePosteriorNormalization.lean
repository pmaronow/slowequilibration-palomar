module
public import QuantitativeFollowup.PosteriorNormalization
public import QuantitativeFollowup.FinitePosteriorBL

@[expose] public section

/-! Actual normalized posterior probability and canonical inverse-Hessian
variance bound on an arbitrary nonempty finite Euclidean coordinate set. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace QuantitativeFollowup
set_option maxSynthPendingDepth 128
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem posteriorNormalizer_pos_finite     (V : EuclideanSpace ℝ ι → ℝ)
    (hi : Integrable (fun x => Real.exp (-V x))) : 0<posteriorNormalizer V :=
  integral_exp_pos hi


theorem normalizedPosteriorMeasure_probability_finite     (V : EuclideanSpace ℝ ι → ℝ)
    (hi : Integrable (fun x => Real.exp (-V x))) :
    IsProbabilityMeasure (normalizedPosteriorMeasure V) := by
  have hp := posteriorNormalizer_pos_finite V hi
  have heq : (fun x => Real.exp (-normalizedPosteriorPotential V x))=
      (fun x => Real.exp (-V x)/posteriorNormalizer V) := by
    funext x
    exact exp_neg_normalizedPosteriorPotential V hp x
  have hi' : Integrable (fun x => Real.exp (-normalizedPosteriorPotential V x)) :=
    heq.symm ▸ hi.div_const _
  have hz : (∫ x, Real.exp (-normalizedPosteriorPotential V x))=1 := by
    simp_rw [heq,div_eq_mul_inv]
    rw [integral_mul_const]
    exact mul_inv_cancel₀ hp.ne'
  constructor
  rw [normalizedPosteriorMeasure,posteriorDensityMeasure,withDensity_apply _
    MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal hi' (.of_forall fun x => (Real.exp_pos _).le),hz]
  simp


theorem normalized_posterior_brascamp_lieb_finite     (V f : EuclideanSpace ℝ ι → ℝ)
    (hi : Integrable (fun x => Real.exp (-V x)))
    (hV : ContDiff ℝ 4 V) (hf : ContDiff ℝ 3 f)
    (r A₁ A₂ B₀ B₁ B₂ Kf : ℝ)
    (hr : 0<r) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hKf : 0 ≤ Kf)
    (hcoercive : ∀ x z, r*‖z‖^2 ≤ directionalHessian V x z)
    (hfb : ∀ x, |f x| ≤ Kf)
    (ha₁ : ∀ x z, ‖fderiv ℝ (hessianOperator V) x z‖ ≤ A₁*‖z‖)
    (ha₂ : ∀ x z, ‖fderiv ℝ (fderiv ℝ (hessianOperator V)) x z z‖ ≤ A₂*‖z‖^2)
    (hb₀ : ∀ x, ‖gradient f x‖ ≤ B₀)
    (hb₁ : ∀ x z, ‖fderiv ℝ (gradient f) x z‖ ≤ B₁*‖z‖)
    (hb₂ : ∀ x z, ‖fderiv ℝ (fderiv ℝ (gradient f)) x z z‖ ≤ B₂*‖z‖^2) :
    variance f (normalizedPosteriorMeasure V) ≤
      ∫ x, inner ℝ (gradient f x) ((Ring.inverse (hessianOperator V x))
        (gradient f x)) ∂normalizedPosteriorMeasure V := by
  haveI : IsProbabilityMeasure (posteriorDensityMeasure (normalizedPosteriorPotential V)) :=
    normalizedPosteriorMeasure_probability_finite V hi
  have hhc (x z : EuclideanSpace ℝ ι) :
      directionalHessian (normalizedPosteriorPotential V) x z=directionalHessian V x z := by
    unfold directionalHessian
    have hd : fderiv ℝ (normalizedPosteriorPotential V)=fderiv ℝ V := by
      funext x
      exact fderiv_add_const _
    rw [hd]
  change variance f (posteriorDensityMeasure (normalizedPosteriorPotential V)) ≤ _
  have hh := posterior_brascamp_lieb_canonical_finite (normalizedPosteriorPotential V) f
    (hV.add contDiff_const) hf r A₁ A₂ B₀ B₁ B₂ Kf
    hr hA₁ hA₂ hB₀ hB₁ hB₂ hKf
    (fun x z => by rw [hhc]; exact hcoercive x z) hfb
    (by rw [hessianOperator_normalizedPosteriorPotential]; exact ha₁)
    (by rw [hessianOperator_normalizedPosteriorPotential]; exact ha₂) hb₀ hb₁ hb₂
  simpa only [hessianOperator_normalizedPosteriorPotential,normalizedPosteriorMeasure] using hh

end QuantitativeFollowup

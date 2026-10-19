module
public import QuantitativeFollowup.CanonicalPosteriorBL

@[expose] public section

/-! Actual normalization of a posterior density. A probability instance
is proved from its positive, finite partition integral. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace QuantitativeFollowup

def posteriorNormalizer {E : Type*} [MeasureSpace E] (V : E → ℝ) : ℝ :=
  ∫ x, Real.exp (-V x)

def normalizedPosteriorPotential {E : Type*} [MeasureSpace E] (V : E → ℝ) (x : E) : ℝ :=
  V x+Real.log (posteriorNormalizer V)

def normalizedPosteriorMeasure {E : Type*} [MeasureSpace E] (V : E → ℝ) : Measure E :=
  posteriorDensityMeasure (normalizedPosteriorPotential V)

theorem posteriorNormalizer_pos {d : ℕ}
    (V : EuclideanSpace ℝ (Fin (d+1)) → ℝ)
    (hi : Integrable (fun x => Real.exp (-V x))) : 0<posteriorNormalizer V :=
  integral_exp_pos hi

theorem exp_neg_normalizedPosteriorPotential {E : Type*} [MeasureSpace E]
    (V : E → ℝ) (hZ : 0<posteriorNormalizer V) (x : E) :
    Real.exp (-normalizedPosteriorPotential V x)=Real.exp (-V x)/posteriorNormalizer V := by
  rw [normalizedPosteriorPotential,neg_add,Real.exp_add,
    show Real.exp (-Real.log (posteriorNormalizer V)) = (posteriorNormalizer V)⁻¹ by
      rw [Real.exp_neg,Real.exp_log hZ],div_eq_mul_inv]

theorem normalizedPosteriorMeasure_probability {d : ℕ}
    (V : EuclideanSpace ℝ (Fin (d+1)) → ℝ)
    (hi : Integrable (fun x => Real.exp (-V x))) :
    IsProbabilityMeasure (normalizedPosteriorMeasure V) := by
  have hp := posteriorNormalizer_pos V hi
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

theorem hessianOperator_normalizedPosteriorPotential {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasureSpace E]
    (V : E → ℝ) : hessianOperator (normalizedPosteriorPotential V)=hessianOperator V := by
  have hd : fderiv ℝ (normalizedPosteriorPotential V)=fderiv ℝ V := by
    funext x
    exact fderiv_add_const _
  funext x
  unfold hessianOperator
  rw [hd]

theorem normalized_posterior_brascamp_lieb {d : ℕ}
    (V f : EuclideanSpace ℝ (Fin (d+1)) → ℝ)
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
    normalizedPosteriorMeasure_probability V hi
  have hhc (x z : EuclideanSpace ℝ (Fin (d+1))) :
      directionalHessian (normalizedPosteriorPotential V) x z=directionalHessian V x z := by
    unfold directionalHessian
    have hd : fderiv ℝ (normalizedPosteriorPotential V)=fderiv ℝ V := by
      funext x
      exact fderiv_add_const _
    rw [hd]
  change variance f (posteriorDensityMeasure (normalizedPosteriorPotential V)) ≤ _
  have hh := posterior_brascamp_lieb_canonical (normalizedPosteriorPotential V) f
    (hV.add contDiff_const) hf r A₁ A₂ B₀ B₁ B₂ Kf
    hr hA₁ hA₂ hB₀ hB₁ hB₂ hKf
    (fun x z => by rw [hhc]; exact hcoercive x z) hfb
    (by rw [hessianOperator_normalizedPosteriorPotential]; exact ha₁)
    (by rw [hessianOperator_normalizedPosteriorPotential]; exact ha₂) hb₀ hb₁ hb₂
  simpa only [hessianOperator_normalizedPosteriorPotential,normalizedPosteriorMeasure] using hh

end QuantitativeFollowup

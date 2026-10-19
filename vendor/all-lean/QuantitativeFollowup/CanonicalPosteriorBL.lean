module
public import QuantitativeFollowup.PosteriorOperatorBL
public import Mathlib.Analysis.Calculus.Gradient.Basic

@[expose] public section

/-! The Hessian and inverse in the posterior variance bound are now
literal constructions from the potential, rather than separate supplied
operator or inverse fields. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup

def hessianOperator {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (V : E → ℝ) (x : E) : E →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (fderiv ℝ (fderiv ℝ V) x)

theorem inner_hessianOperator {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (V : E → ℝ) (x z w : E) :
    inner ℝ (hessianOperator V x z) w=fderiv ℝ (fderiv ℝ V) x z w := by
  exact InnerProductSpace.toDual_symm_apply (x := w)
    (y := fderiv ℝ (fderiv ℝ V) x z)

theorem contDiff_hessianOperator {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (V : E → ℝ)
    (hV : ContDiff ℝ 4 V) : ContDiff ℝ 2 (hessianOperator V) := by
  have h₁ : ContDiff ℝ 3 (fderiv ℝ V) := hV.fderiv_right (by norm_num)
  have h₂ : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ V)) := h₁.fderiv_right (by norm_num)
  exact (contDiff_const (c :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap)).clm_comp h₂

theorem contDiff_gradient_two {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ)
    (hf : ContDiff ℝ 3 f) : ContDiff ℝ 2 (gradient f) := by
  have hd : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp hd

theorem posterior_brascamp_lieb_canonical {d : ℕ}
    (V f : EuclideanSpace ℝ (Fin (d+1)) → ℝ)
    [IsProbabilityMeasure (posteriorDensityMeasure V)]
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
    variance f (posteriorDensityMeasure V) ≤
      ∫ x, inner ℝ (gradient f x) ((Ring.inverse (hessianOperator V x))
        (gradient f x)) ∂posteriorDensityMeasure V := by
  apply posterior_brascamp_lieb_operator V f (hessianOperator V) (gradient f)
    (hV.of_le (by norm_num)) (hf.of_le (by norm_num))
    (contDiff_hessianOperator V hV) (contDiff_gradient_two f hf)
    (fun x z w => (inner_hessianOperator V x z w).symm)
    (fun x z => (inner_gradient_left (f := f) (x := x) (y := z)).symm)
    r A₁ A₂ B₀ B₁ B₂ Kf hr hA₁ hA₂ hB₀ hB₁ hB₂ hKf
    (fun x z => by
      rw [real_inner_comm (hessianOperator V x z) z,inner_hessianOperator]
      exact hcoercive x z)
    hfb ha₁ ha₂ hb₀ hb₁ hb₂

end QuantitativeFollowup

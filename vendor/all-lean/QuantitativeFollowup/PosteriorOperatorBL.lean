module
public import QuantitativeFollowup.EuclideanPosteriorBrascampLieb
public import QuantitativeFollowup.InnerFamilyBounds
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section

/-! Actual posterior Brascamp--Lieb with a constructed inverse. Its
inputs are bounds on the actual Hessian and gradient and their first two
derivatives. Inverse-energy smoothness and bounds are consequences. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup

theorem directionalHessian_eq_inner_gradient_derivative {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (b : E → E) (hf : ContDiff ℝ 2 f) (hb : ContDiff ℝ 2 b)
    (hgrad : ∀ x z, fderiv ℝ f x z=inner ℝ (b x) z) (x z : E) :
    directionalHessian f x z=inner ℝ (fderiv ℝ b x z) z := by
  have hp := (hasDerivAt_vector_on_affine_line b hb x z 0).inner ℝ (hasDerivAt_const 0 z)
  have heq : (fun s : ℝ => inner ℝ (b (x+s • z)) z)=
      (fun s => fderiv ℝ f (x+s • z) z) := by
    funext s
    exact (hgrad _ z).symm
  rw [heq] at hp
  have hh := hp.unique (hasDerivAt_directional_on_affine_line f hf x z 0)
  simpa only [zero_smul,add_zero,inner_zero_right,zero_add] using hh.symm

theorem posterior_brascamp_lieb_operator {d : ℕ}
    (V f : EuclideanSpace ℝ (Fin (d+1)) → ℝ)
    (A : EuclideanSpace ℝ (Fin (d+1)) →
      EuclideanSpace ℝ (Fin (d+1)) →L[ℝ] EuclideanSpace ℝ (Fin (d+1)))
    (b : EuclideanSpace ℝ (Fin (d+1)) → EuclideanSpace ℝ (Fin (d+1)))
    [IsProbabilityMeasure (posteriorDensityMeasure V)]
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hA : ContDiff ℝ 2 A) (hb : ContDiff ℝ 2 b)
    (hhessian : ∀ x z w, fderiv ℝ (fderiv ℝ V) x z w=inner ℝ (A x z) w)
    (hgrad : ∀ x z, fderiv ℝ f x z=inner ℝ (b x) z)
    (r A₁ A₂ B₀ B₁ B₂ Kf : ℝ)
    (hr : 0<r) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hKf : 0 ≤ Kf)
    (hcoercive : ∀ x z, r*‖z‖^2 ≤ inner ℝ z (A x z))
    (hfb : ∀ x, |f x| ≤ Kf)
    (ha₁ : ∀ x z, ‖fderiv ℝ A x z‖ ≤ A₁*‖z‖)
    (ha₂ : ∀ x z, ‖fderiv ℝ (fderiv ℝ A) x z z‖ ≤ A₂*‖z‖^2)
    (hb₀ : ∀ x, ‖b x‖ ≤ B₀)
    (hb₁ : ∀ x z, ‖fderiv ℝ b x z‖ ≤ B₁*‖z‖)
    (hb₂ : ∀ x z, ‖fderiv ℝ (fderiv ℝ b) x z z‖ ≤ B₂*‖z‖^2) :
    variance f (posteriorDensityMeasure V) ≤
      ∫ x, inner ℝ (b x) ((Ring.inverse (A x)) (b x)) ∂posteriorDensityMeasure V := by
  let v := inverseFamily A b
  let L := r⁻¹
  let V₀ := L*B₀
  let V₁ := L*(B₁+A₁*L*B₀)
  let V₂ := L*(B₂+A₂*L*B₀+2*A₁*L*(B₁+A₁*L*B₀))
  have hL : 0 ≤ L := inv_nonneg.mpr hr.le
  have hunit (x : EuclideanSpace ℝ (Fin (d+1))) : IsUnit (A x) :=
    isUnit_of_coercive (A x) r hr (hcoercive x)
  have hI (x : EuclideanSpace ℝ (Fin (d+1))) : ‖Ring.inverse (A x)‖ ≤ L :=
    norm_ringInverse_le_of_coercive (A x) r hr (hcoercive x)
  have hv : ContDiff ℝ 2 v := contDiff_inverseFamily A b hA hb hunit
  have hv₀ (x : EuclideanSpace ℝ (Fin (d+1))) : ‖v x‖ ≤ V₀ :=
    inverseFamily_norm_le A b L B₀ hL hI hb₀ x
  have hv₁ (x z : EuclideanSpace ℝ (Fin (d+1))) : ‖fderiv ℝ v x z‖ ≤ V₁*‖z‖ :=
    inverseFamily_directional_norm_le A b hA hb hunit L A₁ B₀ B₁
      hL hA₁ hB₀ hB₁ hI hb₀ ha₁ hb₁ x z
  have hv₂ (x z : EuclideanSpace ℝ (Fin (d+1))) :
      ‖fderiv ℝ (fderiv ℝ v) x z z‖ ≤ V₂*‖z‖^2 :=
    inverseFamily_second_directional_norm_le A b hA hb hunit L A₁ A₂ B₀ B₁ B₂
      hL hA₁ hA₂ hB₀ hB₁ hB₂ hI hb₀ ha₁ ha₂ hb₁ hb₂ x z
  have hV₀ : 0 ≤ V₀ := by positivity
  have hV₁ : 0 ≤ V₁ := by positivity
  have hV₂ : 0 ≤ V₂ := by positivity
  have henergy : inverseHessianEnergy f v=(fun x => inner ℝ (b x) (v x)) := by
    funext x
    exact hgrad x (v x)
  obtain ⟨he₀,he₁,he₂⟩ := innerFamily_bounds b v hb hv B₀ B₁ B₂ V₀ V₁ V₂
    hB₀ hB₁ hB₂ hV₀ hV₁ hV₂ hb₀ hv₀ hb₁ hv₁ hb₂ hv₂
  have hF (x z : EuclideanSpace ℝ (Fin (d+1))) :
      |directionalHessian f x z| ≤ B₁*‖z‖^2 := by
    rw [directionalHessian_eq_inner_gradient_derivative f b hf hb hgrad]
    calc
      _ ≤ ‖fderiv ℝ b x z‖*‖z‖ := abs_real_inner_le_norm _ _
      _ ≤ (B₁*‖z‖)*‖z‖ := mul_le_mul_of_nonneg_right (hb₁ x z) (norm_nonneg _)
      _ = B₁*‖z‖^2 := by ring
  have hsolve (x z : EuclideanSpace ℝ (Fin (d+1))) :
      fderiv ℝ (fderiv ℝ V) x (v x) z=fderiv ℝ f x z := by
    rw [hhessian,inverseFamily_equation A b hunit,hgrad]
  have hco (x z : EuclideanSpace ℝ (Fin (d+1))) :
      r*‖z‖^2 ≤ directionalHessian V x z := by
    rw [directionalHessian,hhessian,real_inner_comm z (A x z)]
    exact hcoercive x z
  have hsym (x z w : EuclideanSpace ℝ (Fin (d+1))) :
      fderiv ℝ (fderiv ℝ V) x z w=fderiv ℝ (fderiv ℝ V) x w z :=
    (hV.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq z w
  have hh := posterior_brascamp_lieb_euclidean V f v hV hf
    (by rw [henergy]; exact hb.inner ℝ hv) r V₀ Kf (B₀*V₀)
    B₁ (B₀*V₁+B₁*V₀) (B₀*V₂+2*B₁*V₁+B₂*V₀)
    hr hV₀ hKf (by positivity) hB₁ (by positivity) (by positivity)
    hco hsym hsolve hv₀ hfb
    (by rw [henergy]; exact he₀) hF
    (by rw [henergy]; exact he₁) (by rw [henergy]; exact he₂)
  simpa only [henergy,v,inverseFamily] using hh

end QuantitativeFollowup

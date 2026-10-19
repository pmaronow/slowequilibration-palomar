module
public import QuantitativeFollowup.CanonicalPosteriorBL
public import Mathlib.Analysis.Normed.Operator.NormedSpace

@[expose] public section

/-! Exact norm conversion from actual multilinear derivatives to the
canonical Hessian/gradient hypotheses in the Brascamp--Lieb theorem. -/
noncomputable section
namespace QuantitativeFollowup
set_option maxSynthPendingDepth 128
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

private def dualInverseIsometry : StrongDual ℝ E →ₗᵢ[ℝ] E where
  toFun := (InnerProductSpace.toDual ℝ E).symm
  map_add' := map_add _
  map_smul' c z := by simp
  norm_map' := (InnerProductSpace.toDual ℝ E).symm.norm_map

theorem norm_iteratedFDeriv_gradient (f : E→ℝ) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (gradient f) x‖ = ‖iteratedFDeriv ℝ (j+1) f x‖ := by
  have he : gradient f = (InnerProductSpace.toDual ℝ E).symm ∘ fderiv ℝ f := by
    funext y
    rfl
  rw [he]
  rw [(InnerProductSpace.toDual ℝ E).symm.norm_iteratedFDeriv_comp_left, norm_iteratedFDeriv_fderiv]

theorem norm_iteratedFDeriv_hessianOperator (V : E→ℝ) (hV : ContDiff ℝ 4 V)
    (j : ℕ) (hj : j ≤ 2) (x : E) :
    ‖iteratedFDeriv ℝ j (hessianOperator V) x‖ = ‖iteratedFDeriv ℝ (j+2) V x‖ := by
  have h₁ : ContDiff ℝ 3 (fderiv ℝ V) := hV.fderiv_right (by norm_num)
  have h₂ : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ V)) := h₁.fderiv_right (by norm_num)
  let L := dualInverseIsometry (E := E)
  let P : (E →L[ℝ] StrongDual ℝ E) →ₗᵢ[ℝ] (E →L[ℝ] E) := L.postcomp
  have hh := P.norm_iteratedFDeriv_comp_left (x := x) h₂.contDiffAt
    (show (j : WithTop ℕ∞) ≤ 2 by exact_mod_cast hj)
  have he : hessianOperator V = P ∘ fderiv ℝ (fderiv ℝ V) := by
    funext y
    apply ContinuousLinearMap.ext
    intro z
    rfl
  rw [he,hh,norm_iteratedFDeriv_fderiv,norm_iteratedFDeriv_fderiv]

omit [CompleteSpace E] in
private theorem norm_fderiv_fderiv_eq_iterated {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : E→F) (x : E) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
  rw [←norm_iteratedFDeriv_one (fderiv ℝ f),norm_iteratedFDeriv_fderiv]

theorem hessian_first_directional_bound (V : E→ℝ) (hV : ContDiff ℝ 4 V)
    (A : ℝ) (hA : ∀x,‖iteratedFDeriv ℝ 3 V x‖ ≤ A) (x z : E) :
    ‖fderiv ℝ (hessianOperator V) x z‖ ≤ A*‖z‖ := by
  calc
    _ ≤ ‖fderiv ℝ (hessianOperator V) x‖*‖z‖ := (fderiv ℝ (hessianOperator V) x).le_opNorm z
    _ = ‖iteratedFDeriv ℝ 3 V x‖*‖z‖ := by rw [←norm_iteratedFDeriv_one,norm_iteratedFDeriv_hessianOperator V hV 1 (by norm_num)]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hA x) (norm_nonneg _)

theorem hessian_second_directional_bound (V : E→ℝ) (hV : ContDiff ℝ 4 V)
    (A : ℝ) (hA : ∀x,‖iteratedFDeriv ℝ 4 V x‖ ≤ A) (x z : E) :
    ‖fderiv ℝ (fderiv ℝ (hessianOperator V)) x z z‖ ≤ A*‖z‖^2 := by
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ (hessianOperator V)) x z‖*‖z‖ := (fderiv ℝ (fderiv ℝ (hessianOperator V)) x z).le_opNorm z
    _ ≤ (‖fderiv ℝ (fderiv ℝ (hessianOperator V)) x‖*‖z‖)*‖z‖ :=
      mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ (hessianOperator V)) x).le_opNorm z) (norm_nonneg _)
    _ = (‖iteratedFDeriv ℝ 4 V x‖*‖z‖)*‖z‖ := by rw [norm_fderiv_fderiv_eq_iterated,norm_iteratedFDeriv_hessianOperator V hV 2 (by norm_num)]
    _ ≤ (A*‖z‖)*‖z‖ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hA x) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

theorem gradient_norm_bound (f : E→ℝ) (B : ℝ) (hB : ∀x,‖iteratedFDeriv ℝ 1 f x‖ ≤ B) (x : E) :
    ‖gradient f x‖ ≤ B := by
  simpa only [←norm_iteratedFDeriv_gradient f 0 x,norm_iteratedFDeriv_zero] using hB x

theorem gradient_first_directional_bound (f : E→ℝ)
    (B : ℝ) (hB : ∀x,‖iteratedFDeriv ℝ 2 f x‖ ≤ B) (x z : E) :
    ‖fderiv ℝ (gradient f) x z‖ ≤ B*‖z‖ := by
  calc
    _ ≤ ‖fderiv ℝ (gradient f) x‖*‖z‖ := (fderiv ℝ (gradient f) x).le_opNorm z
    _ = ‖iteratedFDeriv ℝ 2 f x‖*‖z‖ := by rw [←norm_iteratedFDeriv_one,norm_iteratedFDeriv_gradient f 1 x]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)

theorem gradient_second_directional_bound (f : E→ℝ)
    (B : ℝ) (hB : ∀x,‖iteratedFDeriv ℝ 3 f x‖ ≤ B) (x z : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient f)) x z z‖ ≤ B*‖z‖^2 := by
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ (gradient f)) x z‖*‖z‖ := (fderiv ℝ (fderiv ℝ (gradient f)) x z).le_opNorm z
    _ ≤ (‖fderiv ℝ (fderiv ℝ (gradient f)) x‖*‖z‖)*‖z‖ :=
      mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ (gradient f)) x).le_opNorm z) (norm_nonneg _)
    _ = (‖iteratedFDeriv ℝ 3 f x‖*‖z‖)*‖z‖ := by rw [norm_fderiv_fderiv_eq_iterated,norm_iteratedFDeriv_gradient f 2 x]
    _ ≤ (B*‖z‖)*‖z‖ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

/-- Apply the canonical posterior theorem directly from actual jet-norm bounds. -/
theorem posterior_brascamp_lieb_canonical_of_jet_bounds {d : ℕ}
    (V f : EuclideanSpace ℝ (Fin (d+1)) → ℝ)
    [MeasureTheory.IsProbabilityMeasure (posteriorDensityMeasure V)]
    (hV : ContDiff ℝ 4 V) (hf : ContDiff ℝ 3 f)
    (r A₁ A₂ B₀ B₁ B₂ Kf : ℝ) (hr : 0 < r)
    (hcoercive : ∀x z,r*‖z‖^2 ≤ directionalHessian V x z)
    (hfb : ∀x,|f x| ≤ Kf)
    (ha₁ : ∀x,‖iteratedFDeriv ℝ 3 V x‖ ≤ A₁)
    (ha₂ : ∀x,‖iteratedFDeriv ℝ 4 V x‖ ≤ A₂)
    (hb₀ : ∀x,‖iteratedFDeriv ℝ 1 f x‖ ≤ B₀)
    (hb₁ : ∀x,‖iteratedFDeriv ℝ 2 f x‖ ≤ B₁)
    (hb₂ : ∀x,‖iteratedFDeriv ℝ 3 f x‖ ≤ B₂) :
    ProbabilityTheory.variance f (posteriorDensityMeasure V) ≤
      ∫x,inner ℝ (gradient f x) ((Ring.inverse (hessianOperator V x)) (gradient f x))
        ∂posteriorDensityMeasure V := by
  apply posterior_brascamp_lieb_canonical V f hV hf r A₁ A₂ B₀ B₁ B₂ Kf hr
    ((norm_nonneg _).trans (ha₁ 0)) ((norm_nonneg _).trans (ha₂ 0))
    ((norm_nonneg _).trans (hb₀ 0)) ((norm_nonneg _).trans (hb₁ 0))
    ((norm_nonneg _).trans (hb₂ 0)) ((abs_nonneg _).trans (hfb 0)) hcoercive hfb
  · exact hessian_first_directional_bound V hV A₁ ha₁
  · exact hessian_second_directional_bound V hV A₂ ha₂
  · exact gradient_norm_bound f B₀ hb₀
  · exact gradient_first_directional_bound f B₁ hb₁
  · exact gradient_second_directional_bound f B₂ hb₂

end QuantitativeFollowup

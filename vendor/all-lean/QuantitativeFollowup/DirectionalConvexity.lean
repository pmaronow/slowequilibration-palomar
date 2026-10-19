module
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic

@[expose] public section

/-! Convexity from genuine derivatives on affine lines. This supplies the
multivariate calculus step in the posterior argument without assuming a
variance or an integration-by-parts identity. -/
noncomputable section
open Set
namespace QuantitativeFollowup

theorem convexOn_of_line_second_derivatives {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (hS : Convex ℝ S) (F : E → ℝ) (hF : ContinuousOn F S)
    (hline : ∀ x ∈ S, ∀ y ∈ S, ∃ F₁ F₂ : ℝ → ℝ,
      (∀ r ∈ Ioo (0:ℝ) 1, HasDerivAt (fun s => F (x+s • (y-x))) (F₁ r) r) ∧
      (∀ r ∈ Ioo (0:ℝ) 1, HasDerivAt F₁ (F₂ r) r) ∧
      (∀ r ∈ Ioo (0:ℝ) 1, 0 ≤ F₂ r)) : ConvexOn ℝ S F := by
  refine ⟨hS, ?_⟩
  intro x hx y hy a b ha hb hab
  obtain ⟨F₁,F₂,h₁,h₂,hpos⟩ := hline x hx y hy
  have hmem (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) : x+r • (y-x) ∈ S := by
    have heq : x+r • (y-x) = (1-r) • x+r • y := by module
    rw [heq]
    exact hS hx hy (sub_nonneg.mpr hr.2) hr.1 (by ring)
  have hc : ContinuousOn (fun r : ℝ => F (x+r • (y-x))) (Icc 0 1) :=
    hF.comp (by fun_prop) hmem
  have hcv : ConvexOn ℝ (Icc (0:ℝ) 1) (fun r => F (x+r • (y-x))) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _) hc
      (f' := F₁) (f'' := F₂)
    · intro r hr
      exact (h₁ r (by simpa only [interior_Icc] using hr)).hasDerivWithinAt
    · intro r hr
      exact (h₂ r (by simpa only [interior_Icc] using hr)).hasDerivWithinAt
    · intro r hr
      exact hpos r (by simpa only [interior_Icc] using hr)
  have hh := hcv.2 (show (0:ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (show (1:ℝ) ∈ Icc 0 1 by constructor <;> norm_num) ha hb hab
  have heq : x+b • (y-x) = a • x+b • y := by
    have : a=1-b := by linarith
    rw [this]
    module
  simpa only [smul_eq_mul,mul_zero,mul_one,zero_add,zero_smul,add_zero,
    one_smul,add_sub_cancel,heq] using hh

def directionalHessian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (x z : E) : ℝ := fderiv ℝ (fderiv ℝ F) x z z

theorem hasDerivAt_on_affine_line {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (hF : ContDiff ℝ 2 F) (x z : E) (r : ℝ) :
    HasDerivAt (fun s => F (x+s • z)) (fderiv ℝ F (x+r • z) z) r := by
  apply (hF.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt r
  simpa only [id_eq,one_smul] using
    ((hasDerivAt_id r).smul_const z |>.const_add x)

theorem hasDerivAt_directional_on_affine_line {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (hF : ContDiff ℝ 2 F) (x z : E) (r : ℝ) :
    HasDerivAt (fun s => fderiv ℝ F (x+s • z) z)
      (directionalHessian F (x+r • z) z) r := by
  have hd : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hh := (hd.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_id r).smul_const z |>.const_add x)
  simpa only [Function.comp_apply,directionalHessian,map_zero,
    add_zero,id_eq,one_smul] using hh.clm_apply (hasDerivAt_const r z)

end QuantitativeFollowup

module
public import QuantitativeFollowup.DirectionalConvexity
public import QuantitativePaper.VectorPosterior
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

/-! Genuine directional Hessian calculus and coercivity of a Gaussian quadratic
plus a smooth convex correction. -/
noncomputable section
open Set
open scoped ContDiff
namespace QuantitativePaper
set_option backward.isDefEq.respectTransparency false
open QuantitativeFollowup FourPapersCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem directionalHessian_add (f g : E → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x z : E) : directionalHessian (fun y => f y+g y) x z=
      directionalHessian f x z+directionalHessian g x z := by
  have he : fderiv ℝ (fun y => f y+g y) = fun y => fderiv ℝ f y+fderiv ℝ g y := by
    funext y
    exact fderiv_add (hf.differentiable (by norm_num) y) (hg.differentiable (by norm_num) y)
  unfold directionalHessian
  rw [he]
  have hf' : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2)).differentiable (by norm_num)
  have hg' : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2)).differentiable (by norm_num)
  change fderiv ℝ (fderiv ℝ f+fderiv ℝ g) x z z=_
  rw [fderiv_add (hf' x) (hg' x)]
  rfl

theorem directionalHessian_nonneg_of_convex (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hc : ConvexOn ℝ univ f) (x z : E) : 0 ≤ directionalHessian f x z := by
  let l := fun r : ℝ => f (x+r • z)
  have hl : ConvexOn ℝ univ l := by
    refine ⟨convex_univ,?_⟩
    intro u hu v hv a b ha hb hab
    have he : x+(a*u+b*v) • z = a • (x+u • z)+b • (x+v • z) := by
      have ha' : a=1-b := by linarith
      rw [ha']
      module
    have hh := hc.2 (mem_univ (x+u • z)) (mem_univ (x+v • z)) ha hb hab
    simpa only [l,smul_eq_mul,he] using hh
  have hd (r : ℝ) := hasDerivAt_on_affine_line f hf x z r
  have hm : Monotone (fun r : ℝ => fderiv ℝ f (x+r • z) z) := by
    intro r u hru
    have hh := hl.monotoneOn_deriv (fun r _ => (hd r).differentiableAt)
      (mem_univ r) (mem_univ u) hru
    change deriv l r ≤ deriv l u at hh
    rw [(hd r).deriv,(hd u).deriv] at hh
    exact hh
  have hh := hm.deriv_nonneg (x := 0)
  rw [(hasDerivAt_directional_on_affine_line f hf x z 0).deriv] at hh
  simpa using hh

theorem directionalHessian_standardGaussianPotential {ι : Type*} [Fintype ι]
    (x z : EuclideanSpace ℝ ι) : directionalHessian standardGaussianPotential x z=‖z‖^2 := by
  have hs : ContDiff ℝ 2 (standardGaussianPotential (ι := ι)) :=
    contDiff_standardGaussianPotential.of_le (by simp)
  have he : (fun r : ℝ => standardGaussianPotential (x+r • z)) =
      fun r => standardGaussianPotential x+r*inner ℝ x z+r^2/2*‖z‖^2 := by
    funext r
    unfold standardGaussianPotential
    simp only [←real_inner_self_eq_norm_sq,inner_add_left,inner_add_right,
      real_inner_smul_left,real_inner_smul_right,real_inner_comm z x]
    ring
  have hd (r : ℝ) : HasDerivAt (fun s : ℝ => standardGaussianPotential (x+s • z))
      (inner ℝ x z+r*‖z‖^2) r := by
    rw [he]
    have hh := (((hasDerivAt_id r).mul_const (inner ℝ x z)).const_add
      (standardGaussianPotential x)).add (((hasDerivAt_id r).pow 2 |>.div_const 2).mul_const (‖z‖^2))
    convert! hh using 1 <;> simp [Pi.add_apply]
  have hf : (fun r : ℝ => fderiv ℝ standardGaussianPotential (x+r • z) z)=
      fun r => inner ℝ x z+r*‖z‖^2 := by
    funext r
    exact (hasDerivAt_on_affine_line _ hs x z r).unique (hd r)
  have hh := hasDerivAt_directional_on_affine_line _ hs x z 0
  rw [hf] at hh
  have hd2 := ((hasDerivAt_id (0 : ℝ)).mul_const (‖z‖^2)).const_add (inner ℝ x z)
  simpa using hh.unique hd2

end QuantitativePaper

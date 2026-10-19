module
public import QuantitativePaper.VectorPosteriorJets
public import QuantitativeFollowup.PosteriorFiniteFeature
public import QuantitativeFollowup.CanonicalPosteriorBL

@[expose] public section

/-! Literal Hessian-operator calculus used for the posterior metric. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace QuantitativePaper
open QuantitativeFollowup FourPapersCommon
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem hessianOperator_add (f g : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (x : E) :
    hessianOperator (fun y => f y+g y) x=hessianOperator f x+hessianOperator g x := by
  have he : fderiv ℝ (fun y => f y+g y)=fderiv ℝ f+fderiv ℝ g :=
    funext fun y => fderiv_fun_add (hf.differentiable (by norm_num) y)
      (hg.differentiable (by norm_num) y)
  have hdf₁ : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hdg₁ : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hdf : Differentiable ℝ (fderiv ℝ f) := hdf₁.differentiable (by norm_num)
  have hdg : Differentiable ℝ (fderiv ℝ g) := hdg₁.differentiable (by norm_num)
  apply ContinuousLinearMap.ext
  intro z
  apply ext_inner_right ℝ
  intro w
  rw [ContinuousLinearMap.add_apply,inner_add_left,inner_hessianOperator,
    inner_hessianOperator,inner_hessianOperator,he,fderiv_add (hdf x) (hdg x)]
  rfl

theorem hessianOperator_const_mul (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (c : ℝ) (x : E) :
    hessianOperator (fun y => c*f y) x=c • hessianOperator f x := by
  have he : fderiv ℝ (fun y => c*f y)=c • fderiv ℝ f :=
    funext fun y => fderiv_fun_const_smul (hf.differentiable (by norm_num) y) c
  have hdf₁ : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hdf : Differentiable ℝ (fderiv ℝ f) := hdf₁.differentiable (by norm_num)
  apply ContinuousLinearMap.ext
  intro z
  apply ext_inner_right ℝ
  intro w
  rw [ContinuousLinearMap.smul_apply,real_inner_smul_left,inner_hessianOperator,
    inner_hessianOperator,he,fderiv_const_smul (hdf x) c]
  rfl

theorem hessianOperator_add_const (f : E → ℝ) (c : ℝ) :
    hessianOperator (fun x => f x+c)=hessianOperator f := by
  have he : fderiv ℝ (fun x => f x+c)=fderiv ℝ f := funext fun _ => fderiv_add_const _
  funext x
  unfold hessianOperator
  rw [he]

theorem hessianOperator_linear (L : E →L[ℝ] ℝ) (x : E) : hessianOperator L x=0 := by
  have he : fderiv ℝ L=fun _ => L := funext fun _ => L.fderiv
  unfold hessianOperator
  rw [he]
  have hd : fderiv ℝ (fun _ : E => L) x=0 := fderiv_const_apply L
  rw [hd]
  simp

theorem hessianOperator_finite_sum {ι : Type*} (S : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ S,ContDiff ℝ 2 (f i)) (x : E) :
    hessianOperator (fun y => ∑ i ∈ S,f i y) x=∑ i ∈ S,hessianOperator (f i) x := by
  classical
  induction S using Finset.induction with
  | empty => simp [hessianOperator,fderiv_const]
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    rw [hessianOperator_add _ _ (hf i (Finset.mem_insert_self _ _))
      (ContDiff.sum (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

theorem hessianOperator_standardGaussianPotential {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℝ ι) : hessianOperator standardGaussianPotential x=1 := by
  apply ContinuousLinearMap.ext
  intro z
  apply ext_inner_right ℝ
  intro w
  rw [inner_hessianOperator,fderiv_standardGaussianPotential,(innerSL ℝ).fderiv]
  rfl

theorem gradient_const_mul (f : E → ℝ) (hf : Differentiable ℝ f) (c : ℝ) (x : E) :
    gradient (fun y => c*f y) x=c • gradient f x := by
  apply ext_inner_right ℝ
  intro w
  rw [real_inner_smul_left,inner_gradient_left,inner_gradient_left]
  convert! congrArg (fun A : E →L[ℝ] ℝ => A w) (fderiv_fun_const_smul (hf x) c) using 1

theorem gradient_finite_sum {ι : Type*} (S : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ S,Differentiable ℝ (f i)) (x : E) :
    gradient (fun y => ∑ i ∈ S,f i y) x=∑ i ∈ S,gradient (f i) x := by
  apply ext_inner_right ℝ
  intro w
  rw [sum_inner,inner_gradient_left,fderiv_fun_sum (fun i hi => hf i hi x),sum_apply]
  simp_rw [inner_gradient_left]

theorem directionalHessian_eq_secondDeriv_line {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (f : A → ℝ) (hf : ContDiff ℝ 2 f)
    (x z : A) : directionalHessian f x z=deriv (deriv (fun r : ℝ => f (x+r • z))) 0 := by
  have he : deriv (fun r : ℝ => f (x+r • z))=fun r => fderiv ℝ f (x+r • z) z :=
    funext fun r => (hasDerivAt_on_affine_line f hf x z r).deriv
  rw [he,(hasDerivAt_directional_on_affine_line f hf x z 0).deriv]
  simp

end QuantitativePaper

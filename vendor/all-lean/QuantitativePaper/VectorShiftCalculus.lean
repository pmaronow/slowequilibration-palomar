module
public import QuantitativePaper.PosteriorMetricCalculus

@[expose] public section

/-! Genuine differential algebra for the normalized spin/mean score and
its Hessian shift representation. All derivative premises in this general
lemma are explicit; the concrete vector model instantiates them separately. -/
noncomputable section
open Set
namespace QuantitativePaper
open QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def normalizedMeanScore (m : E → F) (σ : F) (N : ℝ) (x : E) : ℝ :=
  (inner ℝ (m x) σ-‖m x‖^2/2)/N

theorem fderiv_normalizedMeanScore (m : E → F) (σ : F) (N : ℝ)
    (hm : Differentiable ℝ m) (x z : E) :
    fderiv ℝ (normalizedMeanScore m σ N) x z=
      inner ℝ (fderiv ℝ m x z) (σ-m x)/N := by
  have hd := (((hm x).hasFDerivAt.inner ℝ (hasFDerivAt_const σ x)).sub
    ((hm x).hasFDerivAt.norm_sq.const_smul (1/2 : ℝ))).const_smul N⁻¹
  have hd' : HasFDerivAt (normalizedMeanScore m σ N)
      (N⁻¹ • ((fderivInnerCLM ℝ (m x,σ)).comp ((fderiv ℝ m x).prod 0)-
        (1/2 : ℝ) • (2 : ℕ) • (innerSL ℝ (m x)).comp (fderiv ℝ m x))) x := by
    convert! hd using 1
    · funext y
      simp only [normalizedMeanScore,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
      ring
  rw [hd'.fderiv]
  simp only [sub_apply,ContinuousLinearMap.comp_apply,
    fderivInnerCLM_apply,ContinuousLinearMap.prod_apply,ContinuousLinearMap.zero_apply,
    inner_zero_right,zero_add,smul_apply,smul_eq_mul,innerSL_apply_apply,inner_sub_right,
    two_nsmul,add_apply]
  rw [real_inner_comm (m x) (fderiv ℝ m x z)]
  ring

theorem normalizedMeanScore_hessian_shift (U : E → ℝ) (m : E → F) (L : F →L[ℝ] E)
    (hU : ContDiff ℝ 2 U) (hm : ContDiff ℝ 1 m)
    (hfield : ∀ x w,fderiv ℝ U x (L w)=inner ℝ (m x) w)
    (σ : F) (N : ℝ) (hN : N≠0) (x : E) :
    hessianOperator U x (L (σ-m x))=N • gradient (normalizedMeanScore m σ N) x := by
  let w := σ-m x
  have hdf : ContDiff ℝ 1 (fderiv ℝ U) := hU.fderiv_right (by norm_num)
  have hc := ((hdf.differentiable (by norm_num) x).hasFDerivAt).clm_apply
    (hasFDerivAt_const (L w) x)
  have hi := (hm.differentiable (by norm_num) x).hasFDerivAt.inner ℝ
    (hasFDerivAt_const w x)
  have he : (fun y => fderiv ℝ U y (L w))=(fun y => inner ℝ (m y) w) :=
    funext fun y => hfield y w
  rw [he] at hc
  have hsecond (z : E) : fderiv ℝ (fderiv ℝ U) x z (L w)=inner ℝ (fderiv ℝ m x z) w := by
    have hh := congrArg (fun A : E →L[ℝ] ℝ => A z) (hc.unique hi)
    simpa only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.zero_apply,
      map_zero,zero_add,ContinuousLinearMap.flip_apply,fderivInnerCLM_apply,
      ContinuousLinearMap.prod_apply,inner_zero_right] using hh
  apply ext_inner_right ℝ
  intro z
  rw [inner_hessianOperator,(hU.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq (L w) z,
    hsecond,real_inner_smul_left,inner_gradient_left]
  rw [fderiv_normalizedMeanScore _ _ _ (hm.differentiable (by norm_num))]
  dsimp [w]
  field_simp

end QuantitativePaper

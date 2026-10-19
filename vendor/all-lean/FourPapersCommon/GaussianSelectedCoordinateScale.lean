module
public import OverlapPaper.CavityGaussianIBP
public import Mathlib.Analysis.SpecialFunctions.Sqrt

public import Mathlib.Probability.Distributions.Gaussian.Fernique

@[expose] public section

/-! Actual selected-coordinate Gaussian scaling and its derivative.
The mask may be empty and the coordinate space may have dimension zero. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def gaussianSelectedScale (p : ι→Bool) (b : ℝ) :
    EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ ι :=
  ∑i,(PiLp.proj 2 (fun _ : ι=>ℝ) i).smulRight
    ((if p i then Real.sqrt b else 1) • EuclideanSpace.basisFun ι ℝ i)

def gaussianSelectedScaleDerivative (p : ι→Bool) (b : ℝ) :
    EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ ι :=
  ∑i,(PiLp.proj 2 (fun _ : ι=>ℝ) i).smulRight
    ((if p i then 1/(2*Real.sqrt b) else 0) • EuclideanSpace.basisFun ι ℝ i)

theorem gaussianSelectedScale_apply (p : ι→Bool) (b : ℝ) (z : EuclideanSpace ℝ ι) :
    gaussianSelectedScale p b z=
      ∑i,((if p i then Real.sqrt b else 1)*z i) • EuclideanSpace.basisFun ι ℝ i := by
  simp only [gaussianSelectedScale,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply,PiLp.proj_apply,smul_smul]
  congr 1
  funext i
  rw [mul_comm]

@[simp] theorem gaussianSelectedScale_basis (p : ι→Bool) (b : ℝ) (i : ι) :
    gaussianSelectedScale p b (EuclideanSpace.basisFun ι ℝ i)=
      (if p i then Real.sqrt b else 1) • EuclideanSpace.basisFun ι ℝ i := by
  rw [gaussianSelectedScale_apply]
  simp only [EuclideanSpace.basisFun_apply,PiLp.single_apply]
  simp

theorem gaussianSelectedScaleDerivative_apply (p : ι→Bool) (b : ℝ) (z : EuclideanSpace ℝ ι) :
    gaussianSelectedScaleDerivative p b z=
      ∑i,((if p i then 1/(2*Real.sqrt b) else 0)*z i) • EuclideanSpace.basisFun ι ℝ i := by
  simp only [gaussianSelectedScaleDerivative,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply,PiLp.proj_apply,smul_smul]
  congr 1
  funext i
  rw [mul_comm]

theorem hasDerivAt_gaussianSelectedScale (p : ι→Bool) (b : ℝ) (hb : 0<b)
    (z : EuclideanSpace ℝ ι) :
    HasDerivAt (fun u=>gaussianSelectedScale p u z)
      (gaussianSelectedScaleDerivative p b z) b := by
  simp_rw [gaussianSelectedScale_apply,gaussianSelectedScaleDerivative_apply]
  apply HasDerivAt.fun_sum
  intro i _
  by_cases hp : p i=true
  · simp only [hp,ite_true]
    exact ((Real.hasDerivAt_sqrt hb.ne').mul_const (z i)).smul_const _
  · have hp0 : p i=false:=Bool.eq_false_iff.mpr hp
    simp only [hp0,Bool.false_eq_true,ite_false,zero_mul,zero_smul,one_mul]
    exact hasDerivAt_const b (z i • EuclideanSpace.basisFun ι ℝ i)

theorem norm_gaussianSelectedScale_le (p : ι→Bool) (b u : ℝ) (hbu : b≤u)
    (z : EuclideanSpace ℝ ι) :
    ‖gaussianSelectedScale p b z‖≤(Fintype.card ι:ℝ)*(1+Real.sqrt u)*‖z‖ := by
  rw [gaussianSelectedScale_apply]
  calc
    _≤∑i,‖((if p i then Real.sqrt b else 1)*z i) • EuclideanSpace.basisFun ι ℝ i‖:=norm_sum_le _ _
    _≤∑_i:ι,(1+Real.sqrt u)*‖z‖:=by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,(EuclideanSpace.basisFun ι ℝ).norm_eq_one,mul_one,Real.norm_eq_abs,abs_mul]
      have hc : |if p i then Real.sqrt b else 1|≤1+Real.sqrt u:=by
        split
        · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
          linarith [Real.sqrt_le_sqrt hbu]
        · simp
      exact mul_le_mul hc (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i)
        (abs_nonneg _) (by positivity)
    _=_:=by simp [mul_assoc]

theorem norm_gaussianSelectedScaleDerivative_le (p : ι→Bool) (b l : ℝ)
    (hl : 0<l) (hlb : l≤b) (z : EuclideanSpace ℝ ι) :
    ‖gaussianSelectedScaleDerivative p b z‖≤
      ((Fintype.card ι:ℝ)/(2*Real.sqrt l))*‖z‖ := by
  rw [gaussianSelectedScaleDerivative_apply]
  calc
    _≤∑i,‖((if p i then 1/(2*Real.sqrt b) else 0)*z i) • EuclideanSpace.basisFun ι ℝ i‖:=norm_sum_le _ _
    _≤∑_i:ι,(1/(2*Real.sqrt l))*‖z‖:=by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,(EuclideanSpace.basisFun ι ℝ).norm_eq_one,mul_one,Real.norm_eq_abs,abs_mul]
      have hc : |if p i then 1/(2*Real.sqrt b) else 0|≤1/(2*Real.sqrt l):=by
        split
        · rw [abs_of_nonneg (by positivity)]
          exact one_div_le_one_div_of_le (by positivity) (by gcongr)
        · simp
      exact mul_le_mul hc (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i)
        (abs_nonneg _) (by positivity)
    _=_:=by simp [div_eq_mul_inv,mul_assoc]

theorem covarianceOperator_stdGaussian_id (z : EuclideanSpace ℝ ι) :
    covarianceOperator (stdGaussian (EuclideanSpace ℝ ι)) z=z := by
  apply ext_inner_right ℝ
  intro y
  rw [covarianceOperator_inner IsGaussian.memLp_two_id]
  have hh:=congrArg (fun B=>B z y) (covarianceBilin_stdGaussian (E:=EuclideanSpace ℝ ι))
  simpa only [covarianceBilin_apply IsGaussian.memLp_two_id,Function.id_def,
    integral_id_stdGaussian,sub_zero,innerSL_apply_apply ℝ] using hh

end FourPapersCommon

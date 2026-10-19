module

public import FourPapersCommon.NativeGaussianPolynomialIBP

@[expose] public section

/-! Exact Gaussian contractions for products of linear projections.
All polynomial integrability and Stein envelopes are constructed from
the projections; no Gaussian moment or Wick identity is supplied. -/
noncomputable section
open MeasureTheory ProbabilityTheory QuantitativePaper OverlapPaper
open scoped BigOperators ContDiff
namespace FourPapersCommon
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
local instance : ContinuousSMul ℝ (EuclideanSpace ℝ ι) := IsBoundedSMul.continuousSMul

def GaussianExponentialC1Envelope (P : EuclideanSpace ℝ ι → ℝ) : Prop :=
  ContDiff ℝ 1 P ∧ ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
    (∀ z, ‖P z‖ ≤ C*Real.exp (A*‖z‖)) ∧
    (∀ z, ‖fderiv ℝ P z‖ ≤ C*Real.exp (A*‖z‖))

theorem gaussianExponentialC1Envelope_one :
    GaussianExponentialC1Envelope (fun _ : EuclideanSpace ℝ ι => (1:ℝ)) := by
  refine ⟨contDiff_const,1,0,by norm_num,le_rfl,?_,?_⟩ <;> intro z <;> simp

theorem gaussianExponentialC1Envelope_linear (L : EuclideanSpace ℝ ι →L[ℝ] ℝ) :
    GaussianExponentialC1Envelope L := by
  refine ⟨L.contDiff,‖L‖,1,norm_nonneg _,by norm_num,?_,?_⟩
  · intro z
    exact (L.le_opNorm z).trans (mul_le_mul_of_nonneg_left
      (by simp only [one_mul];linarith [Real.add_one_le_exp ‖z‖]) (norm_nonneg L))
  · intro z
    rw [L.fderiv]
    simpa using mul_le_mul_of_nonneg_left
      (Real.one_le_exp (norm_nonneg z)) (norm_nonneg L)

theorem GaussianExponentialC1Envelope.mul
    {P Q : EuclideanSpace ℝ ι → ℝ}
    (hP : GaussianExponentialC1Envelope P) (hQ : GaussianExponentialC1Envelope Q) :
    GaussianExponentialC1Envelope (fun z => P z*Q z) := by
  obtain ⟨hPc,C,A,hC,hA,hPv,hPd⟩ := hP
  obtain ⟨hQc,D,B,hD,hB,hQv,hQd⟩ := hQ
  refine ⟨hPc.mul hQc,2*C*D,A+B,by positivity,add_nonneg hA hB,?_,?_⟩
  · intro z
    rw [norm_mul]
    calc
      _ ≤ (C*Real.exp (A*‖z‖))*(D*Real.exp (B*‖z‖)) :=
        mul_le_mul (hPv z) (hQv z) (norm_nonneg _) (by positivity)
      _ = C*D*Real.exp ((A+B)*‖z‖) := by rw [add_mul,Real.exp_add];ring
      _ ≤ 2*C*D*Real.exp ((A+B)*‖z‖) := by
        nlinarith [mul_nonneg (mul_nonneg hC hD) (Real.exp_pos ((A+B)*‖z‖)).le]
  · intro z
    change ‖fderiv ℝ (P*Q) z‖ ≤ _
    rw [fderiv_mul (hPc.differentiable (by simp) z) (hQc.differentiable (by simp) z)]
    apply (norm_add_le _ _).trans
    rw [norm_smul,norm_smul]
    calc
      _ ≤ (C*Real.exp (A*‖z‖))*(D*Real.exp (B*‖z‖))+
          (D*Real.exp (B*‖z‖))*(C*Real.exp (A*‖z‖)) :=
        add_le_add
          (mul_le_mul (hPv z) (hQd z) (norm_nonneg _) (by positivity))
          (mul_le_mul (hQv z) (hPd z) (norm_nonneg _) (by positivity))
      _ = _ := by rw [add_mul,Real.exp_add];ring

theorem gaussianExponentialC1Envelope_linear_product
    (I : Finset κ) (L : κ → EuclideanSpace ℝ ι →L[ℝ] ℝ) :
    GaussianExponentialC1Envelope (fun z => ∏ i ∈ I, L i z) := by
  induction I using Finset.induction_on with
  | empty => simpa using (gaussianExponentialC1Envelope_one (ι:=ι))
  | @insert i I hi ih =>
    simpa only [Finset.prod_insert hi] using (gaussianExponentialC1Envelope_linear (L i)).mul ih

theorem integrable_gaussian_linear_product
    (I : Finset κ) (L : κ → EuclideanSpace ℝ ι →L[ℝ] ℝ) :
    Integrable (fun z => ∏ i ∈ I, L i z) (stdGaussian (EuclideanSpace ℝ ι)) := by
  obtain ⟨hP,C,A,hC,hA,hPv,hPd⟩ := gaussianExponentialC1Envelope_linear_product I L
  exact integrable_gaussian_exponential_bound (stdGaussian (EuclideanSpace ℝ ι)) _
    hP.continuous.measurable C A hC hPv

theorem integral_gaussian_linear_product_stein
    (I : Finset κ) (u : κ → EuclideanSpace ℝ ι) (v : EuclideanSpace ℝ ι) :
    (∫ z, inner ℝ z v*(∏ i ∈ I, inner ℝ (u i) z) ∂stdGaussian (EuclideanSpace ℝ ι)) =
      ∑ i ∈ I, inner ℝ (u i) v*
        ∫ z, (∏ j ∈ I.erase i, inner ℝ (u j) z) ∂stdGaussian (EuclideanSpace ℝ ι) := by
  let L : κ → EuclideanSpace ℝ ι →L[ℝ] ℝ := fun i => innerSL ℝ (u i)
  let P : EuclideanSpace ℝ ι → ℝ := fun z => ∏ i ∈ I, L i z
  obtain ⟨hP,C,A,hC,hA,hPv,hPd⟩ := gaussianExponentialC1Envelope_linear_product I L
  have hs := gaussian_posterior_ibp_of_exponential_bounds (fun _ => (0:ℝ)) P
    (boundedPositiveJets_const 0) hP C C A hC hC hPv hPd v
  have hz (z : EuclideanSpace ℝ ι) : fderiv ℝ (fun _ : EuclideanSpace ℝ ι => (0:ℝ)) z=0 :=
    (hasFDerivAt_const (0:ℝ) z).fderiv
  simp only [neg_zero,Real.exp_zero,one_mul,hz,ContinuousLinearMap.zero_apply,
    mul_zero,sub_zero] at hs
  have hd (z : EuclideanSpace ℝ ι) :
      fderiv ℝ P z v = ∑ i ∈ I, (∏ j ∈ I.erase i, L j z)*inner ℝ (u i) v := by
    dsimp only [P]
    rw [fderiv_finsetProd (fun i _ => (L i).differentiableAt),ContinuousLinearMap.sum_apply]
    simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,ContinuousLinearMap.fderiv,
      L,innerSL_apply_apply]
  simp_rw [hd] at hs
  rw [integral_finsetSum] at hs
  · simpa only [P,L,innerSL_apply_apply,mul_comm,integral_const_mul] using hs
  · intro i hi
    exact (integrable_gaussian_linear_product (I.erase i) L).mul_const _

end FourPapersCommon

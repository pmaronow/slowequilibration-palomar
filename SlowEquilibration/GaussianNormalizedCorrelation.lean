-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianMaximalCorrelation

/-! Dimension-free factorization of actual normalized nonnegative Gaussian
observables from their genuine second moments, including raw determinants. -/
@[expose] public section
namespace SlowEquilibration.GaussianMaximalCorrelation
noncomputable section
open Function MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open scoped ENNReal Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
variable {ι : Type*} [Fintype ι]

theorem normalized_coupled_factorization (ρ s : ℝ) (h : ρ^2+s^2=1) (hρ : |ρ| ≤ 1)
    {F G : (ι → ℝ) → ℝ} (hF : Measurable F) (hG : Measurable G)
    (hF2 : MemLp F 2 (γpi ι)) (hG2 : MemLp G 2 (γpi ι))
    (hFmean : ∫ x,F x ∂γpi ι=1) (hGmean : ∫ x,G x ∂γpi ι=1)
    {C : ℝ} (hC : 0 ≤ C) (hFbound : ∫ x,F x^2 ∂γpi ι ≤ C)
    (hGbound : ∫ x,G x^2 ∂γpi ι ≤ C) :
    Integrable (fun z : (ι → ℝ)×(ι → ℝ) => F z.1*G (ρ • z.1+s • z.2)) ((γpi ι).prod (γpi ι)) ∧
    |(∫ z : (ι → ℝ)×(ι → ℝ),F z.1*G (ρ • z.1+s • z.2) ∂(γpi ι).prod (γpi ι))-1| ≤ C * |ρ| := by
  let G0:=fun x => G x-1
  have hG0m : Measurable G0 := hG.sub measurable_const
  have hG02 : MemLp G0 2 (γpi ι) := hG2.sub (memLp_const (1:ℝ))
  have hG0mean : ∫ x,G0 x ∂γpi ι=0 := by
    rw [integral_sub (hG2.integrable (by norm_num)) (integrable_const _)]
    simp only [hGmean,integral_const,probReal_univ,one_smul,sub_self]
  have hG0bound : ∫ x,G0 x^2 ∂γpi ι ≤ C := by
    have hv:=variance_eq_sub hG2
    rw [variance_eq_integral hG2.aemeasurable,hGmean] at hv
    change (∫ x,G0 x^2 ∂γpi ι)=(∫ x,G x^2 ∂γpi ι)-1^2 at hv
    rw [hv]
    linarith
  have hnF : ‖hF2.toLp F‖ ≤ Real.sqrt C := by
    have hh:=hFbound
    rw [← toLp_norm_sq hF2] at hh
    nlinarith [Real.sq_sqrt hC,norm_nonneg (hF2.toLp F),Real.sqrt_nonneg C]
  have hnG : ‖hG02.toLp G0‖ ≤ Real.sqrt C := by
    have hh:=hG0bound
    rw [← toLp_norm_sq hG02] at hh
    nlinarith [Real.sq_sqrt hC,norm_nonneg (hG02.toLp G0),Real.sqrt_nonneg C]
  have hprod : Integrable (fun z : (ι → ℝ)×(ι → ℝ) => F z.1*G (ρ • z.1+s • z.2))
      ((γpi ι).prod (γpi ι)) := (hF2.comp_fst (γpi ι)).integrable_mul (coupled_memLp ρ s h hG2)
  have hCenterEq : (∫ z : (ι → ℝ)×(ι → ℝ),F z.1*G0 (ρ • z.1+s • z.2) ∂(γpi ι).prod (γpi ι))=
      (∫ z : (ι → ℝ)×(ι → ℝ),F z.1*G (ρ • z.1+s • z.2) ∂(γpi ι).prod (γpi ι))-1 := by
    simp only [G0,mul_sub,mul_one]
    rw [integral_sub hprod ((hF2.integrable (by norm_num)).comp_fst (γpi ι)),
      integral_prod _ ((hF2.integrable (by norm_num)).comp_fst (γpi ι))]
    simp only [integral_const,probReal_univ,one_smul,hFmean]
  refine ⟨hprod,?_⟩
  rw [← hCenterEq]
  have hbound:=gaussian_maximal_correlation_centered ρ s h hρ hF hG0m hF2 hG02 hG0mean
  calc
    _ ≤ |ρ| * ‖hF2.toLp F‖*‖hG02.toLp G0‖ := hbound
    _ ≤ |ρ| * Real.sqrt C*Real.sqrt C := by gcongr
    _ = C * |ρ| := by rw [mul_assoc,Real.mul_self_sqrt hC];ring

end
end SlowEquilibration.GaussianMaximalCorrelation

-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOESignedAbsoluteTransfer

/-! Quantitative genuine signed expectation normalization under Gaussian
exponential domination. The weight need not be nonnegative on the exceptional
set; its positive expectation and square bound are derived. -/
@[expose] public section
namespace SlowEquilibration.SignedExponentialNormalizedMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma exponential_integrable {Y : Ω → ℝ} {c : ℝ≥0}
    (hG : HasSubgaussianMGF (fun x=>Y x-∫ y,Y y ∂μ) c μ) :
    Integrable (fun x=>Real.exp (Y x)) μ := by
  apply ((hG.integrable_exp_mul 1).mul_const (Real.exp (∫ y,Y y ∂μ))).congr
  exact ae_of_all μ (fun x=>by simp only [one_mul];rw [← Real.exp_add];congr 1;ring)

lemma mean_lower_bound {Y S : Ω → ℝ} (hY : Integrable Y μ) {c : ℝ≥0}
    (hG : HasSubgaussianMGF (fun x=>Y x-∫ y,Y y ∂μ) c μ)
    (hcomp : (∫ x,Real.exp (Y x) ∂μ)≤2*(∫ x,S x ∂μ)) :
    Real.exp (∫ y,Y y ∂μ)/2 ≤ ∫ x,S x ∂μ := by
  have hJ:=convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all μ (fun _=>mem_univ _)) hY (exponential_integrable hG)
  linarith

/-- The genuine signed weight normalized by its own positive expectation
has an actual dimension independent ordinary second moment. -/
theorem normalized_second_moment {Y S : Ω → ℝ} (hY : Integrable Y μ)
    (hS : AEMeasurable S μ) {c : ℝ≥0}
    (hG : HasSubgaussianMGF (fun x=>Y x-∫ y,Y y ∂μ) c μ)
    (hdom : ∀ᵐ x ∂μ,|S x|≤Real.exp (Y x))
    (hcomp : (∫ x,Real.exp (Y x) ∂μ)≤2*(∫ x,S x ∂μ)) :
    0 < ∫ x,S x ∂μ ∧ MemLp (fun x=>S x/(∫ y,S y ∂μ)) 2 μ ∧
      (∫ x,(S x/(∫ y,S y ∂μ))^2 ∂μ) ≤ 4*Real.exp (2*(c:ℝ)) := by
  let m:=∫ y,Y y ∂μ
  let M:=∫ y,S y ∂μ
  have hlow : Real.exp m/2≤M:=mean_lower_bound hY hG hcomp
  have hM : 0 < M:=(half_pos (Real.exp_pos m)).trans_le hlow
  have habs : ∀ᵐ x ∂μ,|S x/M|≤2*Real.exp (Y x-m) := by
    filter_upwards [hdom] with x hx
    rw [abs_div,abs_of_pos hM]
    calc
      _ ≤ Real.exp (Y x)/(Real.exp m/2) := div_le_div₀ (Real.exp_pos _).le hx (half_pos (Real.exp_pos m)) hlow
      _ = _ := by rw [Real.exp_sub];field_simp
  have hsquare : ∀ᵐ x ∂μ,(S x/M)^2≤4*Real.exp (2*(Y x-m)) := by
    filter_upwards [habs] with x hx
    have hh:=pow_le_pow_left₀ (abs_nonneg _) hx 2
    norm_num only [sq_abs,mul_pow,← Real.exp_nat_mul,Nat.cast_ofNat] at hh
    exact hh
  have he : Integrable (fun x=>4*Real.exp (2*(Y x-m))) μ := (hG.integrable_exp_mul 2).const_mul 4
  have hi : Integrable (fun x=>(S x/M)^2) μ := he.mono'
    ((hS.div_const M).pow_const 2).aestronglyMeasurable (by
      filter_upwards [hsquare] with x hx
      simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hx)
  refine ⟨hM,(memLp_two_iff_integrable_sq (hS.div_const M).aestronglyMeasurable).mpr hi,?_⟩
  calc
    _ ≤ ∫ x,4*Real.exp (2*(Y x-m)) ∂μ := integral_mono_ae hi he hsquare
    _ = 4*mgf (fun x=>Y x-m) μ 2 := by rw [integral_const_mul];rfl
    _ ≤ 4*Real.exp (2*(c:ℝ)) := by
      have hh:=mul_le_mul_of_nonneg_left (hG.mgf_le 2) (by norm_num : (0:ℝ)≤4)
      simpa only [show (c:ℝ)*2^2/2=2*(c:ℝ) by ring] using hh

/-- Actual exponential mass on an arbitrary measurable exceptional set,
normalized by the genuine signed expectation. -/
theorem normalized_exponential_on_bad {Y S : Ω → ℝ} (hY : Integrable Y μ) {c : ℝ≥0}
    (hG : HasSubgaussianMGF (fun x=>Y x-∫ y,Y y ∂μ) c μ)
    (hcomp : (∫ x,Real.exp (Y x) ∂μ)≤2*(∫ x,S x ∂μ))
    {B : Set Ω} (hB : MeasurableSet B) :
    (∫ x in B,Real.exp (Y x)/(∫ y,S y ∂μ) ∂μ) ≤
      2*Real.exp (c:ℝ)*Real.sqrt (μ.real B) := by
  let m:=∫ y,Y y ∂μ
  let M:=∫ y,S y ∂μ
  have hlow : Real.exp m/2≤M:=mean_lower_bound hY hG hcomp
  have hM : 0 < M:=(half_pos (Real.exp_pos m)).trans_le hlow
  have hh:=RareEventMomentTransfer.exponential_on_bad_event_bound hG hB
  have he : (fun x=>Real.exp (Y x))=(fun x=>Real.exp m*Real.exp (Y x-m)) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  rw [integral_div,he,integral_const_mul]
  apply (div_le_iff₀ hM).mpr
  calc
    _ ≤ Real.exp m*(Real.exp (c:ℝ)*Real.sqrt (μ.real B)) :=
      mul_le_mul_of_nonneg_left hh (Real.exp_nonneg _)
    _ ≤ _ := by
      have hnonneg : 0 ≤ Real.exp (c:ℝ)*Real.sqrt (μ.real B):=by positivity
      nlinarith [mul_le_mul_of_nonneg_right hlow hnonneg]

end
end SlowEquilibration.SignedExponentialNormalizedMoments

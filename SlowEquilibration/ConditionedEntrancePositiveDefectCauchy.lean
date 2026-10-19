-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceGradientCauchy
public import Mathlib.Tactic

/-! Cauchy–Schwarz for the source pairing's positive initial forcing.
It treats `I-F` as one difference, so no integrability of its two
individual commutator summands is needed. -/
@[expose] public section
noncomputable section
open MeasureTheory
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem positive_initial_reference_defect_cauchy
    {E : Type*} [MeasurableSpace E] (ν : Measure E)
    (k I F U : E → ℝ)
    (hk : Measurable k) (hIm : Measurable I) (hFm : Measurable F)
    (hUm : Measurable U)
    (hIpos : ∀ᵐ z ∂ν, 1 ≤ I z)
    (hFpos : ∀ᵐ z ∂ν, 1 ≤ F z)
    (hUb : ∀ᵐ z ∂ν, 0 ≤ U z ∧ U z ≤ 1)
    (hIi : Integrable I ν) (hFi : Integrable F ν)
    (hKIi : Integrable (fun z => k z ^ 2 * I z) ν)
    (hKFi : Integrable (fun z => k z ^ 2 * F z) ν) :
    |∫ z, k z * (I z - F z) * U z ∂ν| ≤
      Real.sqrt (((∫ z, k z ^ 2 * I z ∂ν) +
        (∫ z, k z ^ 2 * F z ∂ν)) *
        ((∫ z, I z ∂ν) + (∫ z, F z ∂ν))) := by
  let W : E → ℝ := fun z => I z + F z
  let X : E → ℝ := fun z => k z * Real.sqrt (W z)
  let Y : E → ℝ := fun z => (I z - F z) * U z / Real.sqrt (W z)
  have hWm : Measurable W := hIm.add hFm
  have hXm : AEStronglyMeasurable X ν := (hk.mul hWm.sqrt).aestronglyMeasurable
  have hYm : AEStronglyMeasurable Y ν :=
    (((hIm.sub hFm).mul hUm).div hWm.sqrt).aestronglyMeasurable
  have hWpos : ∀ᵐ z ∂ν, 0 < W z := by
    filter_upwards [hIpos,hFpos] with z hi hf
    dsimp only [W]
    linarith
  have hXsq : (fun z => ‖X z‖ ^ 2) =ᵐ[ν]
      (fun z => k z ^ 2 * I z + k z ^ 2 * F z) := by
    filter_upwards [hWpos] with z hw
    dsimp only [X,W]
    rw [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (by linarith)]
    ring
  have hXint : Integrable (fun z => ‖X z‖ ^ 2) ν :=
    (hKIi.add hKFi).congr hXsq.symm
  have hYsq : ∀ᵐ z ∂ν, ‖Y z‖ ^ 2 ≤ W z := by
    filter_upwards [hIpos,hFpos,hUb] with z hi hf hu
    have hwp : 0 < W z := by dsimp only [W]; linarith
    have hs : 0 < Real.sqrt (W z) := Real.sqrt_pos.2 hwp
    have hu2 : U z ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hu.2)]
    have hd : (I z - F z)^2 ≤ (W z)^2 := by
      dsimp only [W]
      nlinarith [mul_nonneg (by linarith : 0 ≤ I z)
        (by linarith : 0 ≤ F z)]
    dsimp only [Y]
    rw [Real.norm_eq_abs,sq_abs,div_pow,mul_pow,Real.sq_sqrt hwp.le]
    apply (div_le_iff₀ hwp).2
    have hdu : (I z - F z)^2 * U z^2 ≤ W z ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hu2 (sq_nonneg (I z-F z))]
    nlinarith
  have hYint : Integrable (fun z => ‖Y z‖ ^ 2) ν := by
    apply Integrable.mono_nonneg (hIi.add hFi) (by fun_prop)
      (by filter_upwards [] with z; positivity)
    simpa only [W, Pi.add_apply] using hYsq
  have hCross : (fun z => inner ℝ (X z) (Y z)) =ᵐ[ν]
      (fun z => k z * (I z - F z) * U z) := by
    filter_upwards [hWpos] with z hw
    have hs : Real.sqrt (W z) ≠ 0 := (Real.sqrt_pos.2 hw).ne'
    dsimp only [X,Y]
    simp only [RCLike.inner_apply,conj_trivial]
    field_simp
  have h := integral_inner_abs_le_sqrt ν X Y hXm hYm hXint hYint
  rw [integral_congr_ae hCross] at h
  have hXintEq : (∫ z, ‖X z‖ ^ 2 ∂ν) =
      (∫ z, k z ^ 2 * I z ∂ν) + (∫ z, k z ^ 2 * F z ∂ν) := by
    rw [integral_congr_ae hXsq,integral_add hKIi hKFi]
  have hYintLe : (∫ z, ‖Y z‖ ^ 2 ∂ν) ≤
      (∫ z, I z ∂ν) + (∫ z, F z ∂ν) := by
    calc
      _ ≤ ∫ z, W z ∂ν := integral_mono_ae hYint (hIi.add hFi) hYsq
      _ = _ := by exact integral_add hIi hFi
  have hXnonneg : 0 ≤ ∫ z, ‖X z‖ ^ 2 ∂ν :=
    integral_nonneg (fun z => sq_nonneg _)
  rw [hXintEq] at h
  exact h.trans (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hYintLe
    (hXintEq ▸ hXnonneg)))

theorem positive_initial_reference_defect_le_ten_sqrt
    {E : Type*} [MeasurableSpace E] (ν : Measure E)
    (k I F U : E → ℝ)
    (hk : Measurable k) (hIm : Measurable I) (hFm : Measurable F)
    (hUm : Measurable U)
    (hIpos : ∀ᵐ z ∂ν, 1 ≤ I z)
    (hFpos : ∀ᵐ z ∂ν, 1 ≤ F z)
    (hUb : ∀ᵐ z ∂ν, 0 ≤ U z ∧ U z ≤ 1)
    (hIi : Integrable I ν) (hFi : Integrable F ν)
    (hKIi : Integrable (fun z => k z ^ 2 * I z) ν)
    (hKFi : Integrable (fun z => k z ^ 2 * F z) ν)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hImass : (∫ z, I z ∂ν) ≤ 6)
    (hFmass : (∫ z, F z ∂ν) ≤ 6)
    (hKImom : (∫ z, k z ^ 2 * I z ∂ν) ≤ 4*ε)
    (hKFmom : (∫ z, k z ^ 2 * F z ∂ν) ≤ 4*ε) :
    |∫ z, k z * (I z - F z) * U z ∂ν| ≤ 10*Real.sqrt ε := by
  have h := positive_initial_reference_defect_cauchy ν k I F U
    hk hIm hFm hUm hIpos hFpos hUb hIi hFi hKIi hKFi
  have hKnonneg : 0 ≤ (∫ z, k z ^ 2 * I z ∂ν) +
      (∫ z, k z ^ 2 * F z ∂ν) := by
    apply add_nonneg <;> apply integral_nonneg_of_ae
    · filter_upwards [hIpos] with z hz
      exact mul_nonneg (sq_nonneg _) (by linarith)
    · filter_upwards [hFpos] with z hz
      exact mul_nonneg (sq_nonneg _) (by linarith)
  have hMnonneg : 0 ≤ (∫ z, I z ∂ν) + (∫ z, F z ∂ν) := by
    have hi : ∀ᵐ z ∂ν, 0 ≤ I z := hIpos.mono (fun z hz => by linarith)
    have hf : ∀ᵐ z ∂ν, 0 ≤ F z := hFpos.mono (fun z hz => by linarith)
    exact add_nonneg (integral_nonneg_of_ae hi) (integral_nonneg_of_ae hf)
  have hKle : (∫ z, k z ^ 2 * I z ∂ν) +
      (∫ z, k z ^ 2 * F z ∂ν) ≤ 8*ε := by linarith
  have hMle : (∫ z, I z ∂ν) + (∫ z, F z ∂ν) ≤ 12 := by linarith
  have hProd : ((∫ z, k z ^ 2 * I z ∂ν) +
      (∫ z, k z ^ 2 * F z ∂ν)) *
      ((∫ z, I z ∂ν) + (∫ z, F z ∂ν)) ≤ 96*ε := by
    nlinarith [mul_le_mul hKle hMle hMnonneg (by positivity : 0 ≤ 8*ε)]
  have hSqrt : Real.sqrt (96*ε) ≤ 10*Real.sqrt ε := by
    have hsε := Real.sq_sqrt hε
    have hs96 := Real.sq_sqrt (by positivity : 0 ≤ 96*ε)
    have hpε := Real.sqrt_nonneg ε
    have hp96 := Real.sqrt_nonneg (96*ε)
    nlinarith
  exact h.trans ((Real.sqrt_le_sqrt hProd).trans hSqrt)

end SlowEquilibration.ConditionedEntrance

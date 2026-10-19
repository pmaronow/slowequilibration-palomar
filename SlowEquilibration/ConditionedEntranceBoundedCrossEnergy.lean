-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceWeightedGradientDefectCauchy

/-! An integrable gradient cross energy with a bounded multiplier. This
is used for finite-energy justification before the small source-defect
moment is applied in the final absorption step. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 500000

private theorem scalar_weighted_cross
    (F U a b : ℝ) (hF : 1 ≤ F) (hU : |U| ≤ 1) :
    |U * a * b| ≤ (F * b^2 + a^2 / F)/2 := by
  have hpos : 0 < F := by linarith
  have hne : F ≠ 0 := ne_of_gt hpos
  have he : F * ((F*b^2+a^2/F)/2) = ((F*b)^2+a^2)/2 := by
    field_simp [hne]
  have hab : |a*b| ≤ (F*b^2+a^2/F)/2 := by
    apply abs_le.mpr
    constructor
    · apply (mul_le_mul_iff_right₀ hpos).mp
      rw [mul_neg,he]
      nlinarith [sq_nonneg (F*b+a)]
    · apply (mul_le_mul_iff_right₀ hpos).mp
      rw [he]
      nlinarith [sq_nonneg (F*b-a)]
  calc
    |U*a*b| = |U| * |a*b| := by rw [mul_assoc,abs_mul]
    _ ≤ |a*b| := mul_le_of_le_one_left (abs_nonneg _) hU
    _ ≤ _ := hab

/-- Uniform finite control of the literal signed gradient cross term.
The bound also establishes its Bochner integrability. -/
theorem bounded_multiplier_gradient_cross_integrable
    {E ι : Type*} [MeasurableSpace E] [Fintype ι]
    (ν : Measure E) (k F U : E → ℝ) (a b : ι → E → ℝ)
    (hk : Measurable k) (_hF : Measurable F) (hU : Measurable U)
    (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i))
    (hFlo : ∀ᵐ z ∂ν, 1 ≤ F z)
    (hUb : ∀ᵐ z ∂ν, |U z| ≤ 1)
    (K : ℝ) (hK : 0 ≤ K) (hkbound : ∀ᵐ z ∂ν, |k z| ≤ K)
    (hJint : Integrable (fun z => ∑ i, (a i z)^2 / F z) ν)
    (hBint : Integrable (fun z => F z * (∑ i, (b i z)^2)) ν) :
    Integrable (fun z => k z * U z * (∑ i, a i z * b i z)) ν ∧
    |∫ z, k z * U z * (∑ i, a i z * b i z) ∂ν| ≤
      K/2 * ((∫ z, ∑ i, (a i z)^2 / F z ∂ν) +
        (∫ z, F z * (∑ i, (b i z)^2) ∂ν)) := by
  let J : E → ℝ := fun z => ∑ i, (a i z)^2 / F z
  let B : E → ℝ := fun z => F z * (∑ i, (b i z)^2)
  let C : E → ℝ := fun z => k z * U z * (∑ i, a i z * b i z)
  let D : E → ℝ := fun z => K/2 * (J z+B z)
  have hDi : Integrable D ν := (hJint.add hBint).const_mul (K/2)
  have hCm : Measurable C := (hk.mul hU).mul
    (Finset.measurable_sum _ (fun i _ => (ha i).mul (hb i)))
  have hp : ∀ᵐ z ∂ν, |C z| ≤ D z := by
    filter_upwards [hFlo,hUb,hkbound] with z hz hu hkz
    have hsum : |U z * (∑ i, a i z * b i z)| ≤
        (B z + J z)/2 := by
      calc
        |U z * (∑ i, a i z * b i z)| =
            |∑ i, U z * a i z * b i z| := by
              rw [Finset.mul_sum]
              congr 1
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ ≤ ∑ i, |U z * a i z * b i z| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, (F z * (b i z)^2 + (a i z)^2 / F z)/2 :=
          Finset.sum_le_sum (fun i _ => scalar_weighted_cross _ _ _ _ hz hu)
        _ = (B z + J z)/2 := by
          rw [← Finset.sum_div,Finset.sum_add_distrib,← Finset.mul_sum]
    have hnonneg : 0 ≤ (B z+J z)/2 := by
      dsimp only [B,J]
      apply div_nonneg
      apply add_nonneg
      · exact mul_nonneg (by linarith)
          (Finset.sum_nonneg (fun i _ => sq_nonneg _))
      · exact Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (by linarith))
      · norm_num
    calc
      |C z| = |k z| * |U z * (∑ i, a i z * b i z)| := by
        dsimp only [C]
        rw [mul_assoc,abs_mul]
      _ ≤ K * ((B z+J z)/2) :=
        (mul_le_mul hkz hsum (abs_nonneg _) hK)
      _ = D z := by dsimp only [D]; ring
  have hCi : Integrable C ν := hDi.mono' hCm.aestronglyMeasurable
    (hp.mono (fun z hz => by simpa only [Real.norm_eq_abs] using hz))
  refine ⟨hCi,?_⟩
  have habs : |∫ z, C z ∂ν| ≤ ∫ z, |C z| ∂ν := abs_integral_le_integral_abs
  have hmono : (∫ z, |C z| ∂ν) ≤ ∫ z, D z ∂ν :=
    integral_mono_ae hCi.abs hDi hp
  have hD : (∫ z, D z ∂ν) = K/2 * ((∫ z, J z ∂ν)+(∫ z, B z ∂ν)) := by
    rw [integral_const_mul,integral_add hJint hBint]
  exact habs.trans (hmono.trans_eq hD)

end SlowEquilibration.ConditionedEntrance

-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.GaussianRadialEnergyTilt

/-! Uniform logarithmic-window bounds, derived by exact completion of
the original radial Gaussian square. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianRadialEnergyTilt
open Set MeasureTheory RadialGaussianBounds RadialLaplaceBounds
set_option maxHeartbeats 300000

def correctionBound (a A B : ℝ) : ℝ := |-A/2+B^2/(4*a)|

theorem heightCorrection_bounds {a N : ℝ} (ha : 0 < a) (hN : 0 < N)
    (A B c₀ σ : ℝ) (hσ : σ^2/N ≤ 1) :
    -c₀*σ-correctionBound a A B ≤ heightCorrection a N A B c₀ σ ∧
      heightCorrection a N A B c₀ σ ≤ -c₀*σ+correctionBound a A B := by
  have he : heightCorrection a N A B c₀ σ+c₀*σ=
      (-A/2+B^2/(4*a))*(σ^2/N) := by
    unfold heightCorrection
    field_simp [ha.ne',hN.ne']
    ring
  have hq : 0 ≤ σ^2/N := by positivity
  have hh : |heightCorrection a N A B c₀ σ+c₀*σ| ≤ correctionBound a A B := by
    rw [he,abs_mul,abs_of_nonneg hq]
    exact (mul_le_mul_of_nonneg_left hσ (abs_nonneg _)).trans_eq (mul_one _)
  have hl := (abs_le.mp hh).1
  have hu := (abs_le.mp hh).2
  constructor <;> linarith

theorem tilted_integral_log_bounds {w : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    {c C a b N A B c₀ m σ : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hi : IntegrableOn (tiltedDensity w N A B c₀ m σ) U)
    (h0 : ∀ k∈U,0 ≤ w k)
    (hl : ∀ k∈U,c*gaussian (b*N) m k ≤ w k)
    (hu : ∀ k∈U,w k ≤ C*gaussian (a*N) m k)
    (hInside : Icc (shiftedCenter b N B m σ-1/Real.sqrt N)
      (shiftedCenter b N B m σ+1/Real.sqrt N)⊆U) (hσ : σ^2/N ≤ 1) :
    (lowerConstant c b*Real.exp (-correctionBound b A B))*Real.exp (-c₀*σ)/Real.sqrt N ≤
      (∫ k in U,tiltedDensity w N A B c₀ m σ k) ∧
    (∫ k in U,tiltedDensity w N A B c₀ m σ k) ≤
      (upperConstant C a*Real.exp (correctionBound a A B))*Real.exp (-c₀*σ)/Real.sqrt N := by
  constructor
  · apply le_trans _ (tilted_integral_lower hU hc hb hN hi h0 hl hInside)
    have he := Real.exp_le_exp.mpr (heightCorrection_bounds hb hN A B c₀ σ hσ).1
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left he (by unfold lowerConstant;positivity : 0 ≤ lowerConstant c b)) (Real.sqrt_nonneg N)
    refine le_trans ?_ hh
    apply le_of_eq
    rw [Real.exp_sub,Real.exp_neg]
    ring
  · apply (tilted_integral_upper hU hC ha hN hi hu).trans
    have he := Real.exp_le_exp.mpr (heightCorrection_bounds ha hN A B c₀ σ hσ).2
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left he (by unfold upperConstant;positivity : 0 ≤ upperConstant C a)) (Real.sqrt_nonneg N)
    refine hh.trans_eq ?_
    rw [Real.exp_add]
    ring

end SlowEquilibration.GaussianRadialEnergyTilt

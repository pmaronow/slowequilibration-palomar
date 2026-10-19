-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianFullBorderHighMomentTransfer
public import SlowEquilibration.CommonHessianGapHighMomentRates

/-! Deterministic every-real-q rate conversion for the actual full-border
Schur transfer. Model consumers discharge the displayed primitive moments. -/
@[expose] public section
namespace SlowEquilibration.BorderSchurExpectation
noncomputable section
open Function MeasureTheory ProbabilityTheory Set
open GaussianQuadraticVariance SchurDimensionRates
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem q_error_good_event_rate {Ω:Type*} [MeasurableSpace Ω]
    (μ:Measure Ω) [IsProbabilityMeasure μ] (D B T:Ω→ℝ)
    (hD:Measurable D) (hB:Measurable B) (hT:Measurable T) (s q:ℝ) (hq:0 ≤ q)
    (hDI:Integrable (fun x=>|D x|^(2*q)) μ)
    (hBI:Integrable (fun x=>|B x|^(2*q)) μ)
    (hTI:Integrable (fun x=>|T x-s|^(2*q)) μ)
    (G:Set Ω) (hG:MeasurableSet G)
    (hgood:∀ᵐ x ∂μ,x∈G → |D x-|s| * B x| ≤ |B x| * |T x-s|)
    (n:ℕ) {a ε KD KB KT:ℝ} (ha:0<a) (hε:0 ≤ ε)
    (hInv:1/Real.sqrt (n+3:ℕ) ≤ ε) (hKD:0 ≤ KD) (hKB:0 ≤ KB) (hKT:0 ≤ KT)
    (hDM:(∫ x,|D x|^(2*q) ∂μ) ≤ KD)
    (hBM:(∫ x,|B x|^(2*q) ∂μ) ≤ KB)
    (hTM:(∫ x,|T x-s|^(2*q) ∂μ) ≤ KT*ε^(2*q))
    (hGap:μ.real Gᶜ ≤ Real.exp (-(n+1:ℝ)*a^2/(16*Real.pi^2))) :
    Integrable (fun x=>|D x-|s| * B x|^q) μ ∧
      (∫ x,|D x-|s| * B x|^q ∂μ) ≤
        (Real.sqrt KB*Real.sqrt KT+(2:ℝ)^q*(Real.sqrt KD+|s|^q*Real.sqrt KB)*gapMomentConstant a q)*ε^q:=by
  have hBase:=integral_q_error_of_good_event μ D B T hD hB hT s q hq hDI hBI hTI G hG hgood
  have hTrace:Real.sqrt (∫ x,|T x-s|^(2*q) ∂μ) ≤ Real.sqrt KT*ε^q:=by
    have hh:=Real.sqrt_le_sqrt hTM
    rw [Real.sqrt_mul hKT,←rpow_square_eq_double hε,Real.sqrt_sq (Real.rpow_nonneg hε q)] at hh
    exact hh
  have hGapQ:Real.sqrt (μ.real Gᶜ) ≤ gapMomentConstant a q*ε^q:=by
    have hh:=(Real.sqrt_le_sqrt hGap).trans (sqrt_exp_gap_le_ambient_q n ha hq)
    exact hh.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hInv hq) (by unfold gapMomentConstant;positivity))
  refine ⟨hBase.1,hBase.2.trans ?_⟩
  calc
    _ ≤ Real.sqrt KB*(Real.sqrt KT*ε^q)+(2:ℝ)^q*(Real.sqrt KD+|s|^q*Real.sqrt KB)*
        (gapMomentConstant a q*ε^q):=by
      gcongr
    _=_:=by ring

end
end SlowEquilibration.BorderSchurExpectation

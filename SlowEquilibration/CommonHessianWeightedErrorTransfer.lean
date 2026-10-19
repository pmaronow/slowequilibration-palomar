-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianSourceFullBorderHighMoments

/-! Exact real-moment transport to the source Schur-weighted determinant
normalization. The scalar is positive on the actual exterior window. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
open Function MeasureTheory ProbabilityTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

theorem weighted_error_q_transfer {Ω:Type*} [MeasurableSpace Ω]
    (P:Measure Ω) (D B:Ω→ℝ) {s t K ε q:ℝ} (hs:0<s) (ht:0<t) (hst:t ≤ s)
    (hq:0 ≤ q) (hK:0 ≤ K) (hε:0 ≤ ε)
    (hI:Integrable (fun x=>|D x-s*B x|^q) P)
    (hE:(∫ x,|D x-s*B x|^q ∂P) ≤ K*ε^q) :
    Integrable (fun x=>|D x/s-B x|^q) P ∧
      (∫ x,|D x/s-B x|^q ∂P) ≤ (K/t^q)*ε^q:=by
  have hEq (x):|D x/s-B x|^q=s⁻¹^q*|D x-s*B x|^q:=by
    rw [show D x/s-B x=(D x-s*B x)/s by field_simp]
    rw [abs_div,abs_of_pos hs,Real.div_rpow (abs_nonneg _) hs.le]
    rw [Real.inv_rpow hs.le]
    ring
  refine ⟨by simpa only [hEq] using hI.const_mul (s⁻¹^q),?_⟩
  simp only [hEq,integral_const_mul]
  have hInv:s⁻¹ ≤ t⁻¹:=inv_anti₀ ht hst
  have hPow:s⁻¹^q ≤ t⁻¹^q:=Real.rpow_le_rpow (by positivity) hInv hq
  calc
    _ ≤ s⁻¹^q*(K*ε^q):=mul_le_mul_of_nonneg_left hE (by positivity)
    _ ≤ t⁻¹^q*(K*ε^q):=mul_le_mul_of_nonneg_right hPow (by positivity)
    _=_:=by rw [Real.inv_rpow ht.le];ring

end
end SlowEquilibration.GaussianQuadraticVariance

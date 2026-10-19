-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPResidualMargin
public import SlowEquilibration.SphericalGeneralLikelihoodContiguity

@[expose] public section
/-! The actual critical TAP residual is strictly below its own static
threshold. A genuine uniform quadratic RS gap extends its temperature
strictly, so the proved normalized partition lower tail applies without
a supplied residual-static or tightness premise. -/
namespace SlowEquilibration.SphericalTAPResidualStrictStatic
noncomputable section
open Set Filter
open SphericalTAPCertificate SphericalTAPResidual SphericalTAPResidualMargin SphericalModel
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem finite_covariance_quadratic_upper (μ:FiniteMixture) {t:ℝ} (ht:t∈Icc (0:ℝ) 1) :
    μ.xi t ≤ μ.xi 1*t^2:=by
  have hred:μ.reducedCovariance t ≤ μ.xi 1:=by
    unfold FiniteMixture.reducedCovariance FiniteMixture.xi
    simp only [one_pow,mul_one]
    apply Finset.sum_le_sum
    intro p _
    exact mul_le_of_le_one_right (μ.nonneg p) (pow_le_one₀ ht.1 ht.2)
  rw [μ.xi_eq_reducedCovariance]
  exact mul_le_mul_of_nonneg_right hred (sq_nonneg t)

/-- Analytic threshold openness follows from a quantitative scalar gap,
not from assuming physical RS or a desired pressure limit. -/
theorem strict_static_of_uniform_quadratic_gap (μ:FiniteMixture) {β κ:ℝ}
    (hβ:0 ≤ β) (hκ:0<κ)
    (hgap:∀ t∈Ioo (0:ℝ) 1,κ*t^2 ≤ -Thresholds.Phi μ.xi β t) :
    β<Thresholds.staticThreshold μ.xi:=by
  let V:=μ.xi 1
  have hV:0<V:=μ.xi_pos (by norm_num)
  let B:=Real.sqrt (β^2+κ/(2*V))
  have hinc:0<κ/(2*V):=div_pos hκ (by positivity)
  have hB:0<B:=Real.sqrt_pos.mpr (by positivity)
  have hBsq:B^2=β^2+κ/(2*V):=Real.sq_sqrt (by positivity)
  have hBgt:β<B:=by nlinarith
  have hBstatic:B ≤ Thresholds.staticThreshold μ.xi:=by
    apply (μ.Phi_nonpos_iff_le_staticThreshold hB.le).mp
    intro t ht
    have H:=hgap t ht
    have hxi:=finite_covariance_quadratic_upper μ ⟨ht.1.le,ht.2.le⟩
    have hdiff:0 ≤ B^2-β^2:=by linarith
    have hterm:(B^2-β^2)*μ.xi t ≤ κ/2*t^2:=by
      calc
        _ ≤ (B^2-β^2)*(V*t^2):=mul_le_mul_of_nonneg_left hxi hdiff
        _ = _:=by rw [hBsq];field_simp [hV.ne'];ring
    unfold Thresholds.Phi at H ⊢
    nlinarith [sq_nonneg t]
  exact hBgt.trans_le hBstatic

/-- The strict source certificate proves a genuine open RS temperature
region for the literal finite Taylor residual, including quadratic terms. -/
theorem certificate_residual_lt_staticThreshold {μ:FiniteMixture} {β x Q:ℝ}
    (h:Certificate μ β x Q) :
    β<Thresholds.staticThreshold (μ.taylorResidual h.overlap_range.1 (sub_pos.mpr h.overlap_range.2)).xi:=by
  let θ:=μ.taylorResidual h.overlap_range.1 (sub_pos.mpr h.overlap_range.2)
  obtain ⟨κ,hκ,hgap⟩:=uniform_quadratic_gap θ β (residual_Phi_neg h) (residual_replicon_lt_one h)
  exact strict_static_of_uniform_quadratic_gap θ h.beta_pos.le hκ hgap

/-- The genuine fixed-temperature normalized residual partition stays
away from zero; no normalized-tightness property is an input. -/
theorem certificate_residual_likelihoodLowerTailTight {μ:FiniteMixture} {β x Q:ℝ}
    (h:Certificate μ β x Q) :
    LikelihoodLowerTailTight (μ.taylorResidual h.overlap_range.1 (sub_pos.mpr h.overlap_range.2)) β:=
  general_likelihoodLowerTailTight _ h.beta_pos (certificate_residual_lt_staticThreshold h)

end
end SlowEquilibration.SphericalTAPResidualStrictStatic

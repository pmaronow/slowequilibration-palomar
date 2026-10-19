-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCertificate
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section
noncomputable section

namespace SlowEquilibration.CSTAPContactTrialDerivative

open MeasureTheory Set CrisantiSommers SphericalTAPCertificate

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

/-- The first variation of the manuscript's ground-profile perturbation
`ℓ_ε(v) = β x̂(v) + ε(q-v)` is the negative contact potential.  This is the
integration-by-parts step in source §5 before the quantitative TAP gap. -/
theorem contact_trial_first_variation (μ : FiniteMixture) {β x Q q : ℝ}
    (h : Certificate μ β x Q) (hq : q ∈ Ioo (0 : ℝ) 1) :
    (∫ v in (0 : ℝ)..q,
      (β^2 * μ.xi2 v - 1 / (xHat (twoAtom x Q) v)^2) * (q-v)) =
      -CSStructure.potential μ β (twoAtom x Q) q := by
  let ζ : Measure ℝ := twoAtom x Q
  let V : ℝ → ℝ := CSStructure.potential μ β ζ
  haveI : IsProbabilityMeasure ζ := twoAtom_probability ⟨h.weight_range.1.le, h.weight_range.2.le⟩
  have hcut : HasCutoff ζ Q := twoAtom_hasCutoff ⟨h.overlap_range.1.le, h.overlap_range.2⟩
  have hxcont : Continuous (xHat ζ) := xHat_continuous ζ hcut
  have hxne (v : ℝ) (hv : v ∈ Icc (0 : ℝ) q) : xHat ζ v ≠ 0 :=
    (xHat_pos ζ hcut (hv.2.trans_lt hq.2)).ne'
  have hgcont : ContinuousOn
      (fun v : ℝ => (β^2*μ.xi2 v - 1/(xHat ζ v)^2)*(q-v))
      (Icc (0 : ℝ) q) := by
    have hξ : Continuous μ.xi2 := continuous_iff_continuousAt.mpr
      (fun v => (μ.hasDerivAt_xi2 v).continuousAt)
    have hh : ContinuousOn (fun v : ℝ => ((xHat ζ v)^2)⁻¹) (Icc (0 : ℝ) q) :=
      (hxcont.continuousOn.pow 2).inv₀ (fun v hv => pow_ne_zero 2 (hxne v hv))
    have hbase : ContinuousOn
        (fun v : ℝ => β^2*μ.xi2 v - ((xHat ζ v)^2)⁻¹)
        (Icc (0 : ℝ) q) :=
      (continuousOn_const.mul hξ.continuousOn).sub hh
    have hlin : ContinuousOn (fun v : ℝ => q-v) (Icc (0 : ℝ) q) :=
      continuousOn_const.sub continuousOn_id
    convert hbase.mul hlin using 1
    funext v
    simp only [Pi.mul_apply, one_div]
  have hgint : IntervalIntegrable
      (fun v : ℝ => (β^2*μ.xi2 v - 1/(xHat ζ v)^2)*(q-v))
      volume 0 q := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hq.1.le] using hgcont
  let F : ℝ → ℝ := fun v => -((q-v)*deriv V v)-V v
  have hFderiv (v : ℝ) (hv : v ∈ Icc (0 : ℝ) q) :
      HasDerivAt F ((β^2*μ.xi2 v - 1/(xHat ζ v)^2)*(q-v)) v := by
    have hv1 : v < 1 := hv.2.trans_lt hq.2
    have hV := CSStructure.potential_hasDerivAt μ β ζ hcut hv1
    have hV' := CSStructure.potential_deriv_hasDerivAt μ β ζ hcut hv1
    have hD : HasDerivAt V (deriv V v) v := by
      convert hV using 1
      exact hV.deriv
    dsimp [F]
    convert ((((hasDerivAt_const v q).sub (hasDerivAt_id v)).mul hV').neg.sub hD) using 1
    · funext t
      change -((q-t)*deriv V t)-V t =
        -((q-t)*deriv (CSStructure.potential μ β ζ) t)-V t
      rfl
    · dsimp only [Pi.sub_apply, Pi.mul_apply]
      simp only [id_eq]
      ring
  have hFint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := q) (f := F)
    (fun v hv => hFderiv v (by simpa only [uIcc_of_le hq.1.le] using hv)) hgint
  have h0 := CSStructure.potential_origin μ β ζ hcut
  change (∫ v in (0 : ℝ)..q,
    (β^2 * μ.xi2 v - 1 / (xHat ζ v)^2) * (q-v)) = -V q
  rw [hFint]
  dsimp [F]
  change V 0 = 0 ∧ deriv V 0 = 0 at h0
  rw [h0.1, h0.2]
  ring

end SlowEquilibration.CSTAPContactTrialDerivative

-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSTAPGroundTrialQuadratic

@[expose] public section
noncomputable section

namespace SlowEquilibration.CSTAPGroundTrialContactGap

open MeasureTheory Set CrisantiSommers SphericalTAPCertificate
open CSTAPGroundTrialQuadratic

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

/-- The literal quadratic coefficient of the generalized TAP ground trial is
positive at every nonzero overlap below one. -/
theorem ground_trial_curvature_pos (μ : FiniteMixture) {β x Q q : ℝ}
    (h : Certificate μ β x Q) (hq : q ∈ Ioo (0 : ℝ) 1) :
    0 < curvature β (twoAtom x Q) q := by
  let ζ : Measure ℝ := twoAtom x Q
  haveI : IsProbabilityMeasure ζ :=
    twoAtom_probability ⟨h.weight_range.1.le, h.weight_range.2.le⟩
  have hcut : HasCutoff ζ Q :=
    twoAtom_hasCutoff ⟨h.overlap_range.1.le, h.overlap_range.2⟩
  have hxcont : Continuous (xHat ζ) := xHat_continuous ζ hcut
  have hxpos (v : ℝ) (hv : v ∈ Icc (0 : ℝ) q) : 0 < β*xHat ζ v :=
    mul_pos h.beta_pos (xHat_pos ζ hcut (hv.2.trans_lt hq.2))
  have hc : ContinuousOn (fun v : ℝ => (q-v)^2/(β*xHat ζ v)^3)
      (Icc (0 : ℝ) q) := by
    have hn : ContinuousOn (fun v : ℝ => (q-v)^2) (Icc (0 : ℝ) q) := by
      fun_prop
    exact hn.div ((continuous_const.mul hxcont).continuousOn.pow 3)
      (fun v hv => pow_ne_zero 3 (hxpos v hv).ne')
  change 0 < ∫ v in (0 : ℝ)..q, (q-v)^2/(β*xHat ζ v)^3
  apply intervalIntegral.integral_pos hq.1 hc
  · intro v hv
    exact div_nonneg (sq_nonneg _) (pow_nonneg (hxpos v ⟨hv.1.le,hv.2⟩).le _)
  · refine ⟨q/2,⟨by linarith [hq.1],by linarith [hq.1]⟩,?_⟩
    exact div_pos (sq_pos_of_ne_zero (by linarith [hq.1]))
      (pow_pos (hxpos (q/2) ⟨by linarith [hq.1],by linarith [hq.1]⟩) _)

/-- The exact positive contact potential produces a strict optimized gap for
the explicit admissible source profile. The Chen–Sen ground variational
identification and Subag physical TAP representation are separate inputs. -/
theorem ground_trial_strict_contact_gap (μ : FiniteMixture) {β x Q q : ℝ}
    (h : Certificate μ β x Q) (hq : q ∈ Ioo (0 : ℝ) 1) (hqQ : q ≠ Q) :
    functional μ β (twoAtom x Q) q
        (CSStructure.potential μ β (twoAtom x Q) q /
          (2*β^2*curvature β (twoAtom x Q) q)) ≤
      functional μ β (twoAtom x Q) q 0 -
        (CSStructure.potential μ β (twoAtom x Q) q)^2 /
          (8*β^4*curvature β (twoAtom x Q) q) := by
  let V := CSStructure.potential μ β (twoAtom x Q) q
  let M := curvature β (twoAtom x Q) q
  have hV : 0 < V := h.positive_off_contact q hq hqQ
  have hM : 0 < M := ground_trial_curvature_pos μ h hq
  have hε : 0 ≤ V/(2*β^2*M) := by positivity
  have htrial := ground_trial_quadratic_gap μ h hq hε
  change functional μ β (twoAtom x Q) q (V/(2*β^2*M)) ≤
    functional μ β (twoAtom x Q) q 0 - V^2/(8*β^4*M)
  convert htrial using 1
  field_simp [h.beta_pos.ne',hM.ne']
  ring

end SlowEquilibration.CSTAPGroundTrialContactGap

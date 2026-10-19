-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSTAPContactTrialDerivative

@[expose] public section
noncomputable section

namespace SlowEquilibration.CSTAPGroundTrialQuadratic

open MeasureTheory Set CrisantiSommers SphericalTAPCertificate

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

private theorem inv_add_quadratic_upper {a u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    (a+u)⁻¹ ≤ a⁻¹-u/a^2+u^2/a^3 := by
  have hp : 0 < a+u := by linarith
  have he : (a+u)⁻¹ = a⁻¹-u/a^2+u^2/a^3-u^3/(a^3*(a+u)) := by
    field_simp [ha.ne',hp.ne']
    ring
  rw [he]
  exact sub_le_self _ (by positivity)

def profile (β : ℝ) (ζ : Measure ℝ) (q ε v : ℝ) : ℝ :=
  β*xHat ζ v+ε*(q-v)

def functional (μ : FiniteMixture) (β : ℝ) (ζ : Measure ℝ) (q ε : ℝ) : ℝ :=
  (∫ v in (0 : ℝ)..q,
    μ.xi2 v*profile β ζ q ε v+(profile β ζ q ε v)⁻¹)/2

def curvature (β : ℝ) (ζ : Measure ℝ) (q : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..q, (q-v)^2/(β*xHat ζ v)^3

/-- The quantitative one-parameter ground-profile trial estimate in source
§5. The actual first variation is supplied by the previous proved contact
identity; the quadratic term comes from the exact reciprocal remainder. -/
theorem ground_trial_quadratic_gap (μ : FiniteMixture) {β x Q q ε : ℝ}
    (h : Certificate μ β x Q) (hq : q ∈ Ioo (0 : ℝ) 1) (hε : 0 ≤ ε) :
    functional μ β (twoAtom x Q) q ε ≤
      functional μ β (twoAtom x Q) q 0 -
        ε*CSStructure.potential μ β (twoAtom x Q) q/(2*β^2)+
        ε^2*curvature β (twoAtom x Q) q/2 := by
  let ζ : Measure ℝ := twoAtom x Q
  haveI : IsProbabilityMeasure ζ :=
    twoAtom_probability ⟨h.weight_range.1.le, h.weight_range.2.le⟩
  have hcut : HasCutoff ζ Q :=
    twoAtom_hasCutoff ⟨h.overlap_range.1.le, h.overlap_range.2⟩
  have hxcont : Continuous (xHat ζ) := xHat_continuous ζ hcut
  have hxi : Continuous μ.xi2 := continuous_iff_continuousAt.mpr
    (fun v => (μ.hasDerivAt_xi2 v).continuousAt)
  have hxp (v : ℝ) (hv : v ∈ Icc (0 : ℝ) q) : 0 < xHat ζ v :=
    xHat_pos ζ hcut (hv.2.trans_lt hq.2)
  have hbasepos (v : ℝ) (hv : v ∈ Icc (0 : ℝ) q) :
      0 < β*xHat ζ v := mul_pos h.beta_pos (hxp v hv)
  have hprofpos (e : ℝ) (he : 0 ≤ e) (v : ℝ) (hv : v ∈ Icc (0 : ℝ) q) :
      0 < profile β ζ q e v := by
    dsimp [profile]
    have hb : 0 ≤ e*(q-v) := mul_nonneg he (sub_nonneg.mpr hv.2)
    linarith [hbasepos v hv]
  have hprofcont (e : ℝ) : Continuous (profile β ζ q e) := by
    unfold profile
    fun_prop
  have hbasecont : ContinuousOn (fun v : ℝ => (β*xHat ζ v)⁻¹) (Icc (0 : ℝ) q) :=
    (continuous_const.mul hxcont).continuousOn.inv₀
      (fun v hv => (hbasepos v hv).ne')
  have hlincont : ContinuousOn
      (fun v : ℝ => (μ.xi2 v-1/(β*xHat ζ v)^2)*(q-v))
      (Icc (0 : ℝ) q) := by
    have hrec : ContinuousOn (fun v : ℝ => ((β*xHat ζ v)^2)⁻¹)
        (Icc (0 : ℝ) q) :=
      ((continuous_const.mul hxcont).continuousOn.pow 2).inv₀
        (fun v hv => pow_ne_zero 2 (hbasepos v hv).ne')
    have hb : ContinuousOn (fun v : ℝ => μ.xi2 v-((β*xHat ζ v)^2)⁻¹)
        (Icc (0 : ℝ) q) := hxi.continuousOn.sub hrec
    have hc : ContinuousOn (fun v : ℝ => q-v) (Icc (0 : ℝ) q) :=
      continuousOn_const.sub continuousOn_id
    convert hb.mul hc using 1
    funext v
    simp only [Pi.mul_apply, one_div]
  have hquadcont : ContinuousOn
      (fun v : ℝ => (q-v)^2/(β*xHat ζ v)^3)
      (Icc (0 : ℝ) q) := by
    have hc : ContinuousOn (fun v : ℝ => q-v) (Icc (0 : ℝ) q) :=
      continuousOn_const.sub continuousOn_id
    exact (hc.pow 2).div ((continuous_const.mul hxcont).continuousOn.pow 3)
      (fun v hv => pow_ne_zero 3 (hbasepos v hv).ne')
  have hfuncont (e : ℝ) (he : 0 ≤ e) : ContinuousOn
      (fun v : ℝ => μ.xi2 v*profile β ζ q e v+(profile β ζ q e v)⁻¹)
      (Icc (0 : ℝ) q) :=
    (hxi.continuousOn.mul (hprofcont e).continuousOn).add
      ((hprofcont e).continuousOn.inv₀ (fun v hv => (hprofpos e he v hv).ne'))
  have hi (e : ℝ) (he : 0 ≤ e) : IntervalIntegrable
      (fun v : ℝ => μ.xi2 v*profile β ζ q e v+(profile β ζ q e v)⁻¹)
      volume 0 q := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hq.1.le] using hfuncont e he
  have hlinI : IntervalIntegrable
      (fun v : ℝ => (μ.xi2 v-1/(β*xHat ζ v)^2)*(q-v))
      volume 0 q := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hq.1.le] using hlincont
  have hquadI : IntervalIntegrable
      (fun v : ℝ => (q-v)^2/(β*xHat ζ v)^3)
      volume 0 q := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hq.1.le] using hquadcont
  have hpt (v : ℝ) (hv : v ∈ Icc (0 : ℝ) q) :
      μ.xi2 v*profile β ζ q ε v+(profile β ζ q ε v)⁻¹ ≤
        (μ.xi2 v*profile β ζ q 0 v+(profile β ζ q 0 v)⁻¹)+
          ε*((μ.xi2 v-1/(β*xHat ζ v)^2)*(q-v))+
          ε^2*((q-v)^2/(β*xHat ζ v)^3) := by
    let a := β*xHat ζ v
    let u := ε*(q-v)
    have ha : 0 < a := hbasepos v hv
    have hu : 0 ≤ u := mul_nonneg hε (sub_nonneg.mpr hv.2)
    have hh := inv_add_quadratic_upper ha hu
    have he : profile β ζ q ε v = a+u := rfl
    have he0 : profile β ζ q 0 v = a := by simp [profile,a]
    rw [he,he0]
    calc
      μ.xi2 v*(a+u)+(a+u)⁻¹ ≤
          μ.xi2 v*(a+u)+(a⁻¹-u/a^2+u^2/a^3) := by
            simpa only [add_comm] using add_le_add_left hh (μ.xi2 v*(a+u))
      _ = (μ.xi2 v*a+a⁻¹)+ε*((μ.xi2 v-1/a^2)*(q-v))+
          ε^2*((q-v)^2/a^3) := by dsimp [u]; ring
  have hR : IntervalIntegrable
      (fun v : ℝ =>
        (μ.xi2 v*profile β ζ q 0 v+(profile β ζ q 0 v)⁻¹)+
          ε*((μ.xi2 v-1/(β*xHat ζ v)^2)*(q-v))+
          ε^2*((q-v)^2/(β*xHat ζ v)^3)) volume 0 q :=
    ((hi 0 (by norm_num)).add (hlinI.const_mul ε)).add (hquadI.const_mul (ε^2))
  have hbound := intervalIntegral.integral_mono_on hq.1.le (hi ε hε) hR hpt
  have hcontact := CSTAPContactTrialDerivative.contact_trial_first_variation μ h hq
  have hlinEq (v : ℝ) :
      (μ.xi2 v-1/(β*xHat ζ v)^2)*(q-v) =
        ((β^2*μ.xi2 v-1/(xHat ζ v)^2)*(q-v))/β^2 := by
    by_cases hx : xHat ζ v = 0
    · simp only [hx, mul_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0),
        div_zero, sub_zero]
      field_simp [h.beta_pos.ne']
    · field_simp [h.beta_pos.ne',hx]
  have hlinval : (∫ v in (0 : ℝ)..q,
      (μ.xi2 v-1/(β*xHat ζ v)^2)*(q-v)) =
        -CSStructure.potential μ β ζ q/β^2 := by
    simp_rw [hlinEq]
    rw [intervalIntegral.integral_div]
    exact congrArg (fun t : ℝ => t/β^2) hcontact
  unfold functional curvature
  rw [intervalIntegral.integral_add ((hi 0 (by norm_num)).add (hlinI.const_mul ε))
    (hquadI.const_mul (ε^2)), intervalIntegral.integral_add (hi 0 (by norm_num))
    (hlinI.const_mul ε), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hlinval] at hbound
  dsimp [profile] at hbound ⊢
  convert (div_le_div_of_nonneg_right hbound (by norm_num : 0 ≤ (2 : ℝ))) using 1
  all_goals ring

end SlowEquilibration.CSTAPGroundTrialQuadratic

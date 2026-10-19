-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LatitudeGroundTrialSource
public import SlowEquilibration.SphericalTAPCertificate

/-! The printed latitude slack is the actual strict one-step contact
potential. Its positivity comes from the source certificate, rather than
from a supplied ground-state gap or a thermodynamic conclusion. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.LatitudeGroundTrial
open MeasureTheory Set CrisantiSommers TwoAtomStationarity SphericalTAPCertificate
open SphericalParisiConditionedLatitudeCovariance
set_option maxHeartbeats 600000

theorem triangular_affine {C x s : ℝ} (hx : 0 < x) (hs : 0 ≤ s)
    (hC : 0 < C) (hend : 0 < C-x*s) :
    (∫ t in (0 : ℝ)..s, (s-t)/(C-x*t)^2)=
      (Real.log (C/(C-x*s))-x*s/C)/x^2 := by
  have hp : ∀ t ∈ uIcc 0 s, 0 < C-x*t := by
    intro t ht
    rw [uIcc_of_le hs] at ht
    nlinarith [ht.2]
  have hi : IntervalIntegrable (fun t : ℝ => (s-t)/(C-x*t)^2) volume 0 s := by
    apply ContinuousOn.intervalIntegrable
    exact (continuous_const.sub continuous_id).continuousOn.div
      ((continuous_const.sub (continuous_const.mul continuous_id)).continuousOn.pow 2)
      (fun t ht => pow_ne_zero 2 (hp t ht).ne')
  have hd : ∀ t ∈ uIcc 0 s,
      HasDerivAt (fun t : ℝ => (x*s-C)/(x^2*(C-x*t))-Real.log (C-x*t)/x^2)
        ((s-t)/(C-x*t)^2) t := by
    intro t ht
    have hn := (hp t ht).ne'
    have hl := (hasDerivAt_const t C).sub ((hasDerivAt_id t).const_mul x)
    have hq := (hasDerivAt_const t (x*s-C)).div (hl.const_mul (x^2))
      (mul_ne_zero (pow_ne_zero 2 hx.ne') hn)
    convert hq.sub ((hl.log hn).div_const (x^2)) using 1
    · ext u
      rfl
    · dsimp only [Pi.sub_apply, Pi.mul_apply, id_eq]
      field_simp [hx.ne', hn]
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi,
    Real.log_div hC.ne' hend.ne']
  simp only [mul_zero, sub_zero]
  field_simp [hx.ne',hC.ne',hend.ne']
  ring

theorem twoAtom_triangular_below {x Q s : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hQ : Q ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) Q) :
    (∫ t in (0 : ℝ)..s, (s-t)/(xHat (twoAtom x Q) t)^2)=
      (Real.log (profileConstant x Q/(profileConstant x Q-x*s))-
        x*s/profileConstant x Q)/x^2 := by
  rw [← triangular_affine hx.1 hs.1 (profileConstant_pos hx hQ)
    (profile_affine_pos hx hQ hs.2)]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hs.1] at ht
  dsimp only
  rw [xHat_twoAtom ⟨hx.1.le,hx.2.le⟩ ht.1, ite_eq_left (ht.2.trans hs.2)]
  rfl

theorem slack_eq_contact (μ : FiniteMixture) {β x Q r : ℝ}
    (h : Certificate μ β x Q) (hr : r ∈ Ioo (0 : ℝ) 1) :
    slack μ Q (markZ x Q) r=
      CSStructure.potential μ β (twoAtom x Q) (Q*r)/β^2 := by
  have hQ0 := h.overlap_range.1
  have hQ1 := h.overlap_range.2
  have hx0 := h.weight_range.1
  have hx1 := h.weight_range.2
  have hy := markY_pos h.beta_pos h.overlap_range
  have hz : 0 < markZ x Q := div_pos (mul_pos hx0 hQ0) (sub_pos.mpr hQ1)
  have hC := profileConstant_pos h.weight_range h.overlap_range
  have hQr : Q*r ∈ Icc (0 : ℝ) Q := by constructor <;> nlinarith [hr.1,hr.2]
  have hb := profile_affine_pos h.weight_range h.overlap_range hQr.2
  have hD : 0 < D (markZ x Q) r := by
    have hr1 : 0 < 1-r := sub_pos.mpr hr.2
    unfold D
    positivity
  have hCQ : profileConstant x Q-x*Q=1-Q := profile_at_Q x Q
  have hCr : profileConstant x Q-x*(Q*r)=(1-Q)*D (markZ x Q) r := by
    unfold profileConstant D markZ
    field_simp [(sub_pos.mpr hQ1).ne']
    ring
  have hlogs : Real.log (profileConstant x Q/(profileConstant x Q-x*Q))-
      Real.log (profileConstant x Q/(profileConstant x Q-x*(Q*r)))=
      Real.log (D (markZ x Q) r) := by
    rw [hCQ,Real.log_div hC.ne' (sub_pos.mpr hQ1).ne',
      Real.log_div hC.ne' hb.ne',hCr,
      Real.log_mul (sub_pos.mpr hQ1).ne' hD.ne']
    ring
  have hVQ := h.contact_value
  unfold CSStructure.potential firstVariation at hVQ
  rw [twoAtom_triangular_below h.weight_range h.overlap_range ⟨hQ0.le,le_rfl⟩] at hVQ
  have he : CSStructure.potential μ β (twoAtom x Q) (Q*r)=
      β^2*(μ.xi Q-μ.xi (Q*r))-
        (Real.log (D (markZ x Q) r)-x*Q*(1-r)/profileConstant x Q)/x^2 := by
    unfold CSStructure.potential firstVariation
    rw [twoAtom_triangular_below h.weight_range h.overlap_range hQr]
    have hle := hlogs
    field_simp [hx0.ne'] at hVQ hle ⊢
    nlinarith [hVQ,hle]
  rw [he]
  have hscale := markY_sq_from_contact μ h.beta_pos h.weight_range h.overlap_range
    h.contact_value h.contact_derivative
  have hA : gradientVariance μ Q=(markY β Q)^2/(1+markZ x Q) := by
    have hz1 : 1+markZ x Q ≠ 0 := ne_of_gt (by linarith)
    apply (eq_div_iff hz1).mpr
    change Q*μ.xi1 (Q*1)*(1+markZ x Q)=(markY β Q)^2
    simpa only [mul_one,markA,mul_comm] using hscale.symm
  unfold slack centerCovariance
  rw [hA]
  unfold markY markZ profileConstant
  field_simp [h.beta_pos.ne',hx0.ne',hQ0.ne',(sub_pos.mpr hQ1).ne',hC.ne']

theorem slack_positive (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    0 < slack μ Q (markZ x Q) r := by
  rw [slack_eq_contact μ h hr]
  have hQr : Q*r ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact mul_pos h.overlap_range.1 hr.1
    · nlinarith [h.overlap_range.1,h.overlap_range.2,hr.1,hr.2]
  have hne : Q*r ≠ Q := by nlinarith [h.overlap_range.1,hr.2]
  exact div_pos (h.positive_off_contact (Q*r) hQr hne) (sq_pos_of_pos h.beta_pos)

end SlowEquilibration.LatitudeGroundTrial

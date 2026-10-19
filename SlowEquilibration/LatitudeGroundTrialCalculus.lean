-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib

/-! Literal one-step zero-temperature spherical trial calculus. The
degree-one term is included in the defining functional. All integral
evaluations below use ordinary FTC, including the actual reciprocal profile. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.LatitudeGroundTrial
open MeasureTheory Set
set_option maxHeartbeats 500000

def profile (L α s t : ℝ) : ℝ := L-α*max (t-s) 0

def functional (χ₁ χ₂ : ℝ → ℝ) (L α s : ℝ) : ℝ :=
  (χ₁ 0*L + (∫ t in (0 : ℝ)..1, χ₂ t*profile L α s t) +
    (∫ t in (0 : ℝ)..1, (profile L α s t)⁻¹))/2

theorem profile_continuous (L α s : ℝ) : Continuous (profile L α s) := by
  unfold profile
  fun_prop

theorem profile_of_le {L α s t : ℝ} (ht : t ≤ s) : profile L α s t=L := by
  simp [profile, max_eq_right (sub_nonpos.mpr ht)]

theorem profile_of_ge {L α s t : ℝ} (ht : s ≤ t) :
    profile L α s t=L-α*(t-s) := by
  simp [profile, max_eq_left (sub_nonneg.mpr ht)]

theorem profile_lower {L α s t : ℝ} (hα : 0 ≤ α) (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) : L-α*(1-s) ≤ profile L α s t := by
  have hm : max (t-s) 0 ≤ 1-s := max_le (by linarith [ht.2]) (by linarith [hs.2])
  have hh := mul_le_mul_of_nonneg_left hm hα
  unfold profile
  linarith

theorem energy_integral (χ χ₁ χ₂ : ℝ → ℝ)
    (hχ : ∀ t, HasDerivAt χ (χ₁ t) t)
    (hχ₁ : ∀ t, HasDerivAt χ₁ (χ₂ t) t)
    (hχ₂ : Continuous χ₂) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (L α : ℝ) :
    χ₁ 0*L+(∫ t in (0 : ℝ)..1, χ₂ t*profile L α s t)=
      χ₁ 1*(L-α*(1-s))+α*(χ 1-χ s) := by
  have hwhole : Continuous (fun t => χ₂ t*profile L α s t) :=
    hχ₂.mul (profile_continuous L α s)
  have hleft : (∫ t in (0 : ℝ)..s, χ₂ t*profile L α s t)=(χ₁ s-χ₁ 0)*L := by
    calc
      _ = ∫ t in (0 : ℝ)..s, χ₂ t*L := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hs.1] at ht
        dsimp only
        rw [profile_of_le ht.2]
      _ = _ := by
        have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t (_ : t ∈ uIcc 0 s) => (hχ₁ t).mul_const L)
          ((hχ₂.mul (continuous_const : Continuous (fun _ : ℝ => L))).intervalIntegrable 0 s)
        simpa only [sub_mul] using he
  let F : ℝ → ℝ := fun t => χ₁ t*(L-α*(t-s))+α*χ t
  have hF : ∀ t, HasDerivAt F (χ₂ t*(L-α*(t-s))) t := by
    intro t
    have ha := (hasDerivAt_const t L).sub
      (((hasDerivAt_id t).sub_const s).const_mul α)
    convert ((hχ₁ t).mul ha).add ((hχ t).const_mul α) using 1
    · ext u
      rfl
    · dsimp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, id_eq]
      ring
  have hright : (∫ t in s..1, χ₂ t*profile L α s t)=F 1-F s := by
    calc
      _ = ∫ t in s..1, χ₂ t*(L-α*(t-s)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hs.2] at ht
        dsimp only
        rw [profile_of_ge ht.1]
      _ = _ := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hF t)
        ((hχ₂.mul (continuous_const.sub (continuous_const.mul (continuous_id.sub continuous_const)))).intervalIntegrable s 1)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hwhole.intervalIntegrable 0 s) (hwhole.intervalIntegrable s 1), hleft, hright]
  dsimp [F]
  ring

theorem inverse_integral {L α s : ℝ} (hα : 0 < α) (hs : s ∈ Icc (0 : ℝ) 1)
    (hb : 0 < L-α*(1-s)) :
    (∫ t in (0 : ℝ)..1, (profile L α s t)⁻¹)=
      s/L+Real.log (L/(L-α*(1-s)))/α := by
  have hL : 0 < L := by nlinarith [mul_nonneg hα.le (sub_nonneg.mpr hs.2)]
  have hp : ∀ t ∈ Icc (0 : ℝ) 1, 0 < profile L α s t :=
    fun t ht => hb.trans_le (profile_lower hα.le hs ht)
  have hi : ∀ a b, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 →
      IntervalIntegrable (fun t => (profile L α s t)⁻¹) volume a b := by
    intro a b ha hb'
    apply ContinuousOn.intervalIntegrable
    apply (profile_continuous L α s).continuousOn.inv₀
    intro t ht
    exact (hp t ⟨(le_min ha.1 hb'.1).trans ht.1, ht.2.trans (max_le ha.2 hb'.2)⟩).ne'
  have hleft : (∫ t in (0 : ℝ)..s, (profile L α s t)⁻¹)=s/L := by
    calc
      _ = ∫ _t in (0 : ℝ)..s, L⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hs.1] at ht
        dsimp only
        rw [profile_of_le ht.2]
      _ = _ := by simp [div_eq_mul_inv]
  let F : ℝ → ℝ := fun t => -Real.log (L-α*(t-s))/α
  have haff : ∀ t ∈ uIcc s 1, 0 < L-α*(t-s) := by
    intro t ht
    rw [uIcc_of_le hs.2] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨hs.1.trans ht.1, ht.2⟩
    simpa only [profile_of_ge ht.1] using hp t ht'
  have hF : ∀ t ∈ uIcc s 1, HasDerivAt F ((L-α*(t-s))⁻¹) t := by
    intro t ht
    have ha := (hasDerivAt_const t L).sub
      (((hasDerivAt_id t).sub_const s).const_mul α)
    have hh := (ha.log (haff t ht).ne').neg.div_const α
    convert hh using 1
    · rfl
    · dsimp only [Pi.sub_apply, Pi.neg_apply, id_eq]
      field_simp [hα.ne']
      ring
  have hright : (∫ t in s..1, (profile L α s t)⁻¹)=F 1-F s := by
    calc
      _ = ∫ t in s..1, (L-α*(t-s))⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hs.2] at ht
        dsimp only
        rw [profile_of_ge ht.1]
      _ = _ := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
        ((continuous_const.sub (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn.inv₀
          (fun t ht => (haff t ht).ne')).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hi 0 s ⟨le_rfl, by norm_num⟩ hs) (hi s 1 hs ⟨by norm_num, le_rfl⟩), hleft, hright]
  dsimp [F]
  simp only [sub_self, mul_zero, sub_zero]
  rw [Real.log_div hL.ne' hb.ne']
  ring

theorem functional_eq (χ χ₁ χ₂ : ℝ → ℝ)
    (hχ : ∀ t, HasDerivAt χ (χ₁ t) t)
    (hχ₁ : ∀ t, HasDerivAt χ₁ (χ₂ t) t)
    (hχ₂ : Continuous χ₂) {L α s : ℝ} (hα : 0 < α)
    (hs : s ∈ Icc (0 : ℝ) 1) (hb : 0 < L-α*(1-s)) :
    functional χ₁ χ₂ L α s=
      (χ₁ 1*(L-α*(1-s))+α*(χ 1-χ s)+s/L+
        Real.log (L/(L-α*(1-s)))/α)/2 := by
  unfold functional
  rw [energy_integral χ χ₁ χ₂ hχ hχ₁ hχ₂ hs L α, inverse_integral hα hs hb]
  ring

end SlowEquilibration.LatitudeGroundTrial

module
public import FourPapersCommon.MixtureConvexity

@[expose] public section

/-! Actual strict and quantitative tangent control, including degenerate xi''(0). -/
noncomputable section
open Set
namespace FourPapersCommon.AdmissibleEvenMixture
set_option maxHeartbeats 600000

theorem tangentRemainder_pos (ξ : AdmissibleEvenMixture) {r q : ℝ}
    (hr : r ∈ Icc (-1 : ℝ) 1) (hq : q ∈ Icc (-1 : ℝ) 1) (hrq : r ≠ q) :
    0 < ξ.tangentRemainder r q := by
  rcases lt_or_gt_of_ne hrq with hh | hh
  · have hs := ξ.strictConvexOn_value.slope_lt_of_hasDerivAt hr hq hh (ξ.hasDerivAt_value_unit hq)
    rw [slope_def_field] at hs
    have hp := (div_lt_iff₀ (sub_pos.mpr hh)).mp hs
    unfold tangentRemainder
    nlinarith
  · have hs := ξ.strictConvexOn_value.lt_slope_of_hasDerivAt hq hr hh (ξ.hasDerivAt_value_unit hq)
    rw [slope_def_field] at hs
    have hp := (lt_div_iff₀ (sub_pos.mpr hh)).mp hs
    unfold tangentRemainder
    nlinarith

theorem first_lipschitz_unit (ξ : AdmissibleEvenMixture) {r q : ℝ}
    (hr : r ∈ Icc (-1 : ℝ) 1) (hq : q ∈ Icc (-1 : ℝ) 1) :
    |ξ.first r - ξ.first q| ≤ ξ.second 1 * |r - q| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := ξ.first) (f' := ξ.second)
    (fun x hx => (ξ.hasDerivAt_first_unit hx).hasDerivWithinAt)
    (fun x hx => by simpa only [Real.norm_eq_abs] using ξ.abs_second_le_at_one (abs_le.mpr hx))
    (convex_Icc (-1 : ℝ) 1) hq hr
  simpa only [Real.norm_eq_abs] using hh

theorem tangentRemainder_quadratic_upper (ξ : AdmissibleEvenMixture) {r q : ℝ}
    (hr : r ∈ Icc (-1 : ℝ) 1) (hq : q ∈ Icc (-1 : ℝ) 1) :
    ξ.tangentRemainder r q ≤ ξ.second 1 * (r - q) ^ 2 := by
  have hsub : uIcc q r ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    rcases mem_uIcc.mp hx with hh | hh
    · exact ⟨hq.1.trans hh.1, hh.2.trans hr.2⟩
    · exact ⟨hr.1.trans hh.1, hh.2.trans hq.2⟩
  have hd (x : ℝ) (hx : x ∈ uIcc q r) :
      HasDerivAt (fun x => ξ.tangentRemainder x q) (ξ.first x - ξ.first q) x := by
    convert (ξ.hasDerivAt_value_unit (hsub hx)).sub
      ((hasDerivAt_id x).sub_const q |>.const_mul (ξ.first q)) |>.sub_const (ξ.value q) using 1
    · funext y
      simp only [tangentRemainder, id_eq, Pi.sub_apply]
      ring
    · simp
  have hb (x : ℝ) (hx : x ∈ uIcc q r) :
      ‖ξ.first x - ξ.first q‖ ≤ ξ.second 1 * |r - q| := by
    rw [Real.norm_eq_abs]
    exact (ξ.first_lipschitz_unit (hsub hx) hq).trans
      (mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc hx) (ξ.second_nonneg 1))
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x => ξ.tangentRemainder x q) (f' := fun x => ξ.first x - ξ.first q)
    (fun x hx => (hd x hx).hasDerivWithinAt) hb (convex_uIcc q r)
    (left_mem_uIcc) (right_mem_uIcc)
  simp only [tangentRemainder, sub_self, mul_zero, sub_zero, Real.norm_eq_abs] at hh
  calc
    _ ≤ |ξ.value r - ξ.value q - ξ.first q * (r - q)| := le_abs_self _
    _ ≤ ξ.second 1 * (r - q) ^ 2 := by
      rw [mul_assoc, ← pow_two, sq_abs] at hh
      exact hh

theorem tangentRemainder_uniform_away (ξ : AdmissibleEvenMixture) {η : ℝ} (hη : 0 < η) :
    ∃ c > (0 : ℝ), ∀ r ∈ Icc (-1 : ℝ) 1, ∀ q ∈ Icc (-1 : ℝ) 1,
      η ≤ |r - q| → c ≤ ξ.tangentRemainder r q := by
  let S : Set (ℝ × ℝ) := (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ∩ {p | η ≤ |p.1 - p.2|}
  have hS : IsCompact S := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_const (continuous_fst.sub continuous_snd).abs)
  have hc : ContinuousOn (fun p : ℝ × ℝ => ξ.tangentRemainder p.1 p.2) S := by
    have hfst : MapsTo Prod.fst S (Icc (-1 : ℝ) 1) := fun _ hp => hp.1.1
    have hsnd : MapsTo Prod.snd S (Icc (-1 : ℝ) 1) := fun _ hp => hp.1.2
    exact ((ξ.continuousOn_value.comp continuous_fst.continuousOn hfst).sub
      (ξ.continuousOn_value.comp continuous_snd.continuousOn hsnd)).sub
      ((ξ.continuousOn_first.comp continuous_snd.continuousOn hsnd).mul
        (continuous_fst.sub continuous_snd).continuousOn)
  obtain ⟨c, hc0, Hc⟩ := hS.exists_forall_le' hc (a := 0) (by
    intro p hp
    exact ξ.tangentRemainder_pos hp.1.1 hp.1.2 (by
      intro he
      have hz : |p.1 - p.2| = 0 := by simp [he]
      have hh : η ≤ |p.1 - p.2| := hp.2
      rw [hz] at hh
      exact (not_le.mpr hη) hh))
  exact ⟨c, hc0, fun r hr q hq haway => Hc (r, q) ⟨⟨hr, hq⟩, haway⟩⟩

end FourPapersCommon.AdmissibleEvenMixture

-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalOnePointRadialCurvature
public import SlowEquilibration.SemicircleInsidePotential
public import SlowEquilibration.SemicircleWholeLine

/-! A global quadratic supporting bound for the literal semicircle logarithmic
potential. The bound includes the spectral support and the negative exterior. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SemicirclePotential
open Set OAI.CriticalSK SemicircleWholeLine
set_option maxHeartbeats 300000

private theorem concave_tangent_bound {f : ℝ → ℝ} {D : Set ℝ} {m v : ℝ}
    (hc : ConcaveOn ℝ D f) (hm : m ∈ D) (hd : HasDerivAt f v m) :
    ∀ t ∈ D, f t ≤ f m+v*(t-m) := by
  intro t ht
  rcases lt_trichotomy t m with htm|rfl|hmt
  · have hh := hc.le_slope_of_hasDerivAt ht hm htm hd
    simp only [slope_def_field] at hh
    have hmul := (le_div_iff₀ (sub_pos.mpr htm)).mp hh
    linarith
  · simp
  · have hh := hc.slope_le_of_hasDerivAt hm ht hmt hd
    simp only [slope_def_field] at hh
    have hmul := (div_le_iff₀ (sub_pos.mpr hmt)).mp hh
    linarith

theorem potential_positive_exterior_tangent {m : ℝ} (hm : 2 < m) :
    ∀ t ∈ Ioi (2 : ℝ), potential t ≤ potential m+resolvent m*(t-m) := by
  have hc : ConcaveOn ℝ (Ioi (2 : ℝ)) potential := by
    simpa using SphericalMarkedWindows.source_semicircle_radial_concave (b := 1)
      (by norm_num : (0 : ℝ) < 1)
  exact concave_tangent_bound hc hm (potential_hasDerivAt hm)

theorem resolvent_sub_half_nonpos {m : ℝ} (hm : 2 < m) :
    resolvent m-m/2 ≤ 0 := by
  rw [resolvent_eq_semicircleResolvent hm]
  unfold semicircleResolvent
  nlinarith [Real.sqrt_nonneg ((m-2)*(4+(m-2)))]

/-- The literal semicircle potential admits the source global quadratic
support at every positive exterior contact, on the entire real line. -/
theorem potential_global_quadratic_tangent {m : ℝ} (hm : 2 < m) (t : ℝ) :
    potential t ≤ potential m+resolvent m*(t-m)+(t-m)^2/4 := by
  let F : ℝ → ℝ := fun v => potential v-v^2/4
  let L : ℝ → ℝ := fun v => F m+(resolvent m-m/2)*(v-m)
  have hs : resolvent m-m/2 ≤ 0 := resolvent_sub_half_nonpos hm
  have hExt : ∀ v ∈ Ioi (2 : ℝ), F v ≤ L v := by
    intro v hv
    have hh := potential_positive_exterior_tangent hm v hv
    dsimp [F,L]
    nlinarith [sq_nonneg (v-m)]
  have hF : Continuous F := potential_continuous.sub (continuous_id.pow 2 |>.div_const 4)
  have hL : Continuous L := by fun_prop
  have hEdge : F 2 ≤ L 2 := by
    apply le_on_closure hExt hF.continuousOn hL.continuousOn
    rw [closure_Ioi]
    exact le_rfl
  have hInside : ∀ v, |v| ≤ 2 → F v ≤ L v := by
    intro v hv
    have hv2 : v ≤ 2 := (abs_le.mp hv).2
    have hf : F v = F 2 := by
      dsimp [F]
      rw [potential_eq_inside v hv,potential_eq_inside 2 (by norm_num)]
      ring
    rw [hf]
    apply hEdge.trans
    dsimp [L]
    nlinarith [mul_nonneg (neg_nonneg.mpr hs) (sub_nonneg.mpr hv2)]
  have hGlobal : F t ≤ L t := by
    by_cases hi : |t| ≤ 2
    · exact hInside t hi
    have ha : 2 < |t| := lt_of_not_ge hi
    have hp := hExt |t| ha
    have he : F t = F |t| := by
      dsimp [F]
      rw [sq_abs]
      by_cases ht : 0 ≤ t
      · rw [abs_of_nonneg ht]
      · rw [abs_of_neg (lt_of_not_ge ht),potential_even]
    rw [he]
    apply hp.trans
    dsimp [L]
    nlinarith [mul_nonneg (neg_nonneg.mpr hs) (sub_nonneg.mpr (le_abs_self t))]
  dsimp [F,L] at hGlobal
  nlinarith

end SlowEquilibration.SemicirclePotential

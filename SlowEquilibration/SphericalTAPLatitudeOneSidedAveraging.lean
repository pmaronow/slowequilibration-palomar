-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeLaplace
public import Mathlib.Analysis.Calculus.Taylor

@[expose] public section

/-! A deterministic core of manuscript Lemma 12.19. A parabolic Taylor
minorant of the true latitude exponent gives a lower integral bound on
one half of a microscopic interval. The chosen half depends only on the
sign of the linear coefficient. This incurs a fixed factor two, which the
lemma's unspecified constant absorbs. The physical second-derivative
bound and the spherical coarea specialization are separate obligations. -/

namespace SlowEquilibration.SphericalTAPLatitudeOneSidedAveraging
noncomputable section
open MeasureTheory Set

/-- Taylor's theorem turns a uniform second-derivative lower bound into the
parabolic minorant used in the one-sided integral estimate. -/
theorem parabolic_minorant_of_second_derivative (J : ℝ → ℝ)
    (hJ : ContDiff ℝ 2 J) (center width curvature : ℝ)
    (hwidth : 0 ≤ width)
    (hsecond : ∀ y ∈ Icc (center-width) (center+width),
      -curvature ≤ iteratedDeriv 2 J y) :
    ∀ a ∈ Icc (center-width) (center+width),
      J center+(deriv J center)*(a-center)-curvature*(a-center)^2/2 ≤ J a := by
  intro a ha
  by_cases hac : a = center
  · subst a
    norm_num
  have hca : center ≠ a := Ne.symm hac
  obtain ⟨y,hy,htaylor⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hca hJ.contDiffOn
  have hpoly : taylorWithinEval J 1 (uIcc center a) center a =
      J center+(deriv J center)*(a-center) := by
    rw [show (1:ℕ)=0+1 by norm_num, taylorWithinEval_succ]
    simp only [Nat.zero_add, taylor_within_zero_eval, iteratedDerivWithin_one]
    norm_num
    rw [(hJ.differentiable (by norm_num) center).derivWithin
      ((uniqueDiffOn_uIcc hca) center left_mem_uIcc)]
    ring
  have hybig : y ∈ Icc (center-width) (center+width) := by
    have hcenter : center ∈ Icc (center-width) (center+width) := by constructor <;> linarith
    have hycc : y ∈ uIcc center a := Ioo_subset_Icc_self hy
    grind [Set.mem_uIcc]
  have hcurv := hsecond y hybig
  have hsq : 0 ≤ (a-center)^2 := sq_nonneg _
  have hbound := mul_le_mul_of_nonneg_right hcurv hsq
  rw [hpoly] at htaylor
  norm_num at htaylor
  nlinarith

/-- A local parabolic Taylor minorant controls the whole exponential
integral without restricting the sign or size of the linear term. -/
theorem exponential_latitude_integral_lower (J : ℝ → ℝ) (hJ : Continuous J)
    (center width curvature slope : ℝ) (hwidth : 0 < width)
    (hcurvature : 0 ≤ curvature)
    (hminorant : ∀ a ∈ Icc (center-width) (center+width),
      J center+slope*(a-center)-curvature*(a-center)^2/2 ≤ J a) :
    width*Real.exp (J center-curvature*width^2/2) ≤
      ∫ a in (center-width)..(center+width), Real.exp (J a) := by
  let E : ℝ → ℝ := fun a => Real.exp (J a)
  have hE : Continuous E := Real.continuous_exp.comp hJ
  have hleft : center-width ≤ center := by linarith
  have hright : center ≤ center+width := by linarith
  by_cases hslope : 0 ≤ slope
  · have hpoint : ∀ a ∈ Icc center (center+width),
        Real.exp (J center-curvature*width^2/2) ≤ E a := by
      intro a ha
      have ha0 : 0 ≤ a-center := by linarith [ha.1]
      have haw : a-center ≤ width := by linarith [ha.2]
      have hsq : (a-center)^2 ≤ width^2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr haw) (add_nonneg hwidth.le ha0)]
      apply Real.exp_le_exp.mpr
      have hlocal : a ∈ Icc (center-width) (center+width) := ⟨by linarith [ha.1],ha.2⟩
      have ht := hminorant a hlocal
      nlinarith [mul_nonneg hslope ha0,
        mul_nonneg hcurvature (sub_nonneg.mpr hsq)]
    have hrightBound : width*Real.exp (J center-curvature*width^2/2) ≤
        ∫ a in center..(center+width), E a := by
      calc
        _ = ∫ a in center..(center+width),
            Real.exp (J center-curvature*width^2/2) := by
              simp only [intervalIntegral.integral_const,smul_eq_mul]
              ring
        _ ≤ _ := intervalIntegral.integral_mono_on hright
          (continuous_const.intervalIntegrable _ _) (hE.intervalIntegrable _ _) hpoint
    have hleftNonneg : 0 ≤ ∫ a in (center-width)..center, E a :=
      intervalIntegral.integral_nonneg hleft (fun _ _ => (Real.exp_pos _).le)
    calc
      _ ≤ ∫ a in center..(center+width), E a := hrightBound
      _ ≤ (∫ a in (center-width)..center, E a)+
          (∫ a in center..(center+width), E a) := le_add_of_nonneg_left hleftNonneg
      _ = _ := intervalIntegral.integral_add_adjacent_intervals
        (hE.intervalIntegrable _ _) (hE.intervalIntegrable _ _)
  · have hslope' : slope ≤ 0 := le_of_not_ge hslope
    have hpoint : ∀ a ∈ Icc (center-width) center,
        Real.exp (J center-curvature*width^2/2) ≤ E a := by
      intro a ha
      have ha0 : a-center ≤ 0 := by linarith [ha.2]
      have haw : -width ≤ a-center := by linarith [ha.1]
      have hsq : (a-center)^2 ≤ width^2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith : width-(center-a) ≥ 0))
          (add_nonneg hwidth.le (by linarith : 0 ≤ center-a))]
      apply Real.exp_le_exp.mpr
      have hlocal : a ∈ Icc (center-width) (center+width) := ⟨ha.1,by linarith [ha.2]⟩
      have ht := hminorant a hlocal
      nlinarith [mul_nonneg_of_nonpos_of_nonpos hslope' ha0,
        mul_nonneg hcurvature (sub_nonneg.mpr hsq)]
    have hleftBound : width*Real.exp (J center-curvature*width^2/2) ≤
        ∫ a in (center-width)..center, E a := by
      calc
        _ = ∫ a in (center-width)..center,
            Real.exp (J center-curvature*width^2/2) := by
              simp only [intervalIntegral.integral_const,smul_eq_mul]
              ring
        _ ≤ _ := intervalIntegral.integral_mono_on hleft
          (continuous_const.intervalIntegrable _ _) (hE.intervalIntegrable _ _) hpoint
    have hrightNonneg : 0 ≤ ∫ a in center..(center+width), E a :=
      intervalIntegral.integral_nonneg hright (fun _ _ => (Real.exp_pos _).le)
    calc
      _ ≤ ∫ a in (center-width)..center, E a := hleftBound
      _ ≤ (∫ a in (center-width)..center, E a)+
          (∫ a in center..(center+width), E a) := le_add_of_nonneg_right hrightNonneg
      _ = _ := intervalIntegral.integral_add_adjacent_intervals
        (hE.intervalIntegrable _ _) (hE.intervalIntegrable _ _)

/-- A direct deterministic curvature-to-partition form of the microscopic
latitude estimate. The slope at the central latitude is unrestricted. -/
theorem exponential_latitude_integral_lower_of_second_derivative
    (J : ℝ → ℝ) (hJ : ContDiff ℝ 2 J)
    (center width curvature : ℝ) (hwidth : 0 < width)
    (hcurvature : 0 ≤ curvature)
    (hsecond : ∀ y ∈ Icc (center-width) (center+width),
      -curvature ≤ iteratedDeriv 2 J y) :
    width*Real.exp (J center-curvature*width^2/2) ≤
      ∫ a in (center-width)..(center+width), Real.exp (J a) :=
  exponential_latitude_integral_lower J hJ.continuous center width curvature
    (deriv J center) hwidth hcurvature
    (parabolic_minorant_of_second_derivative J hJ center width curvature hwidth.le hsecond)

end
end SlowEquilibration.SphericalTAPLatitudeOneSidedAveraging

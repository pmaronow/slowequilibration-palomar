-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPLatitudeOneSidedAveraging

@[expose] public section

/-! The symmetric microscopic latitude step of manuscript Lemma 12.19.
The proof pairs latitudes equidistant from the central slice. The pair
cancels an arbitrarily large first derivative, so only a second-derivative
lower bound is required. The physical entropy/field curvature and coarea
specialization are kept separate. -/

namespace SlowEquilibration.SphericalTAPSymmetricLatitudeIntegral
noncomputable section
open MeasureTheory Set

set_option autoImplicit false
set_option maxHeartbeats 500000

/-- Pairing the two sides of a Taylor parabola removes its linear term. -/
theorem exponential_symmetric_pair_lower (J : ℝ → ℝ)
    (center width curvature slope : ℝ)
    (hwidth : 0 ≤ width) (hcurvature : 0 ≤ curvature)
    (hminorant : ∀ a ∈ Icc (center-width) (center+width),
      J center+slope*(a-center)-curvature*(a-center)^2/2 ≤ J a)
    (t : ℝ) (ht : t ∈ Icc 0 width) :
    2*Real.exp (J center-curvature*width^2/2) ≤
      Real.exp (J (center-t))+Real.exp (J (center+t)) := by
  have htleft : center-t ∈ Icc (center-width) (center+width) := by
    constructor <;> linarith [ht.1,ht.2]
  have htright : center+t ∈ Icc (center-width) (center+width) := by
    constructor <;> linarith [ht.1,ht.2]
  have hsq : t^2 ≤ width^2 := by nlinarith [ht.1,ht.2]
  let A : ℝ := J center-curvature*t^2/2
  let B : ℝ := J center-curvature*width^2/2
  let z : ℝ := slope*t
  have hB : B ≤ A := by dsimp [A,B]; nlinarith
  have hsym : 2 ≤ Real.exp z+Real.exp (-z) := by
    linarith [Real.add_one_le_exp z,Real.add_one_le_exp (-z)]
  have hfactor : Real.exp (A-z)+Real.exp (A+z) =
      Real.exp A*(Real.exp (-z)+Real.exp z) := by
    rw [show A-z=A+(-z) by ring,Real.exp_add,Real.exp_add]
    ring
  have hleft : A-z ≤ J (center-t) := by
    have h := hminorant (center-t) htleft
    dsimp [A,z]
    convert h using 1
    ring
  have hright : A+z ≤ J (center+t) := by
    have h := hminorant (center+t) htright
    dsimp [A,z]
    convert h using 1
    ring
  calc
    2*Real.exp B ≤ 2*Real.exp A := by gcongr
    _ ≤ Real.exp (A-z)+Real.exp (A+z) := by
      rw [hfactor]
      nlinarith [mul_nonneg (Real.exp_pos A).le
        (show 0 ≤ Real.exp (-z)+Real.exp z-2 by linarith [hsym])]
    _ ≤ Real.exp (J (center-t))+Real.exp (J (center+t)) :=
      add_le_add (Real.exp_le_exp.mpr hleft) (Real.exp_le_exp.mpr hright)

/-- A symmetric interval has the full factor `2*width`, independently of
the size and sign of the first latitude derivative. -/
theorem exponential_symmetric_integral_lower
    (J : ℝ → ℝ)
    (center width curvature slope : ℝ)
    (hwidth : 0 < width) (hcurvature : 0 ≤ curvature)
    (hJ : ContinuousOn J (Icc (center-width) (center+width)))
    (hminorant : ∀ a ∈ Icc (center-width) (center+width),
      J center+slope*(a-center)-curvature*(a-center)^2/2 ≤ J a) :
    2*width*Real.exp (J center-curvature*width^2/2) ≤
      ∫ a in (center-width)..(center+width), Real.exp (J a) := by
  let E : ℝ → ℝ := fun a => Real.exp (J a)
  have hE : ContinuousOn E (Icc (center-width) (center+width)) :=
    Real.continuous_exp.continuousOn.comp hJ (fun _ _ => Set.mem_univ _)
  have hleftArg : Set.MapsTo (fun t : ℝ => center-t) (Icc 0 width)
      (Icc (center-width) (center+width)) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hrightArg : Set.MapsTo (fun t : ℝ => center+t) (Icc 0 width)
      (Icc (center-width) (center+width)) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hleftInt : IntervalIntegrable (fun t : ℝ => E (center-t)) volume 0 width :=
    (hE.comp (continuous_const.sub continuous_id).continuousOn hleftArg).intervalIntegrable_of_Icc
      hwidth.le
  have hrightInt : IntervalIntegrable (fun t : ℝ => E (center+t)) volume 0 width :=
    (hE.comp (continuous_const.add continuous_id).continuousOn hrightArg).intervalIntegrable_of_Icc
      hwidth.le
  have hEInt : IntervalIntegrable E volume (center-width) (center+width) :=
    hE.intervalIntegrable_of_Icc (by linarith)
  have hleftEInt : IntervalIntegrable E volume (center-width) center :=
    (hE.mono (by
      intro x hx
      exact ⟨hx.1,by linarith [hx.2]⟩)).intervalIntegrable_of_Icc (by linarith)
  have hrightEInt : IntervalIntegrable E volume center (center+width) :=
    (hE.mono (by
      intro x hx
      exact ⟨by linarith [hx.1],hx.2⟩)).intervalIntegrable_of_Icc (by linarith)
  have hpair : ∀ t ∈ Icc 0 width,
      2*Real.exp (J center-curvature*width^2/2) ≤ E (center-t)+E (center+t) :=
    exponential_symmetric_pair_lower J center width curvature slope
      hwidth.le hcurvature hminorant
  have hmono :
      ∫ t in (0:ℝ)..width, 2*Real.exp (J center-curvature*width^2/2) ≤
        ∫ t in (0:ℝ)..width, E (center-t)+E (center+t) := by
    apply intervalIntegral.integral_mono_on hwidth.le
      (continuous_const.intervalIntegrable _ _)
      (hleftInt.add hrightInt)
    exact hpair
  have hsplit :
      (∫ t in (0:ℝ)..width, E (center-t)+E (center+t)) =
      ∫ a in (center-width)..(center+width), E a := by
    rw [intervalIntegral.integral_add hleftInt hrightInt,
      intervalIntegral.integral_comp_sub_left,intervalIntegral.integral_comp_add_left]
    simp only [sub_zero,add_zero]
    exact intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      hleftEInt hrightEInt
  calc
    _ = ∫ t in (0:ℝ)..width,
        2*Real.exp (J center-curvature*width^2/2) := by
          simp only [intervalIntegral.integral_const,smul_eq_mul]
          ring
    _ ≤ _ := hmono.trans_eq hsplit

/-- Taylor's theorem supplies the minorant from a genuine second-derivative
bound, with no hypothesis on the first derivative. -/
theorem exponential_symmetric_integral_lower_of_second_derivative
    (J : ℝ → ℝ) (hJ : ContDiff ℝ 2 J)
    (center width curvature : ℝ)
    (hwidth : 0 < width) (hcurvature : 0 ≤ curvature)
    (hsecond : ∀ y ∈ Icc (center-width) (center+width),
      -curvature ≤ iteratedDeriv 2 J y) :
    2*width*Real.exp (J center-curvature*width^2/2) ≤
      ∫ a in (center-width)..(center+width), Real.exp (J a) :=
  exponential_symmetric_integral_lower J center width curvature
    (deriv J center) hwidth hcurvature
    (hJ.continuous.continuousOn)
    (SlowEquilibration.SphericalTAPLatitudeOneSidedAveraging.parabolic_minorant_of_second_derivative
      J hJ center width curvature hwidth.le hsecond)

/-- Local Taylor minorant. Unlike the globally smooth variant, this applies
to the physical latitude entropy `log (1-a²)`, which is smooth only for
latitudes strictly between the two poles. -/
theorem parabolic_minorant_of_local_second_derivative
    (J : ℝ → ℝ) (lo hi center width curvature : ℝ)
    (hJ : ContDiffOn ℝ 2 J (Ioo lo hi))
    (hwidth : 0 ≤ width)
    (hinterval : Icc (center-width) (center+width) ⊆ Ioo lo hi)
    (hsecond : ∀ y ∈ Icc (center-width) (center+width),
      -curvature ≤ iteratedDeriv 2 J y) :
    ∀ a ∈ Icc (center-width) (center+width),
      J center+(deriv J center)*(a-center)-curvature*(a-center)^2/2 ≤ J a := by
  intro a ha
  by_cases hac : a = center
  · subst a
    norm_num
  have hca : center ≠ a := Ne.symm hac
  have hcenter : center ∈ Icc (center-width) (center+width) := by
    constructor <;> linarith
  have hseg : uIcc center a ⊆ Ioo lo hi := by
    intro y hy
    apply hinterval
    have hycc : y ∈ Icc (center-width) (center+width) := by
      have : y ∈ uIcc center a := hy
      grind [Set.mem_uIcc]
    exact hycc
  obtain ⟨y,hy,htaylor⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hca (hJ.mono hseg)
  have hpoly : taylorWithinEval J 1 (uIcc center a) center a =
      J center+(deriv J center)*(a-center) := by
    rw [show (1:ℕ)=0+1 by norm_num,taylorWithinEval_succ]
    simp only [Nat.zero_add,taylor_within_zero_eval,iteratedDerivWithin_one]
    norm_num
    have hJcenter : ContDiffAt ℝ 2 J center :=
      hJ.contDiffAt (isOpen_Ioo.mem_nhds (hinterval hcenter))
    rw [(hJcenter.differentiableAt (by norm_num)).derivWithin
      ((uniqueDiffOn_uIcc hca) center left_mem_uIcc)]
    ring
  have hybig : y ∈ Icc (center-width) (center+width) := by
    have hycc : y ∈ uIcc center a := Ioo_subset_Icc_self hy
    grind [Set.mem_uIcc]
  have hcurv := hsecond y hybig
  have hsq : 0 ≤ (a-center)^2 := sq_nonneg _
  have hbound := mul_le_mul_of_nonneg_right hcurv hsq
  rw [hpoly] at htaylor
  norm_num at htaylor
  nlinarith

/-- The full symmetric integral estimate under only *local* `C²`
regularity. This is the natural analytic interface for the physical
latitude exponent. -/
theorem exponential_symmetric_integral_lower_of_local_second_derivative
    (J : ℝ → ℝ) (lo hi center width curvature : ℝ)
    (hJ : ContDiffOn ℝ 2 J (Ioo lo hi))
    (hwidth : 0 < width) (hcurvature : 0 ≤ curvature)
    (hinterval : Icc (center-width) (center+width) ⊆ Ioo lo hi)
    (hsecond : ∀ y ∈ Icc (center-width) (center+width),
      -curvature ≤ iteratedDeriv 2 J y) :
    2*width*Real.exp (J center-curvature*width^2/2) ≤
      ∫ a in (center-width)..(center+width), Real.exp (J a) := by
  apply exponential_symmetric_integral_lower J center width curvature
    (deriv J center) hwidth hcurvature
    (hJ.continuousOn.mono hinterval)
  exact parabolic_minorant_of_local_second_derivative J lo hi center width curvature
    hJ hwidth.le hinterval hsecond

/-- The pointwise symmetric latitude estimate survives integration over the
true transverse angular law. This is the analytic form needed before the
spherical coarea identity converts the shell integral into band mass. -/
theorem exponential_symmetric_shell_lower
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (J : Ω → ℝ → ℝ) (center width curvature : ℝ)
    (hwidth : 0 < width) (hcurvature : 0 ≤ curvature)
    (hJ : ∀ ω, ContDiff ℝ 2 (J ω))
    (hsecond : ∀ ω y, y ∈ Icc (center-width) (center+width) →
      -curvature ≤ iteratedDeriv 2 (J ω) y)
    (hcentral : Integrable (fun ω => Real.exp (J ω center)) ν)
    (hshell : Integrable (fun ω =>
      ∫ a in (center-width)..(center+width), Real.exp (J ω a)) ν) :
    (2*width*Real.exp (-curvature*width^2/2))*
      (∫ ω, Real.exp (J ω center) ∂ν) ≤
        ∫ ω, (∫ a in (center-width)..(center+width),
          Real.exp (J ω a)) ∂ν := by
  let c : ℝ := 2*width*Real.exp (-curvature*width^2/2)
  have hfactor (ω : Ω) :
      2*width*Real.exp (J ω center-curvature*width^2/2) =
        c*Real.exp (J ω center) := by
    dsimp [c]
    rw [show J ω center-curvature*width^2/2 =
      -curvature*width^2/2 + J ω center by ring,Real.exp_add]
    ring
  have hpoint (ω : Ω) :
      c*Real.exp (J ω center) ≤
        ∫ a in (center-width)..(center+width), Real.exp (J ω a) := by
    rw [← hfactor]
    exact exponential_symmetric_integral_lower_of_second_derivative
      (J ω) (hJ ω) center width curvature hwidth hcurvature
      (hsecond ω)
  have hbound := integral_mono_ae (hcentral.const_mul c) hshell
    (Filter.Eventually.of_forall hpoint)
  simpa only [integral_const_mul,c] using hbound

end
end SlowEquilibration.SphericalTAPSymmetricLatitudeIntegral

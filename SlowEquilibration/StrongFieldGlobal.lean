-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.StrongFieldCoercivity
public import SlowEquilibration.SemicircleInsidePotential

@[expose] public section

/-!
# The genuine whole-line strong-field critical-point exponent

The actual semicircle logarithmic integral, including its inner branch, has
exactly the two strong-field zero pairs. Compact and closed height-excluded
sets have a uniform negative gap; the latter uses proved quadratic tails.
-/

namespace SlowEquilibration.StrongFieldComplexity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set

theorem radial_lt_zero_inside {t u : ℝ} (ht : 1 < t) (hu : |u| ≤ 2) :
    radial t u < 0 := by
  rw [radial, SemicirclePotential.potential_eq_inside u hu]
  exact innerQuadraticRadial_lt_zero ht hu

theorem radial_nonpos_global {t : ℝ} (ht : 1 < t) (u : ℝ) : radial t u ≤ 0 := by
  rcases le_total |u| 2 with hu | hu
  · exact (radial_lt_zero_inside ht hu).le
  · exact radial_nonpos_of_abs_ge_two ht hu

theorem radial_eq_zero_iff_global {t : ℝ} (ht : 1 < t) (u : ℝ) :
    radial t u = 0 ↔ |u| = endpoint t := by
  by_cases hu : 2 ≤ |u|
  · exact radial_eq_zero_iff_of_abs_ge_two ht hu
  · have hu' : |u| < 2 := lt_of_not_ge hu
    constructor
    · intro hz
      have hn := radial_lt_zero_inside ht hu'.le
      linarith
    · intro he
      have hout := endpoint_gt_two ht
      rw [← he] at hout
      linarith

theorem radialEndpoint_gt_edge {a b : ℝ} (hb : 0 < b) (hab : b < a) :
    2*Real.sqrt b < radialEndpoint a b := by
  have h := endpoint_gt_two (ratio_gt_one hb hab)
  rw [← radialEndpoint_normalized hb hab] at h
  exact (lt_div_iff₀ (Real.sqrt_pos.mpr hb)).mp h

/-- The actual BCNS exponent is nonpositive at every real pair. -/
theorem exponent_nonpos_global {a b variance : ℝ} (hb : 0 < b) (hab : b < a)
    (hvariance : 0 < variance) (h k : ℝ) : exponent a b variance h k ≤ 0 := by
  have hg := radial_nonpos_global (ratio_gt_one hb hab) (k/Real.sqrt b)
  rw [radial_physical hb hab] at hg
  have htail : 0 ≤ (h-a*k/(a+b))^2/(2*variance) := by positivity
  unfold exponent
  linarith

/-- Exact two-point zero classification for the literal exponent on all ℝ². -/
theorem exponent_eq_zero_iff_global {a b variance : ℝ} (hb : 0 < b) (hab : b < a)
    (hvariance : 0 < variance) (h k : ℝ) :
    exponent a b variance h k = 0 ↔
      (h = Real.sqrt a ∧ k = radialEndpoint a b) ∨
      (h = -Real.sqrt a ∧ k = -radialEndpoint a b) := by
  by_cases hk : 2*Real.sqrt b ≤ |k|
  · exact exponent_eq_zero_iff_of_abs_ge_edge hb hab hvariance hk
  · have hk' : |k| < 2*Real.sqrt b := lt_of_not_ge hk
    have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
    have hu : |k/Real.sqrt b| < 2 := by
      rw [abs_div, abs_of_pos hs]
      exact (div_lt_iff₀ hs).mpr hk'
    have hg := radial_lt_zero_inside (ratio_gt_one hb hab) hu.le
    rw [radial_physical hb hab] at hg
    have htail : 0 ≤ (h-a*k/(a+b))^2/(2*variance) := by positivity
    have hn : exponent a b variance h k < 0 := by unfold exponent; linarith
    constructor
    · intro hz
      linarith
    · rintro (⟨_, hke⟩ | ⟨_, hke⟩)
      · have he := radialEndpoint_gt_edge hb hab
        have hep : 0 < radialEndpoint a b := (by positivity : 0 < 2*Real.sqrt b).trans he
        rw [hke, abs_of_pos hep] at hk'
        linarith
      · have he := radialEndpoint_gt_edge hb hab
        have hep : 0 < radialEndpoint a b := (by positivity : 0 < 2*Real.sqrt b).trans he
        rw [hke, abs_neg, abs_of_pos hep] at hk'
        linarith

/-- Genuine uniform compact gaps away from both endpoint heights. -/
theorem exists_uniform_exponent_gap_global {a b variance : ℝ}
    (hb : 0 < b) (hab : b < a) (hvariance : 0 < variance)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hheight : ∀ z ∈ K, |z.1| ≠ Real.sqrt a) :
    ∃ η : ℝ, 0 < η ∧ ∀ z ∈ K, exponent a b variance z.1 z.2 ≤ -η := by
  by_cases hne : K.Nonempty
  · obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne
      (exponent_continuous a b variance).continuousOn
    have hle := exponent_nonpos_global hb hab hvariance z.1 z.2
    have hstrict : exponent a b variance z.1 z.2 < 0 := by
      apply lt_of_le_of_ne hle
      intro heq
      have he := (exponent_eq_zero_iff_global hb hab hvariance z.1 z.2).mp heq
      have ha : 0 < a := hb.trans hab
      apply hheight z hz
      rcases he with he | he
      · rw [he.1, abs_of_pos (Real.sqrt_pos.mpr ha)]
      · rw [he.1, abs_neg, abs_of_pos (Real.sqrt_pos.mpr ha)]
    refine ⟨-exponent a b variance z.1 z.2/2, by linarith, ?_⟩
    intro w hw
    have hm : exponent a b variance w.1 w.2 ≤ exponent a b variance z.1 z.2 := hmax hw
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz
    exact (hne ⟨z, hz⟩).elim

/-- Quadratic tails upgrade the actual compact gap to every closed set
whose heights exclude the two limiting endpoint heights. -/
theorem exists_uniform_exponent_gap_closed {a b variance : ℝ}
    (hb : 0 < b) (hab : b < a) (hvariance : 0 < variance)
    {S : Set (ℝ × ℝ)} (hS : IsClosed S)
    (hheight : ∀ z ∈ S, |z.1| ≠ Real.sqrt a) :
    ∃ η : ℝ, 0 < η ∧ ∀ z ∈ S, exponent a b variance z.1 z.2 ≤ -η := by
  let c := precisionCoefficient (a+b) variance (a/(a+b))
  let C := coercivityConstant a b
  have hc : 0 < c := precisionCoefficient_pos (by linarith) hvariance
  have hC : 0 < C := coercivityConstant_pos a b
  let R := (C+1)/c+1
  have hR1 : 1 < R := by
    have hratio : 0 < (C+1)/c := by positivity
    dsimp [R]
    linarith
  have hR0 : 0 < R := by linarith
  have hcR : C+1 < c*R := by
    dsimp [R]
    rw [mul_add, mul_div_cancel₀ _ hc.ne']
    linarith
  have hcR2 : C+1 < c*R^2 := by
    have hm := mul_lt_mul_of_pos_left (show R < R^2 by nlinarith) hc
    exact hcR.trans hm
  let B : Set (ℝ × ℝ) := Icc (-R) R ×ˢ Icc (-R) R
  have hK : IsCompact (B ∩ S) :=
    (isCompact_Icc.prod isCompact_Icc).inter_right hS
  obtain ⟨η, hη, hgap⟩ := exists_uniform_exponent_gap_global hb hab hvariance hK
    (fun z hz => hheight z hz.2)
  refine ⟨min η 1, lt_min hη (by norm_num), ?_⟩
  intro z hz
  by_cases hB : z ∈ B
  · exact (hgap z ⟨hB,hz⟩).trans (neg_le_neg (min_le_left _ _))
  · have hnot : ¬ (|z.1| ≤ R ∧ |z.2| ≤ R) := by
      intro h
      exact hB ⟨abs_le.mp h.1,abs_le.mp h.2⟩
    have hor : R < |z.1| ∨ R < |z.2| := by simpa only [not_and_or, not_le] using hnot
    have hsq : R^2 ≤ z.1^2+z.2^2 := by
      rcases hor with h | h
      · nlinarith [sq_abs z.1, sq_nonneg z.2]
      · nlinarith [sq_abs z.2, sq_nonneg z.1]
    have hmul := mul_le_mul_of_nonneg_left hsq hc.le
    have hcoercive := exponent_le_quadratic_coercivity hb hab hvariance z.1 z.2
    change exponent a b variance z.1 z.2 ≤ C-c*(z.1^2+z.2^2) at hcoercive
    have htail : exponent a b variance z.1 z.2 ≤ -(1 : ℝ) := by linarith
    exact htail.trans (neg_le_neg (min_le_right _ _))

end
end SlowEquilibration.StrongFieldComplexity

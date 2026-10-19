-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceLiteratureGroundStateCenterBridge
public import SlowEquilibration.SourceLiteratureGroundTrialProfile
public import SlowEquilibration.CSConvexity

/-!
The uniqueness clause and radius change of variables in source `thm:th-ground`.
Uniqueness concerns the continuous profile on the physical closed interval;
values of the slope outside that interval are irrelevant. Chen–Sen supplies
attainment and the physical limit through the existing explicit interface.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceGroundProfileUniqueness

open MeasureTheory Set Filter SourceLiteratureGroundState
open SourceLiteratureGroundStateCenterBridge SourceLiteratureGroundStateRadialCoefficients
open SourceLiteratureGroundTrialProfile LiteratureSubagTAP
open scoped Topology

set_option autoImplicit false

/-- The continuous positive function represented by a Chen–Sen pair. -/
def profile (u : GroundProfile) (r : ℝ) : ℝ :=
  u.L - ∫ s in (0 : ℝ)..r, u.alpha s

private theorem mass_continuous (u : GroundProfile) :
    ContinuousOn (fun r => ∫ s in (0 : ℝ)..r, u.alpha s) (Icc 0 1) := by
  simpa only [uIcc_of_le zero_le_one] using
    intervalIntegral.continuousOn_primitive_interval' u.alpha_integrable (left_mem_uIcc)

private theorem profile_continuous (u : GroundProfile) :
    ContinuousOn (profile u) (Icc 0 1) :=
  continuousOn_const.sub (mass_continuous u)

private theorem profile_pos (u : GroundProfile) {r : ℝ} (hr : r ∈ Icc 0 1) :
    0 < profile u r := by
  have htail : 0 ≤ ∫ s in r..1, u.alpha s := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hr.2
    filter_upwards [ae_restrict_mem measurableSet_Icc, (volume.restrict (Icc r 1)).ae_ne (1 : ℝ)] with s hs hs1
    exact u.alpha_nonnegative s ⟨hr.1.trans hs.1, lt_of_le_of_ne hs.2 hs1⟩
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (u.alpha_integrable.mono_set (by rw [uIcc_of_le hr.1, uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl hr.2))
    (u.alpha_integrable.mono_set (by rw [uIcc_of_le hr.2, uIcc_of_le zero_le_one]; exact Icc_subset_Icc hr.1 le_rfl))
  unfold profile
  linarith [u.height_gt_mass]

private theorem inverse_profile_continuous (u : GroundProfile) :
    ContinuousOn (fun r => (profile u r)⁻¹) (Icc 0 1) :=
  (profile_continuous u).inv₀ (fun _ hr => (profile_pos u hr).ne')

/-- Midpoints stay in the full monotone, right-continuous profile class. -/
def midpoint (u v : GroundProfile) : GroundProfile where
  L := (u.L + v.L) / 2
  alpha := fun r => (u.alpha r + v.alpha r) / 2
  alpha_nonnegative := fun r hr => by
    exact div_nonneg (add_nonneg (u.alpha_nonnegative r hr)
      (v.alpha_nonnegative r hr)) (by norm_num)
  alpha_monotone := fun r hr s hs hrs => by
    linarith [u.alpha_monotone hr hs hrs, v.alpha_monotone hr hs hrs]
  alpha_rightContinuous := fun r hr =>
    ((u.alpha_rightContinuous r hr).add (v.alpha_rightContinuous r hr)).div_const 2
  alpha_integrable := (u.alpha_integrable.add v.alpha_integrable).div_const 2
  height_gt_mass := by
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_add u.alpha_integrable v.alpha_integrable]
    linarith [u.height_gt_mass, v.height_gt_mass]

private theorem profile_midpoint (u v : GroundProfile) {r : ℝ} (hr : r ∈ Icc 0 1) :
    profile (midpoint u v) r = (profile u r + profile v r) / 2 := by
  have hsub : uIcc (0 : ℝ) r ⊆ uIcc 0 1 := by
    rw [uIcc_of_le hr.1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hr.2
  unfold profile midpoint
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add (u.alpha_integrable.mono_set hsub)
      (v.alpha_integrable.mono_set hsub)]
  ring

/-- The Chen–Sen objective is the printed integral objective at radius one. -/
theorem groundFunctional_eq_integral (μ : FiniteMixture) (u : GroundProfile) :
    groundFunctional μ u =
      ((∫ r in (0 : ℝ)..1, μ.xi2 r * profile u r) +
        (∫ r in (0 : ℝ)..1, (profile u r)⁻¹)) / 2 := by
  have hc : Continuous μ.xi2 := by unfold FiniteMixture.xi2; fun_prop
  have hxi : (∫ r in (0 : ℝ)..1, μ.xi2 r) = μ.xi1 1 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => μ.hasDerivAt_xi1 r) (hc.intervalIntegrable _ _), xi1_zero, sub_zero]
  have hmass := mass_continuous u
  have he : (∫ r in (0 : ℝ)..1, μ.xi2 r * profile u r) =
      μ.xi1 1 * u.L - ∫ r in (0 : ℝ)..1,
        μ.xi2 r * (∫ s in (0 : ℝ)..r, u.alpha s) := by
    simp only [profile, mul_sub]
    rw [intervalIntegral.integral_sub (f := fun r => μ.xi2 r * u.L)
      (g := fun r => μ.xi2 r * (∫ s in (0 : ℝ)..r, u.alpha s))
      ((hc.mul continuous_const).intervalIntegrable _ _)
      ((hc.continuousOn.mul hmass).intervalIntegrable_of_Icc zero_le_one),
      intervalIntegral.integral_mul_const, hxi]
  rw [he]
  rfl

/-- Distinct profile functions have a strictly smaller midpoint objective. -/
theorem groundFunctional_midpoint_strict (μ : FiniteMixture) (u v : GroundProfile)
    (hne : ∃ r ∈ Icc (0 : ℝ) 1, profile u r ≠ profile v r) :
    groundFunctional μ (midpoint u v) <
      (groundFunctional μ u + groundFunctional μ v) / 2 := by
  have hJ := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    zero_lt_one (inverse_profile_continuous (midpoint u v))
    (((inverse_profile_continuous u).add (inverse_profile_continuous v)).div_const 2)
    (fun r hr => by
      rw [profile_midpoint u v ⟨hr.1.le, hr.2⟩]
      have h := CrisantiSommers.reciprocal_convex_combination
        (a := (1 : ℝ) / 2) (b := (1 : ℝ) / 2)
        (by norm_num) (by norm_num) (by norm_num) (profile_pos u ⟨hr.1.le, hr.2⟩) (profile_pos v ⟨hr.1.le, hr.2⟩)
      convert h using 1 <;> (try simp only [Pi.add_apply]) <;> ring)
    (by
      obtain ⟨r, hr, hne⟩ := hne
      refine ⟨r, hr, ?_⟩
      rw [profile_midpoint u v hr]
      exact CrisantiSommers.reciprocal_midpoint_strict
        (profile_pos u hr) (profile_pos v hr) hne)
  have hiu := (inverse_profile_continuous u).intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have hiv := (inverse_profile_continuous v).intervalIntegrable_of_Icc (μ := volume) zero_le_one
  simp only [Pi.add_apply] at hJ
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add hiu hiv] at hJ
  have hc : Continuous μ.xi2 := by unfold FiniteMixture.xi2; fun_prop
  have hE : (∫ r in (0 : ℝ)..1, μ.xi2 r * profile (midpoint u v) r) =
      ((∫ r in (0 : ℝ)..1, μ.xi2 r * profile u r) +
        (∫ r in (0 : ℝ)..1, μ.xi2 r * profile v r)) / 2 := by
    rw [intervalIntegral.integral_congr (g := fun r =>
      (μ.xi2 r * profile u r + μ.xi2 r * profile v r) / 2)]
    · rw [intervalIntegral.integral_div, intervalIntegral.integral_add
        (f := fun r => μ.xi2 r * profile u r) (g := fun r => μ.xi2 r * profile v r)
        (by simpa only [Pi.mul_def] using
          ((hc.continuousOn.mul (profile_continuous u)).intervalIntegrable_of_Icc
            (μ := volume) zero_le_one))
        (by simpa only [Pi.mul_def] using
          ((hc.continuousOn.mul (profile_continuous v)).intervalIntegrable_of_Icc
            (μ := volume) zero_le_one))]
    · intro r hr
      rw [uIcc_of_le zero_le_one] at hr
      dsimp only
      rw [profile_midpoint u v hr]
      ring
  rw [groundFunctional_eq_integral, groundFunctional_eq_integral,
    groundFunctional_eq_integral, hE]
  linarith

/-- Uniqueness is literal equality of profiles on the full closed interval. -/
theorem minimizer_profile_unique (μ : FiniteMixture) (u v : GroundProfile)
    (hu : ∀ w, groundFunctional μ u ≤ groundFunctional μ w)
    (hv : ∀ w, groundFunctional μ v ≤ groundFunctional μ w) :
    ∀ r ∈ Icc (0 : ℝ) 1, profile u r = profile v r := by
  by_contra h
  push Not at h
  have hstrict := groundFunctional_midpoint_strict μ u v h
  have h1 := hu (midpoint u v)
  have h2 := hu v
  have h3 := hv u
  linarith

/-- The manuscript's full admissible domain on `[0,q]`. Endpoint and
outside-interval slope values are deliberately not identified. -/
structure RadiusGroundProfile (q : ℝ) where
  L : ℝ
  alpha : ℝ → ℝ
  alpha_nonnegative : ∀ v ∈ Ico (0 : ℝ) q, 0 ≤ alpha v
  alpha_monotone : MonotoneOn alpha (Ico (0 : ℝ) q)
  alpha_rightContinuous : ∀ v ∈ Ico (0 : ℝ) q,
    ContinuousWithinAt alpha (Ici v) v
  alpha_integrable : IntervalIntegrable alpha volume 0 q
  height_gt_mass : (∫ v in (0 : ℝ)..q, alpha v) < L

/-- The actual function on the radius interval. -/
def radiusProfile {q : ℝ} (u : RadiusGroundProfile q) (v : ℝ) : ℝ :=
  u.L - ∫ w in (0 : ℝ)..v, u.alpha w

/-- The printed `𝒬q`, with no one-step restriction. -/
def radiusFunctional (μ : FiniteMixture) {q : ℝ} (u : RadiusGroundProfile q) : ℝ :=
  ((∫ v in (0 : ℝ)..q, μ.xi2 v * radiusProfile u v) +
    (∫ v in (0 : ℝ)..q, (radiusProfile u v)⁻¹)) / 2

private theorem integral_comp_scale (α : ℝ → ℝ) {q : ℝ} (hq : 0 < q) (r : ℝ) :
    (∫ s in (0 : ℝ)..r, α (q * s)) =
      (∫ s in (0 : ℝ)..(q * r), α s) / q := by
  simpa only [mul_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    intervalIntegral.integral_comp_mul_left (a := 0) (b := r) α hq.ne'

private theorem integral_comp_divide (α : ℝ → ℝ) {q : ℝ} (hq : 0 < q) (v : ℝ) :
    (∫ w in (0 : ℝ)..v, α (w / q)) = q * (∫ s in (0 : ℝ)..(v / q), α s) := by
  simpa only [zero_div, smul_eq_mul] using
    intervalIntegral.integral_comp_div (a := 0) (b := v) α hq.ne'

/-- Rescale a unit Chen–Sen pair to the entire source radius domain. -/
def rescale {q : ℝ} (hq : 0 < q) (u : GroundProfile) : RadiusGroundProfile q where
  L := q * u.L
  alpha := fun v => u.alpha (v / q)
  alpha_nonnegative := fun v hv => u.alpha_nonnegative (v / q)
    ⟨div_nonneg hv.1 hq.le, (div_lt_one hq).mpr hv.2⟩
  alpha_monotone := fun v hv w hw hvw => u.alpha_monotone
    ⟨div_nonneg hv.1 hq.le, (div_lt_one hq).mpr hv.2⟩
    ⟨div_nonneg hw.1 hq.le, (div_lt_one hq).mpr hw.2⟩
    ((div_le_div_iff_of_pos_right hq).mpr hvw)
  alpha_rightContinuous := by
    intro v hv
    exact (u.alpha_rightContinuous (v / q)
      ⟨div_nonneg hv.1 hq.le, (div_lt_one hq).mpr hv.2⟩).comp (f := fun w : ℝ => w / q)
      (show ContinuousWithinAt (fun w : ℝ => w / q) (Ici v) v from
        (continuousAt_id.div_const q).continuousWithinAt)
      (fun w hw => (div_le_div_iff_of_pos_right hq).mpr hw)
  alpha_integrable := by
    have h := u.alpha_integrable.comp_mul_left (c := q⁻¹)
    simpa only [zero_div, one_div, inv_inv, div_eq_mul_inv, mul_comm, mul_zero, mul_one] using h
  height_gt_mass := by
    rw [integral_comp_divide u.alpha hq, div_self hq.ne']
    exact mul_lt_mul_of_pos_left u.height_gt_mass hq

/-- Normalize any admissible source profile; thus no radius profiles are lost. -/
def normalize {q : ℝ} (hq : 0 < q) (u : RadiusGroundProfile q) : GroundProfile where
  L := u.L / q
  alpha := fun r => u.alpha (q * r)
  alpha_nonnegative := fun r hr => u.alpha_nonnegative (q * r)
    ⟨mul_nonneg hq.le hr.1, by nlinarith [hr.2]⟩
  alpha_monotone := fun r hr s hs hrs => u.alpha_monotone
    ⟨mul_nonneg hq.le hr.1, by nlinarith [hr.2]⟩
    ⟨mul_nonneg hq.le hs.1, by nlinarith [hs.2]⟩
    (mul_le_mul_of_nonneg_left hrs hq.le)
  alpha_rightContinuous := by
    intro r hr
    exact (u.alpha_rightContinuous (q * r)
      ⟨mul_nonneg hq.le hr.1, by nlinarith [hr.2]⟩).comp
      (continuousAt_const.mul continuousAt_id).continuousWithinAt
      (fun s hs => mul_le_mul_of_nonneg_left hs hq.le)
  alpha_integrable := by
    have h := u.alpha_integrable.comp_mul_left (c := q)
    simpa only [zero_div, div_self hq.ne'] using h
  height_gt_mass := by
    rw [integral_comp_scale u.alpha hq, mul_one]
    exact (div_lt_div_iff_of_pos_right hq).mpr u.height_gt_mass

/-- The source's exact change of variables `ℓ(v) = q b(v/q)`. -/
theorem radiusProfile_rescale {q : ℝ} (hq : 0 < q) (u : GroundProfile) (v : ℝ) :
    radiusProfile (rescale hq u) v = q * profile u (v / q) := by
  change q * u.L - (∫ w in (0 : ℝ)..v, u.alpha (w / q)) = _
  rw [integral_comp_divide u.alpha hq]
  unfold profile
  ring

/-- The inverse substitution, valid as a function even off the physical interval. -/
theorem profile_normalize {q : ℝ} (hq : 0 < q) (u : RadiusGroundProfile q) (r : ℝ) :
    profile (normalize hq u) r = radiusProfile u (q * r) / q := by
  change u.L / q - (∫ s in (0 : ℝ)..r, u.alpha (q * s)) = _
  rw [integral_comp_scale u.alpha hq]
  unfold radiusProfile
  ring

private theorem radiusProfile_rescale_normalize {q : ℝ} (hq : 0 < q)
    (u : RadiusGroundProfile q) (v : ℝ) :
    radiusProfile (rescale hq (normalize hq u)) v = radiusProfile u v := by
  rw [radiusProfile_rescale, profile_normalize]
  simp only [mul_div_cancel₀ _ hq.ne']

/-- Equality with the printed radius functional for every Chen–Sen pair. -/
theorem groundFunctional_center_eq_radius (μ : FiniteMixture) {q : ℝ}
    (hq : 0 < q) (u : GroundProfile) :
    groundFunctional (centerMixture μ q hq) u = radiusFunctional μ (rescale hq u) := by
  rw [groundFunctional_eq_integral]
  have he : (∫ r in (0 : ℝ)..1, (centerMixture μ q hq).xi2 r * profile u r) =
      ∫ v in (0 : ℝ)..q, μ.xi2 v * radiusProfile (rescale hq u) v := by
    have hcv := integral_comp_scale
      (fun v => μ.xi2 v * radiusProfile (rescale hq u) v) hq 1
    simp only [mul_one] at hcv
    have hcv' := congrArg (fun x : ℝ => q * x) hcv
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hq.ne'] at hcv'
    rw [← hcv', ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only
    rw [centerMixture_xi2, radiusProfile_rescale]
    simp only [mul_div_cancel_left₀ _ hq.ne']
    ring
  have hi : (∫ r in (0 : ℝ)..1, (profile u r)⁻¹) =
      ∫ v in (0 : ℝ)..q, (radiusProfile (rescale hq u) v)⁻¹ := by
    have hcv := integral_comp_scale
      (fun v => (radiusProfile (rescale hq u) v)⁻¹) hq 1
    simp only [mul_one] at hcv
    have hcv' := congrArg (fun x : ℝ => q * x) hcv
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hq.ne'] at hcv'
    rw [← hcv', ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only
    rw [radiusProfile_rescale]
    simp only [mul_div_cancel_left₀ _ hq.ne', mul_inv_rev]
    field_simp
  rw [he, hi]
  rfl

/-- The inverse objective transport covers every source radius profile. -/
theorem radiusFunctional_eq_normalize (μ : FiniteMixture) {q : ℝ}
    (hq : 0 < q) (u : RadiusGroundProfile q) :
    radiusFunctional μ u = groundFunctional (centerMixture μ q hq) (normalize hq u) := by
  rw [groundFunctional_center_eq_radius]
  unfold radiusFunctional
  simp only [radiusProfile_rescale_normalize]

/-- Uniqueness on the radius interval is a deterministic strict-convexity
consequence, independent of the published attainment theorem. -/
theorem radius_minimizer_profile_unique (μ : FiniteMixture) {q : ℝ} (hq : 0 < q)
    (u v : RadiusGroundProfile q)
    (hu : ∀ w : RadiusGroundProfile q, radiusFunctional μ u ≤ radiusFunctional μ w)
    (hv : ∀ w : RadiusGroundProfile q, radiusFunctional μ v ≤ radiusFunctional μ w) :
    ∀ r ∈ Icc (0 : ℝ) q, radiusProfile u r = radiusProfile v r := by
  have hnorm (a : RadiusGroundProfile q)
      (ha : ∀ w : RadiusGroundProfile q, radiusFunctional μ a ≤ radiusFunctional μ w) :
      ∀ w : GroundProfile, groundFunctional (centerMixture μ q hq) (normalize hq a) ≤
        groundFunctional (centerMixture μ q hq) w := by
    intro w
    rw [← radiusFunctional_eq_normalize, groundFunctional_center_eq_radius]
    exact ha _
  intro r hr
  have heq := minimizer_profile_unique (centerMixture μ q hq)
    (normalize hq u) (normalize hq v) (hnorm u hu) (hnorm v hv)
    (r / q) ⟨div_nonneg hr.1 hq.le, (div_le_one hq).mpr hr.2⟩
  simp only [profile_normalize, mul_div_cancel₀ _ hq.ne'] at heq
  exact (div_left_inj' hq.ne').mp heq

/-- Source `thm:th-ground`: the physical limit, minimum over the full source
radius domain, and equality of every minimizing function on `[0,q]`.
This applies to every `q > 0`, in particular the printed `0 < q ≤ 1`. -/
theorem source_ground_limit_unique (hChenSen : ChenSenFiniteGround) (μ : FiniteMixture)
    {q : ℝ} (hq : 0 < q) :
    ∃ u : RadiusGroundProfile q,
      (∀ v : RadiusGroundProfile q, radiusFunctional μ u ≤ radiusFunctional μ v) ∧
      Tendsto (fun N : ℕ => expectedCenterGroundEnergy N μ q) atTop
        (𝓝 (radiusFunctional μ u)) ∧
      (∀ v : RadiusGroundProfile q,
        (∀ w : RadiusGroundProfile q, radiusFunctional μ v ≤ radiusFunctional μ w) →
        ∀ r ∈ Icc (0 : ℝ) q, radiusProfile v r = radiusProfile u r) := by
  obtain ⟨u, hmin, hlim⟩ := center_ground_limit hChenSen μ hq
  refine ⟨rescale hq u, ?_, ?_, ?_⟩
  · intro v
    rw [← groundFunctional_center_eq_radius, radiusFunctional_eq_normalize μ hq v]
    exact hmin _
  · rwa [groundFunctional_center_eq_radius] at hlim
  · intro v hv
    apply radius_minimizer_profile_unique μ hq v (rescale hq u) hv
    intro w
    rw [← groundFunctional_center_eq_radius, radiusFunctional_eq_normalize μ hq w]
    exact hmin _

end SlowEquilibration.SourceGroundProfileUniqueness

-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceLiteratureGroundState
public import SlowEquilibration.SourceLiteratureGroundStateRadialCoefficients
public import SlowEquilibration.CSTAPGroundTrialQuadratic

/-!
# The source ground trial as a genuine Chen–Sen profile

Source Section 5, change of variables after `thm:th-ground`: an admissible
ground profile `ℓ` on `[0,q]` corresponds to the Chen–Sen pair `(L, α)` for
the center covariance `η(t) = ξ(q t)` through `ℓ(v) = q b(v/q)`, with
`b(r) = L - ∫₀^r α`. Here this is carried out for the trial profiles
`ℓ_ε(v) = β x̂(v) + ε (q - v)` of the two-atom certificate law.

The slope `α(r) = β ζ([0,qr]) + ε` is a right-continuous nondecreasing step
function, so `(L, α)` lies in the full Chen–Sen domain, and its Chen–Sen
objective equals the repository's zero-temperature trial functional.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceLiteratureGroundTrialProfile

open MeasureTheory Set Filter CrisantiSommers SphericalTAPCertificate
open CSTAPGroundTrialQuadratic SourceLiteratureGroundState
open SourceLiteratureGroundStateRadialCoefficients
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! ### Derivatives of the center covariance -/

theorem centerMixture_xi1 (μ : FiniteMixture) (q : ℝ) (hq : 0 < q) (t : ℝ) :
    (centerMixture μ q hq).xi1 t = q * μ.xi1 (q * t) := by
  have h1 := (centerMixture μ q hq).hasDerivAt_xi t
  have hfun : (centerMixture μ q hq).xi = fun s => μ.xi (q * s) :=
    funext (centerMixture_xi μ q hq)
  rw [hfun] at h1
  have h2 := (μ.hasDerivAt_xi (q * t)).comp t ((hasDerivAt_id' t).const_mul q)
  rw [h1.unique h2]
  ring

theorem centerMixture_xi2 (μ : FiniteMixture) (q : ℝ) (hq : 0 < q) (t : ℝ) :
    (centerMixture μ q hq).xi2 t = q ^ 2 * μ.xi2 (q * t) := by
  have h1 := (centerMixture μ q hq).hasDerivAt_xi1 t
  have hfun : (centerMixture μ q hq).xi1 = fun s => q * μ.xi1 (q * s) :=
    funext (centerMixture_xi1 μ q hq)
  rw [hfun] at h1
  have h2 := ((μ.hasDerivAt_xi1 (q * t)).comp t
    ((hasDerivAt_id' t).const_mul q)).const_mul q
  rw [h1.unique h2]
  ring

theorem xi1_zero (μ : FiniteMixture) : μ.xi1 0 = 0 := by
  unfold FiniteMixture.xi1
  apply Finset.sum_eq_zero
  intro p hp
  have hp2 := μ.degree_ge_two hp
  rw [zero_pow (show p - 1 ≠ 0 by omega), mul_zero]

/-! ### The trial slope -/

/-- `α(r) = β ζ([0, q r]) + ε` for `ζ = x δ₀ + (1-x) δ_Q`, on `r ≥ 0`. -/
def trialAlpha (β x Q q ε : ℝ) (r : ℝ) : ℝ :=
  if q * r < Q then β * x + ε else β + ε

theorem trialAlpha_monotone {β x Q q ε : ℝ} (hβ : 0 ≤ β) (hx : x ≤ 1)
    (hq : 0 ≤ q) : Monotone (trialAlpha β x Q q ε) := by
  intro r s hrs
  unfold trialAlpha
  have hmul : q * r ≤ q * s := mul_le_mul_of_nonneg_left hrs hq
  split_ifs with h1 h2 h2
  · exact le_rfl
  · nlinarith [mul_nonneg hβ (sub_nonneg.mpr hx)]
  · exfalso
    linarith
  · exact le_rfl

theorem trialAlpha_rightContinuous {β x Q q ε : ℝ} (hq : 0 ≤ q) (r : ℝ) :
    ContinuousWithinAt (trialAlpha β x Q q ε) (Ici r) r := by
  by_cases h : q * r < Q
  · have hopen : {s : ℝ | q * s < Q} ∈ 𝓝 r :=
      (isOpen_lt (continuous_const.mul continuous_id) continuous_const).mem_nhds h
    have heq : (fun _ : ℝ => β * x + ε) =ᶠ[𝓝 r] trialAlpha β x Q q ε := by
      filter_upwards [hopen] with s hs
      simp only [trialAlpha, ite_eq_left (show q * s < Q from hs)]
    exact (continuousAt_const.congr heq).continuousWithinAt
  · apply (continuousWithinAt_const (b := β + ε)).congr
    · intro s hs
      have : ¬ q * s < Q := by
        have : q * r ≤ q * s := mul_le_mul_of_nonneg_left hs hq
        intro hlt
        exact h (lt_of_le_of_lt this hlt)
      simp only [trialAlpha, ite_eq_right this]
    · simp only [trialAlpha, ite_eq_right h]

/-- The trial mass `∫₀^r α = (β/q)(x̂(0) - x̂(q r)) + ε r` on `r ≥ 0`. -/
theorem integral_trialAlpha {β x Q q ε : ℝ} (hβ : 0 ≤ β) (hx : x ∈ Icc (0 : ℝ) 1)
    (hQ : Q ∈ Ioo (0 : ℝ) 1) (hq : 0 < q) {r : ℝ} (hr : 0 ≤ r) :
    (∫ s in (0 : ℝ)..r, trialAlpha β x Q q ε s) =
      β / q * ((1 - Q + x * Q) - xHat (twoAtom x Q) (q * r)) + ε * r := by
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ Q / q := by
    rw [ae_iff]
    simp
  have hconst_below (b : ℝ) (h0b : 0 ≤ b) (hb : q * b ≤ Q) :
      (∫ s in (0 : ℝ)..b, trialAlpha β x Q q ε s) = b * (β * x + ε) := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => β * x + ε)]
    · simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    · filter_upwards [hne] with s hs hsI
      rw [uIoc_of_le h0b] at hsI
      have hle : q * s ≤ Q :=
        (mul_le_mul_of_nonneg_left hsI.2 hq.le).trans hb
      have hlt : q * s < Q := by
        refine lt_of_le_of_ne hle ?_
        intro heq
        apply hs
        rw [← heq, mul_div_cancel_left₀ s hq.ne']
      simp only [trialAlpha, ite_eq_left hlt]
  by_cases hqr : q * r ≤ Q
  · rw [hconst_below r hr hqr, xHat_twoAtom hx (mul_nonneg hq.le hr), ite_eq_left hqr]
    field_simp
    ring
  · have hr₀ : q * (Q / q) = Q := by field_simp
    have hr₀r : Q / q ≤ r := by
      rw [div_le_iff₀ hq]
      linarith
    have hr₀0 : 0 ≤ Q / q := div_nonneg hQ.1.le hq.le
    have hupper : (∫ s in (Q / q)..r, trialAlpha β x Q q ε s) =
        (r - Q / q) * (β + ε) := by
      rw [intervalIntegral.integral_congr_ae (g := fun _ => β + ε)]
      · simp only [intervalIntegral.integral_const, smul_eq_mul]
      · refine Filter.Eventually.of_forall (fun s hsI => ?_)
        rw [uIoc_of_le hr₀r] at hsI
        have hlt : Q < q * s := by
          have := mul_lt_mul_of_pos_left hsI.1 hq
          rwa [hr₀] at this
        simp only [trialAlpha, ite_eq_right (not_lt.mpr hlt.le)]
    have hint : ∀ a b : ℝ,
        IntervalIntegrable (trialAlpha β x Q q ε) volume a b :=
      fun a b => (trialAlpha_monotone hβ hx.2 hq.le).intervalIntegrable
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 (Q / q)) (hint (Q / q) r),
      hconst_below (Q / q) hr₀0 hr₀.le, hupper,
      xHat_twoAtom hx (mul_nonneg hq.le hr), ite_eq_right hqr]
    field_simp
    ring

/-! ### The Chen–Sen pair of the trial profile -/

theorem trialAlpha_nonneg {β x Q q ε : ℝ} (hβ : 0 ≤ β) (hx : 0 ≤ x)
    (hε : 0 ≤ ε) (r : ℝ) : 0 ≤ trialAlpha β x Q q ε r := by
  unfold trialAlpha
  split_ifs
  · exact add_nonneg (mul_nonneg hβ hx) hε
  · exact add_nonneg hβ hε

/-- The height `L = ℓ_ε(0)/q` of the rescaled trial profile. -/
def trialHeight (β x Q q ε : ℝ) : ℝ := (β * (1 - Q + x * Q) + ε * q) / q

/-- `L - ∫₀^r α = ℓ_ε(q r)/q` on `r ≥ 0`. -/
theorem trialHeight_sub_mass {β x Q q ε : ℝ} (hβ : 0 ≤ β) (hx : x ∈ Icc (0 : ℝ) 1)
    (hQ : Q ∈ Ioo (0 : ℝ) 1) (hq : 0 < q) {r : ℝ} (hr : 0 ≤ r) :
    trialHeight β x Q q ε - (∫ s in (0 : ℝ)..r, trialAlpha β x Q q ε s) =
      profile β (twoAtom x Q) q ε (q * r) / q := by
  rw [integral_trialAlpha hβ hx hQ hq hr, trialHeight, profile]
  field_simp
  ring

/-- The source trial profile `ℓ_ε`, rescaled to Chen–Sen's unit interval. -/
def trialGroundProfile {μ : FiniteMixture} {β x Q : ℝ} (h : Certificate μ β x Q)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) {ε : ℝ} (hε : 0 ≤ ε) : GroundProfile where
  L := trialHeight β x Q q ε
  alpha := trialAlpha β x Q q ε
  alpha_nonnegative := fun r _ =>
    trialAlpha_nonneg h.beta_pos.le h.weight_range.1.le hε r
  alpha_monotone :=
    (trialAlpha_monotone h.beta_pos.le h.weight_range.2.le hq.1.le).monotoneOn _
  alpha_rightContinuous := fun r _ => trialAlpha_rightContinuous hq.1.le r
  alpha_integrable :=
    (trialAlpha_monotone h.beta_pos.le h.weight_range.2.le hq.1.le).intervalIntegrable
  height_gt_mass := by
    have hx : x ∈ Icc (0 : ℝ) 1 := ⟨h.weight_range.1.le, h.weight_range.2.le⟩
    have : IsProbabilityMeasure (twoAtom x Q) := twoAtom_probability hx
    have hcut : HasCutoff (twoAtom x Q) Q :=
      twoAtom_hasCutoff ⟨h.overlap_range.1.le, h.overlap_range.2⟩
    have hd := trialHeight_sub_mass (ε := ε) h.beta_pos.le hx h.overlap_range hq.1
      zero_le_one
    have hpos : 0 < profile β (twoAtom x Q) q ε (q * 1) / q := by
      rw [mul_one, profile, sub_self, mul_zero, add_zero]
      exact div_pos (mul_pos h.beta_pos (xHat_pos _ hcut hq.2)) hq.1
    linarith

/-- The Chen–Sen objective of the rescaled trial is the source
zero-temperature functional `𝒬_q(ℓ_ε)` of the center covariance. -/
theorem groundFunctional_trialGroundProfile {μ : FiniteMixture} {β x Q : ℝ}
    (h : Certificate μ β x Q) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) {ε : ℝ}
    (hε : 0 ≤ ε) :
    groundFunctional (centerMixture μ q hq.1) (trialGroundProfile h hq hε) =
      CSTAPGroundTrialQuadratic.functional μ β (twoAtom x Q) q ε := by
  have hx : x ∈ Icc (0 : ℝ) 1 := ⟨h.weight_range.1.le, h.weight_range.2.le⟩
  have hQ := h.overlap_range
  have hq0 := hq.1
  have : IsProbabilityMeasure (twoAtom x Q) := twoAtom_probability hx
  have hcut : HasCutoff (twoAtom x Q) Q := twoAtom_hasCutoff ⟨hQ.1.le, hQ.2⟩
  have hxc : Continuous (xHat (twoAtom x Q)) := xHat_continuous _ hcut
  set ℓ := profile β (twoAtom x Q) q ε with hℓ
  have hℓc : Continuous ℓ := by
    rw [hℓ]
    unfold profile
    exact (continuous_const.mul hxc).add
      (continuous_const.mul (continuous_const.sub continuous_id))
  have hℓpos : ∀ v ∈ Icc (0 : ℝ) q, 0 < ℓ v := by
    intro v hv
    rw [hℓ]
    unfold profile
    have h1 : 0 < β * xHat (twoAtom x Q) v :=
      mul_pos h.beta_pos (xHat_pos _ hcut (hv.2.trans_lt hq.2))
    have h2 : 0 ≤ ε * (q - v) := mul_nonneg hε (sub_nonneg.mpr hv.2)
    linarith
  have hxi2 : Continuous μ.xi2 := continuous_iff_continuousAt.mpr
    (fun v => (μ.hasDerivAt_xi2 v).continuousAt)
  set cm := centerMixture μ q hq0 with hcm
  have hcxi2 : Continuous cm.xi2 := continuous_iff_continuousAt.mpr
    (fun v => (cm.hasDerivAt_xi2 v).continuousAt)
  let b : ℝ → ℝ := fun r => ℓ (q * r) / q
  have hbc : Continuous b := (hℓc.comp (continuous_const.mul continuous_id)).div_const q
  have hmass : ∀ r ∈ uIcc (0 : ℝ) 1,
      (trialGroundProfile h hq hε).L -
        (∫ s in (0 : ℝ)..r, (trialGroundProfile h hq hε).alpha s) = b r := by
    intro r hr
    rw [uIcc_of_le zero_le_one] at hr
    exact trialHeight_sub_mass h.beta_pos.le hx hQ hq0 hr.1
  have hqr : ∀ r ∈ Icc (0 : ℝ) 1, q * r ∈ Icc (0 : ℝ) q := by
    intro r hr
    exact ⟨mul_nonneg hq0.le hr.1, by nlinarith [hr.2]⟩
  -- energy part
  have hxi2int : (∫ r in (0 : ℝ)..1, cm.xi2 r) = cm.xi1 1 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => cm.hasDerivAt_xi1 r) (hcxi2.intervalIntegrable _ _), xi1_zero cm,
      sub_zero]
  have henergy : cm.xi1 1 * (trialGroundProfile h hq hε).L -
      (∫ r in (0 : ℝ)..1, cm.xi2 r *
        (∫ s in (0 : ℝ)..r, (trialGroundProfile h hq hε).alpha s)) =
      ∫ r in (0 : ℝ)..1, cm.xi2 r * b r := by
    rw [intervalIntegral.integral_congr (g := fun r => cm.xi2 r *
      ((trialGroundProfile h hq hε).L - b r))]
    · rw [← hxi2int]
      simp_rw [mul_sub]
      rw [intervalIntegral.integral_sub
        (f := fun r => cm.xi2 r * (trialGroundProfile h hq hε).L)
        (g := fun r => cm.xi2 r * b r)
        ((hcxi2.mul continuous_const).intervalIntegrable _ _)
        ((hcxi2.mul hbc).intervalIntegrable _ _), intervalIntegral.integral_mul_const]
      ring
    · intro r hr
      simp only
      rw [← hmass r hr]
      ring
  have hscale_energy : (∫ r in (0 : ℝ)..1, cm.xi2 r * b r) =
      ∫ v in (0 : ℝ)..q, μ.xi2 v * ℓ v := by
    rw [intervalIntegral.integral_congr (g := fun r => q * (μ.xi2 (q * r) * ℓ (q * r)))]
    · have hcv := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
        (fun v => μ.xi2 v * ℓ v) hq0.ne'
      simp only [mul_zero, mul_one, smul_eq_mul] at hcv
      rw [intervalIntegral.integral_const_mul, hcv, ← mul_assoc, mul_inv_cancel₀ hq0.ne',
        one_mul]
    · intro r _
      simp only [b, hcm, centerMixture_xi2]
      field_simp
  have hscale_entropy : (∫ r in (0 : ℝ)..1, (b r)⁻¹) =
      ∫ v in (0 : ℝ)..q, (ℓ v)⁻¹ := by
    rw [intervalIntegral.integral_congr (g := fun r => q * (ℓ (q * r))⁻¹)]
    · have hcv := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
        (fun v => (ℓ v)⁻¹) hq0.ne'
      simp only [mul_zero, mul_one, smul_eq_mul] at hcv
      rw [intervalIntegral.integral_const_mul, hcv, ← mul_assoc, mul_inv_cancel₀ hq0.ne',
        one_mul]
    · intro r _
      simp only [b]
      rw [inv_div]
      ring
  have hentropy : (∫ r in (0 : ℝ)..1, ((trialGroundProfile h hq hε).L -
      ∫ s in (0 : ℝ)..r, (trialGroundProfile h hq hε).alpha s)⁻¹) =
      ∫ r in (0 : ℝ)..1, (b r)⁻¹ := by
    apply intervalIntegral.integral_congr
    intro r hr
    simp only
    rw [hmass r hr]
  have hℓinv : IntervalIntegrable (fun v => (ℓ v)⁻¹) volume 0 q := by
    apply ContinuousOn.intervalIntegrable
    apply hℓc.continuousOn.inv₀
    intro v hv
    rw [uIcc_of_le hq0.le] at hv
    exact (hℓpos v hv).ne'
  unfold groundFunctional CSTAPGroundTrialQuadratic.functional
  rw [← hℓ, henergy, hentropy, hscale_energy, hscale_entropy,
    intervalIntegral.integral_add (f := fun v => μ.xi2 v * ℓ v)
      ((hxi2.mul hℓc).intervalIntegrable _ _) hℓinv]

end SlowEquilibration.SourceLiteratureGroundTrialProfile

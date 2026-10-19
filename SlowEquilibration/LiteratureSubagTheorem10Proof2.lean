-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagBandLowerFinal
public import SlowEquilibration.LiteratureSubagBandUpperFinal
public import SlowEquilibration.SourceMainTheoremsReducedFinal
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

/-!
The ground-profile part of Subag's Proposition 11 is proved over the full
monotone, right-continuous, integrable profile domain. Its finite-temperature
residual counterpart and the telescope give the contact TAP identity.

The remaining positive-overlap lower band approximation suffices both for
positive contacts and for the exact zero-contact lower tail. For the latter,
small positive-overlap blocks are embedded in a zero-overlap block and the
residual pressure is controlled by uniform covariance stability at the origin.
Theorem 10 and the requested endpoints thus retain only this one physical
approximation, besides Chen where used. Its proof, and therefore the requested
Chen-only probability conclusions, remain unfinished.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.LiteratureSubagTheorem10Proof2

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel CrisantiSommers CSParisiMeasure
open LiteratureSubagPhysicalDefinitions LiteratureSubagContact
open LiteratureSubagTheorem10Proof LiteratureSubagTheorem10Final
open SourceGroundProfileUniqueness SourceGeneralContactTheorem
open LiteratureSubagTAP LiteratureSubagTheorem5Proof
open SourceLiteratureParisi SourceLiteratureGroundState
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem radiusProfile_continuous {q : ℝ} (hq : 0 ≤ q)
    (u : RadiusGroundProfile q) : ContinuousOn (radiusProfile u) (Icc 0 q) := by
  exact continuousOn_const.sub (by
    simpa only [uIcc_of_le hq] using
      intervalIntegral.continuousOn_primitive_interval' u.alpha_integrable left_mem_uIcc)

private theorem radiusProfile_pos {q r : ℝ} (hq : 0 ≤ q)
    (u : RadiusGroundProfile q) (hr : r ∈ Icc 0 q) : 0 < radiusProfile u r := by
  have htail : 0 ≤ ∫ s in r..q, u.alpha s := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hr.2
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      (volume.restrict (Icc r q)).ae_ne q] with s hs hsq
    exact u.alpha_nonnegative s ⟨hr.1.trans hs.1, lt_of_le_of_ne hs.2 hsq⟩
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (u.alpha_integrable.mono_set (by
      rw [uIcc_of_le hr.1, uIcc_of_le hq]
      exact Icc_subset_Icc le_rfl hr.2))
    (u.alpha_integrable.mono_set (by
      rw [uIcc_of_le hr.2, uIcc_of_le hq]
      exact Icc_subset_Icc hr.1 le_rfl))
  unfold radiusProfile
  linarith [u.height_gt_mass]

private theorem radiusProfile_hasRightDerivative {q r : ℝ}
    (u : RadiusGroundProfile q) (hr : r ∈ Ioo 0 q) :
    HasDerivWithinAt (radiusProfile u) (-u.alpha r) (Ioi r) r := by
  have hi : IntervalIntegrable u.alpha volume 0 r := u.alpha_integrable.mono_set (by
    rw [uIcc_of_le hr.1.le, uIcc_of_le (hr.1.trans hr.2).le]
    exact Icc_subset_Icc le_rfl hr.2.le)
  have hm : StronglyMeasurableAtFilter u.alpha (𝓝[>] r) := by
    exact ⟨Ico 0 q, mem_nhdsWithin_of_mem_nhds (Ico_mem_nhds hr.1 hr.2),
      (aemeasurable_restrict_of_monotoneOn measurableSet_Ico u.alpha_monotone).aestronglyMeasurable⟩
  exact ((intervalIntegral.integral_hasDerivWithinAt_right hi
    (s := Ici r) (t := Ioi r) hm
    ((u.alpha_rightContinuous r ⟨hr.1.le, hr.2⟩).mono Ioi_subset_Ici_self)).const_sub u.L).Ioi_of_Ici

private theorem integral_force_radiusProfile {q : ℝ} (hq : 0 < q)
    (u : RadiusGroundProfile q) (F f : ℝ → ℝ)
    (hF : ContinuousOn F (Icc 0 q))
    (hf : ContinuousOn f (Icc 0 q))
    (hd : ∀ t ∈ Ioo 0 q, HasDerivAt F (f t) t)
    (hF0 : F 0 = 0) (hFq : F q = 0) :
    (∫ t in (0 : ℝ)..q, f t * radiusProfile u t) =
      ∫ t in (0 : ℝ)..q, F t * u.alpha t := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (u := radiusProfile u) (u' := fun t => -u.alpha t) (v := F) (v' := f)
    (by simpa only [uIcc_of_le hq.le] using radiusProfile_continuous hq.le u)
    (by simpa only [uIcc_of_le hq.le] using hF)
    (by simpa only [min_eq_left hq.le, max_eq_right hq.le] using
      fun t ht => radiusProfile_hasRightDerivative u ht)
    (by simpa only [min_eq_left hq.le, max_eq_right hq.le] using
      fun t ht => (hd t ht).hasDerivWithinAt)
    u.alpha_integrable.neg (hf.intervalIntegrable_of_Icc hq.le)
  simpa only [hF0, hFq, mul_zero, sub_zero, zero_sub, neg_mul,
    intervalIntegral.integral_neg, neg_neg, mul_neg, zero_mul, mul_comm] using h

private theorem integral_monotone_mul_nonneg {q : ℝ} (hq : 0 < q)
    (u : RadiusGroundProfile q) (G F : ℝ → ℝ)
    (hF : ContinuousOn F (Icc 0 q))
    (hd : ∀ t ∈ Icc 0 q, HasDerivAt G (F t) t)
    (hGq : G q = 0) (hG : ∀ t ∈ Icc 0 q, G t ≤ 0) :
    0 ≤ ∫ t in (0 : ℝ)..q, F t * u.alpha t := by
  let a : ℕ → ℝ → ℝ := fun n t => if t < q then min (u.alpha t) n else n
  have ham (n : ℕ) : MonotoneOn (a n) (Icc 0 q) := by
    intro s hs t ht hst
    by_cases htq : t < q
    · have hsq := hst.trans_lt htq
      simp only [a, ite_eq_left htq, ite_eq_left hsq]
      exact min_le_min_right _ (u.alpha_monotone ⟨hs.1, hsq⟩ ⟨ht.1, htq⟩ hst)
    · simp only [a, ite_eq_right htq]
      split_ifs <;> simp
  have han (n : ℕ) : 0 ≤ a n 0 := by
    simp only [a, ite_eq_left hq]
    exact le_min (u.alpha_nonnegative 0 ⟨le_rfl, hq⟩) (Nat.cast_nonneg n)
  have hpos (n : ℕ) : 0 ≤ ∫ t in (0 : ℝ)..q, F t * a n t := by
    obtain ⟨r, hr, he⟩ :=
      exists_eq_const_mul_intervalIntegral_of_nonneg_of_monotoneOn
        hq.le (han n) (ham n) (hF.intervalIntegrable_of_Icc hq.le)
    have hFTC : (∫ t in r..q, F t) = G q - G r :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hd t (by
          rw [uIcc_of_le hr.2] at ht
          exact ⟨hr.1.trans ht.1, ht.2⟩))
        ((hF.mono (Icc_subset_Icc hr.1 le_rfl)).intervalIntegrable_of_Icc hr.2)
    rw [intervalIntegral.integral_congr (fun _ _ => mul_comm _ _), he, hFTC, hGq,
      zero_sub]
    exact mul_nonneg ((ham n) ⟨le_rfl, hq.le⟩ ⟨hq.le, le_rfl⟩ hq.le |>.trans'
      (han n)) (neg_nonneg.mpr (hG r hr))
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun t => F t * a n t)
      (volume.restrict (uIoc 0 q)) := by
    have ha : AEStronglyMeasurable (a n) (volume.restrict (uIoc 0 q)) := by
      rw [uIoc_of_le hq.le]
      exact (aemeasurable_restrict_of_monotoneOn measurableSet_Ioc
        ((ham n).mono Ioc_subset_Icc_self)).aestronglyMeasurable
    exact (hF.intervalIntegrable_of_Icc hq.le).def'.aestronglyMeasurable.mul ha
  have hbound (n : ℕ) : ∀ᵐ t ∂volume, t ∈ uIoc 0 q →
      ‖F t * a n t‖ ≤ ‖F t * u.alpha t‖ := by
    filter_upwards [volume.ae_ne q] with t ht htr
    rw [uIoc_of_le hq.le] at htr
    have htq : t < q := lt_of_le_of_ne htr.2 ht
    have ha0 := u.alpha_nonnegative t ⟨htr.1.le, htq⟩
    simp only [a, ite_eq_left htq, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg ha0, abs_of_nonneg (le_min ha0 (Nat.cast_nonneg n))]
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) (abs_nonneg _)
  have hlim : Tendsto (fun n => ∫ t in (0 : ℝ)..q, F t * a n t) atTop
      (𝓝 (∫ t in (0 : ℝ)..q, F t * u.alpha t)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun t => ‖F t * u.alpha t‖)
    · exact .of_forall hmeas
    · exact .of_forall hbound
    · exact (u.alpha_integrable.continuousOn_mul (by
        simpa only [uIcc_of_le hq.le] using hF)).norm
    · filter_upwards [volume.ae_ne q] with t ht htr
      rw [uIoc_of_le hq.le] at htr
      have htq : t < q := lt_of_le_of_ne htr.2 ht
      apply tendsto_const_nhds.congr'
      filter_upwards [tendsto_natCast_atTop_atTop.eventually
        (eventually_ge_atTop (u.alpha t))] with n hn
      simp [a, htq, min_eq_left hn]
  exact ge_of_tendsto hlim (.of_forall hpos)

private def force (μ : FiniteMixture) (β : ℝ) (ζ : Admissible) (t : ℝ) : ℝ :=
  β ^ 2 * μ.xi1 t - ∫ s in (0 : ℝ)..t, 1 / (xHat ζ.law s) ^ 2

private def curvature (μ : FiniteMixture) (β : ℝ) (ζ : Admissible) (t : ℝ) : ℝ :=
  β ^ 2 * μ.xi2 t - 1 / (xHat ζ.law t) ^ 2

private theorem curvature_continuousOn (μ : FiniteMixture) (β : ℝ)
    (ζ : Admissible) {q : ℝ} (hq : q < 1) :
    ContinuousOn (curvature μ β ζ) (Icc 0 q) := by
  exact (continuous_const.mul (by unfold FiniteMixture.xi2; fun_prop)).continuousOn.sub
    (continuousOn_const.div ((xHat_continuous ζ.law ζ.hasCutoff).continuousOn.pow 2)
      (fun t ht => pow_ne_zero 2 (xHat_pos ζ.law ζ.hasCutoff (ht.2.trans_lt hq)).ne'))

private theorem force_hasDerivAt (μ : FiniteMixture) (β : ℝ)
    (ζ : Admissible) {t : ℝ} (ht : t < 1) :
    HasDerivAt (force μ β ζ) (curvature μ β ζ t) t := by
  let A : ℝ → ℝ := fun s => 1 / (xHat ζ.law s) ^ 2
  have hm : Measurable A :=
    measurable_const.div ((xHat_continuous ζ.law ζ.hasCutoff).measurable.pow_const 2)
  have hc : ContinuousAt A t :=
    continuousAt_const.div ((xHat_continuous ζ.law ζ.hasCutoff).continuousAt.pow 2)
      (pow_ne_zero 2 (xHat_pos ζ.law ζ.hasCutoff ht).ne')
  have hi : IntervalIntegrable A volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div
      ((xHat_continuous ζ.law ζ.hasCutoff).continuousOn.pow 2)
      (fun s hs => pow_ne_zero 2
        (xHat_pos ζ.law ζ.hasCutoff (hs.2.trans_lt (max_lt zero_lt_one ht))).ne')
  exact ((μ.hasDerivAt_xi1 t).const_mul (β ^ 2)).sub
    (intervalIntegral.integral_hasDerivAt_right hi
      hm.aestronglyMeasurable.stronglyMeasurableAtFilter hc)

private theorem force_integral {μ : FiniteMixture} {β q : ℝ}
    (hc : Contact μ β q) (hq : 0 < q) :
    (∫ t in (0 : ℝ)..q,
      curvature μ β (canonicalMinimizer μ β) t) = 0 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => force_hasDerivAt μ β (canonicalMinimizer μ β)
      (by rw [uIcc_of_le hq.le] at ht; exact ht.2.trans_lt hc.1.2))
    ((curvature_continuousOn μ β _ hc.1.2).intervalIntegrable_of_Icc hq.le)
  simpa only [force, contact_stationary hc hq, sub_self,
    CSTAPTelescope.xi1_zero, mul_zero, intervalIntegral.integral_same] using h

private theorem contact_curvature_pairing_zero {μ : FiniteMixture} {β q : ℝ}
    (hc : Contact μ β q) (hq : 0 < q) :
    (∫ t in (0 : ℝ)..q, curvature μ β (canonicalMinimizer μ β) t *
      xHat (canonicalMinimizer μ β).law t) = 0 := by
  let ζ := canonicalMinimizer μ β
  let f := curvature μ β ζ
  have hf : ContinuousOn f (Icc 0 q) := curvature_continuousOn μ β ζ hc.1.2
  have hfi : IntervalIntegrable f volume 0 q := hf.intervalIntegrable_of_Icc hq.le
  have htri (s : ℝ) (hs : s ∈ Icc 0 q) :
      (∫ t in (0 : ℝ)..s, (s - t) * f t) = firstVariation β μ.xi ζ.law s := by
    by_cases hs0 : s = 0
    · simp [hs0, firstVariation, μ.xi_zero]
    · simpa only [f, curvature, CSStructure.potential, neg_neg, mul_comm] using
        contact_trial_first_variation μ ζ
          ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), hs.2.trans_lt hc.1.2⟩
  have hA : (∫ t in (0 : ℝ)..q, (1 - t) * f t) = 0 := by
    calc
      _ = (∫ t in (0 : ℝ)..q, (q - t) * f t) +
          (1 - q) * ∫ t in (0 : ℝ)..q, f t := by
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
          (hfi.continuousOn_mul (by fun_prop)) (hfi.const_mul (1 - q))]
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = 0 := by rw [htri q ⟨hq.le, le_rfl⟩,
          (contact_iff_firstVariation_zero μ β q).mp hc |>.2, force_integral hc hq]
                  ring
  let K : ℝ → ℝ → ℝ := fun t s => (1 - max t s) * f t
  have hfm : Measurable f := by
    exact (measurable_const.mul (by unfold FiniteMixture.xi2; fun_prop)).sub
      (measurable_const.div ((xHat_continuous ζ.law ζ.hasCutoff).measurable.pow_const 2))
  have hKm : Measurable (Function.uncurry K) :=
    (measurable_const.sub (measurable_fst.max measurable_snd)).mul (hfm.comp measurable_fst)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hKi : Integrable (Function.uncurry K)
      ((volume.restrict (Ioc (0 : ℝ) q)).prod ζ.law) := by
    apply (integrable_const (max C 0)).mono' hKm.aestronglyMeasurable
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hKm.norm measurable_const)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    filter_upwards [ζ.hasCutoff.2.2] with s hs
    have hk0 : 0 ≤ 1 - max t s := sub_nonneg.mpr
      (max_le (ht.2.trans hc.1.2.le) (hs.2.trans ζ.hasCutoff.2.1.le))
    have hk1 : 1 - max t s ≤ 1 := by linarith [le_max_left t s, ht.1]
    change ‖(1 - max t s) * f t‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs (1 - max t s),
      abs_of_nonneg hk0]
    exact (mul_le_of_le_one_left (norm_nonneg _) hk1).trans
      ((hC t ⟨ht.1.le, ht.2⟩).trans (le_max_left _ _))
  rw [← uIoc_of_le hq.le] at hKi
  have hswap := intervalIntegral_integral_swap (f := K) (a := 0) (b := q) hKi
  have hleft (t : ℝ) : (∫ s, K t s ∂ζ.law) = f t * xHat ζ.law t := by
    simp only [K, integral_mul_const, xHat, mul_comm]
  have hright : (∫ s, (∫ t in (0 : ℝ)..q, K t s) ∂ζ.law) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ζ.hasCutoff.2.2,
      (ThermalPhysicalZeroContact.minimizer_firstVariation_maximum_zero
        μ β ζ (canonicalMinimizer_isMinimizer μ β)).2.1] with s hs hsz
    by_cases hsq : s ≤ q
    · change (∫ t in (0 : ℝ)..q, (1 - max t s) * f t) = 0
      rw [weighted_kernel_identity hf hs.1 hsq, hA, htri s ⟨hs.1, hsq⟩, hsz, sub_self]
    · calc
        _ = (1 - s) * ∫ t in (0 : ℝ)..q, f t := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hq.le] at ht
          simp only [K, max_eq_right (ht.2.trans (le_of_not_ge hsq))]
        _ = 0 := by rw [force_integral hc hq, mul_zero]
  simpa only [hleft, hright] using hswap

/-- Proposition 11's ground clause: at a positive contact, the unperturbed
canonical trial minimizes over the entire encoded radius-profile domain.
No physical band estimate or literature hypothesis is used. -/
theorem contact_groundTrial_minimizes {μ : FiniteMixture} {β q : ℝ}
    (hβ : 0 < β) (hc : Contact μ β q) (hq : 0 < q) :
    ∀ v : RadiusGroundProfile q,
      radiusFunctional μ (groundTrial (canonicalMinimizer μ β) hβ
        ⟨hq, hc.1.2⟩ (le_refl (0 : ℝ))) ≤ radiusFunctional μ v := by
  let ζ := canonicalMinimizer μ β
  let u := groundTrial ζ hβ ⟨hq, hc.1.2⟩ (le_refl (0 : ℝ))
  let f := curvature μ β ζ
  let F := force μ β ζ
  have hFc : ContinuousOn F (Icc 0 q) := fun t ht =>
    (force_hasDerivAt μ β ζ (ht.2.trans_lt hc.1.2)).continuousAt.continuousWithinAt
  have hF0 : F 0 = 0 := by simp [F, force, CSTAPTelescope.xi1_zero]
  have hFq : F q = 0 := sub_eq_zero.mpr (contact_stationary hc hq)
  have hpair (v : RadiusGroundProfile q) :
      0 ≤ ∫ t in (0 : ℝ)..q, f t * radiusProfile v t := by
    rw [integral_force_radiusProfile hq v F f hFc
      (curvature_continuousOn μ β ζ hc.1.2)
      (fun t ht => force_hasDerivAt μ β ζ (ht.2.trans hc.1.2)) hF0 hFq]
    exact integral_monotone_mul_nonneg hq v (firstVariation β μ.xi ζ.law) F hFc
      (fun t ht => firstVariation_hasDerivAt β μ.xi ζ.law ζ.hasCutoff
        (ht.2.trans_lt hc.1.2) (μ.hasDerivAt_xi t))
      ((contact_iff_firstVariation_zero μ β q).mp hc).2
      (fun t ht => (ThermalPhysicalZeroContact.minimizer_firstVariation_maximum_zero
        μ β ζ (canonicalMinimizer_isMinimizer μ β)).1 t
          ⟨ht.1, ht.2.trans_lt hc.1.2⟩)
  have hu (t : ℝ) (ht : t ∈ Icc 0 q) : radiusProfile u t = β * xHat ζ.law t := by
    simpa only [CSTAPGroundTrialQuadratic.profile, zero_mul, add_zero] using
      radiusProfile_groundTrial ζ hβ ⟨hq, hc.1.2⟩ (le_refl (0 : ℝ))
        (ht.2.trans hc.1.2.le)
  have hzero : (∫ t in (0 : ℝ)..q, f t * radiusProfile u t) = 0 := by
    calc
      _ = ∫ t in (0 : ℝ)..q, β * (f t * xHat ζ.law t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hq.le] at ht
        dsimp only
        rw [hu t ht]
        ring
      _ = 0 := by rw [intervalIntegral.integral_const_mul,
        contact_curvature_pairing_zero hc hq, mul_zero]
  intro v
  have hv := radiusProfile_continuous hq.le v
  have huc := radiusProfile_continuous hq.le u
  have hfc := curvature_continuousOn μ β ζ hc.1.2
  have hxi : ContinuousOn μ.xi2 (Icc 0 q) := by unfold FiniteMixture.xi2; fun_prop
  have hi (w : RadiusGroundProfile q) : IntervalIntegrable
      (fun t => μ.xi2 t * radiusProfile w t + (radiusProfile w t)⁻¹) volume 0 q := by
    exact ((hxi.mul (radiusProfile_continuous hq.le w)).add
      ((radiusProfile_continuous hq.le w).inv₀
        (fun t ht => (radiusProfile_pos hq.le w ht).ne'))).intervalIntegrable_of_Icc hq.le
  have hlin := intervalIntegral.integral_mono_on hq.le
    (((hfc.mul hv).sub (hfc.mul huc)).intervalIntegrable_of_Icc hq.le)
    (((hi v).sub (hi u)).const_mul (β ^ 2)) (fun t ht => ?_)
  · change (∫ t in (0 : ℝ)..q, f t * radiusProfile v t - f t * radiusProfile u t) ≤ _ at hlin
    have hiv : IntervalIntegrable (fun t => f t * radiusProfile v t) volume 0 q :=
      (hfc.mul hv).intervalIntegrable_of_Icc hq.le
    have hiu : IntervalIntegrable (fun t => f t * radiusProfile u t) volume 0 q :=
      (hfc.mul huc).intervalIntegrable_of_Icc hq.le
    rw [intervalIntegral.integral_sub
        hiv hiu, hzero, sub_zero,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (hi v) (hi u)] at hlin
    have he (w : RadiusGroundProfile q) :
        (∫ t in (0 : ℝ)..q, μ.xi2 t * radiusProfile w t + (radiusProfile w t)⁻¹) =
          2 * radiusFunctional μ w := by
      have hiE : IntervalIntegrable (fun t => μ.xi2 t * radiusProfile w t) volume 0 q :=
        (hxi.mul (radiusProfile_continuous hq.le w)).intervalIntegrable_of_Icc hq.le
      have hiI : IntervalIntegrable (fun t => (radiusProfile w t)⁻¹) volume 0 q :=
        ((radiusProfile_continuous hq.le w).inv₀
          (fun t ht => (radiusProfile_pos hq.le w ht).ne')).intervalIntegrable_of_Icc hq.le
      rw [intervalIntegral.integral_add hiE hiI]
      unfold radiusFunctional
      ring
    rw [he v, he u] at hlin
    have := hpair v
    nlinarith [sq_pos_of_pos hβ]
  · have ha := radiusProfile_pos hq.le u ht
    have hb := radiusProfile_pos hq.le v ht
    have hs := mul_le_mul_of_nonneg_left (reciprocal_supporting_inequality ha hb)
      (sq_nonneg β)
    have hscale : β ^ 2 * (-(radiusProfile v t - radiusProfile u t) /
        radiusProfile u t ^ 2) =
          -(radiusProfile v t - radiusProfile u t) / xHat ζ.law t ^ 2 := by
      rw [hu t ht, mul_pow]
      field_simp [hβ.ne', (xHat_pos ζ.law ζ.hasCutoff (ht.2.trans_lt hc.1.2)).ne']
    rw [hscale] at hs
    change (β ^ 2 * μ.xi2 t - 1 / xHat ζ.law t ^ 2) * radiusProfile v t -
      (β ^ 2 * μ.xi2 t - 1 / xHat ζ.law t ^ 2) * radiusProfile u t ≤ _
    simp only [div_eq_mul_inv] at hs ⊢
    nlinarith

/-- The ground profile at a contact is identified without Theorem 10.
Chen is used only to supply the physical ground-state limit. -/
theorem contact_ground_profile_unique (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β q : ℝ} (D : ThermodynamicData μ β)
    (hβ : 0 < β) (hq : q ∈ Ioo (0 : ℝ) 1) (hc : Contact μ β q) :
    let u := groundTrial (canonicalMinimizer μ β) hβ hq (le_refl (0 : ℝ))
    (∀ v : RadiusGroundProfile q, radiusFunctional μ u ≤ radiusFunctional μ v) ∧
    D.ground q = radiusFunctional μ u ∧
    (∀ v : RadiusGroundProfile q,
      (∀ w : RadiusGroundProfile q, radiusFunctional μ v ≤ radiusFunctional μ w) →
      ∀ r ∈ Icc (0 : ℝ) q,
        radiusProfile v r = β * xHat (canonicalMinimizer μ β).law r) := by
  dsimp only
  let u := groundTrial (canonicalMinimizer μ β) hβ hq (le_refl (0 : ℝ))
  have hu := contact_groundTrial_minimizes hβ hc hq.1
  obtain ⟨v, hv, hlim, _⟩ := source_ground_limit_unique
    (SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen) μ hq.1
  have he : radiusFunctional μ v = radiusFunctional μ u := le_antisymm (hv u) (hu v)
  refine ⟨hu, (tendsto_nhds_unique (D.ground_limit q hq) hlim).trans he, ?_⟩
  intro w hw r hr
  rw [radius_minimizer_profile_unique μ hq.1 w u hw hu r hr]
  simpa only [CSTAPGroundTrialQuadratic.profile, zero_mul, add_zero] using
    radiusProfile_groundTrial (canonicalMinimizer μ β) hβ hq (le_refl (0 : ℝ))
      (hr.2.trans hq.2.le)

/-- Subag's Lemma 34 variational identity at positive contacts, before
any physical replica reconstruction is invoked. -/
theorem contact_tap_equality (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β q : ℝ} (D : ThermodynamicData μ β)
    (hβ : 0 < β) (hc : Contact μ β q) (hq : 0 < q) :
    D.pressure = tapValue D q := by
  have hqr : q ∈ Ioo (0 : ℝ) 1 := ⟨hq, hc.1.2⟩
  have hg := (contact_ground_profile_unique hChen D hβ hqr hc).2.1
  rw [radiusFunctional_groundTrial] at hg
  have hp := tendsto_nhds_unique D.pressure_limit (hChen μ β hβ.le)
  have hr := tendsto_nhds_unique (D.residual_limit q hqr)
    (hChen (physicalResidualMixture μ q hqr) β hβ.le)
  rw [tapValue, hg, hp, hr]
  exact contact_variational_telescope hβ hc hq

/-- For positive contacts the only remaining physical input is the
lower band approximation, rather than a contact-by-contact tail premise. -/
private theorem positive_contact_multiSamplable_of_bandLower
    (hChen : Chen2013FiniteParisi) {μ : FiniteMixture} {β q : ℝ}
    (D : ThermodynamicData μ β) (hβ : 0 < β)
    (hlower : ExpectedBandLowerApproximation D)
    (hc : Contact μ β q) (hq : 0 < q) : MultiSamplable μ β q :=
  multiSamplable_of_tap_equality D hβ ⟨hq, hc.1.2⟩ hlower
    (LiteratureSubagBandLowerComparison.bandBlockRateComparison μ β)
    (contact_tap_equality hChen D hβ hc hq)

private theorem variationalValue_abs_sub_le (μ ν : FiniteMixture) (β δ : ℝ)
    (hδ : ∀ r ∈ Icc (0 : ℝ) 1, |μ.xi r - ν.xi r| ≤ δ) :
    |variationalValue μ β - variationalValue ν β| ≤ β ^ 2 * δ := by
  let ζ := canonicalMinimizer μ β
  let τ := canonicalMinimizer ν β
  have hA := CSStability.functional_abs_sub_le ζ.law ζ.hasCutoff β μ.xi ν.xi
    (fun r _ => (μ.hasDerivAt_xi r).continuousAt.continuousWithinAt)
    (fun r _ => (ν.hasDerivAt_xi r).continuousAt.continuousWithinAt) δ hδ
  have hB := CSStability.functional_abs_sub_le τ.law τ.hasCutoff β μ.xi ν.xi
    (fun r _ => (μ.hasDerivAt_xi r).continuousAt.continuousWithinAt)
    (fun r _ => (ν.hasDerivAt_xi r).continuousAt.continuousWithinAt) δ hδ
  rw [← ζ.value_eq β μ.xi ζ.hasCutoff, ← ζ.value_eq β ν.xi ζ.hasCutoff] at hA
  rw [← τ.value_eq β μ.xi τ.hasCutoff, ← τ.value_eq β ν.xi τ.hasCutoff] at hB
  have hμ := canonicalMinimizer_isMinimizer μ β τ
  have hν := canonicalMinimizer_isMinimizer ν β ζ
  change |ζ.value β μ.xi - τ.value β ν.xi| ≤ _
  exact abs_le.mpr ⟨by linarith [(abs_le.mp hA).1], by linarith [(abs_le.mp hB).2]⟩

private theorem residual_covariance_error (μ : FiniteMixture) {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |μ.xi t - (physicalResidualMixture μ q hq).xi t| ≤
      2 * (CSCompactAttainment.mixtureLipschitzConstant μ : ℝ) * q + |μ.xi1 q| := by
  let L : ℝ := CSCompactAttainment.mixtureLipschitzConstant μ
  let u := q + (1 - q) * t
  have hL : 0 ≤ L := NNReal.coe_nonneg _
  have hu : u ∈ Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor
    · exact add_nonneg hq.1.le (mul_nonneg (sub_pos.mpr hq.2).le ht.1)
    · nlinarith [mul_nonneg (sub_pos.mpr hq.2).le (sub_nonneg.mpr ht.2)]
  have hud : u - t = q * (1 - t) := by dsimp [u]; ring
  have hdt : q * (1 - t) ≤ q := by nlinarith [mul_nonneg hq.1.le ht.1]
  have hA := (CSCompactAttainment.mixture_xi_lipschitzOn μ).dist_le_mul u hu t ht
  rw [Real.dist_eq, Real.dist_eq, hud,
    abs_of_nonneg (mul_nonneg hq.1.le (sub_nonneg.mpr ht.2))] at hA
  have hA' : |μ.xi u - μ.xi t| ≤ L * q :=
    hA.trans (mul_le_mul_of_nonneg_left hdt hL)
  have hB := (CSCompactAttainment.mixture_xi_lipschitzOn μ).dist_le_mul
    q ⟨hq.1.le, hq.2.le⟩ 0 ⟨le_rfl, zero_le_one⟩
  have hB' : |μ.xi q| ≤ L * q := by
    simpa only [Real.dist_eq, μ.xi_zero, sub_zero, abs_of_pos hq.1] using hB
  have hp : (1 - q) * t ≤ 1 := by nlinarith [ht.2, mul_nonneg hq.1.le ht.1]
  have hC : |(1 - q) * μ.xi1 q * t| ≤ |μ.xi1 q| := by
    rw [abs_mul, abs_mul, abs_of_pos (sub_pos.mpr hq.2), abs_of_nonneg ht.1]
    calc
      _ = |μ.xi1 q| * ((1 - q) * t) := by ring
      _ ≤ |μ.xi1 q| * 1 := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
      _ = _ := mul_one _
  rw [abs_sub_comm]
  change |(CSTAPTelescope.residualMixture μ hq).xi t - μ.xi t| ≤ _
  rw [CSTAPTelescope.residualMixture_xi]
  calc
    _ = |((μ.xi u - μ.xi t) - μ.xi q) - (1 - q) * μ.xi1 q * t| := by
      congr 1
      dsimp [u]
      ring
    _ ≤ |μ.xi u - μ.xi t| + |μ.xi q| + |(1 - q) * μ.xi1 q * t| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ _ := by change _ ≤ 2 * L * q + |μ.xi1 q|; linarith

private theorem ground_nonneg (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β q : ℝ} (D : ThermodynamicData μ β)
    (hq : q ∈ Ioo (0 : ℝ) 1) : 0 ≤ D.ground q := by
  obtain ⟨u, _, hlim, _⟩ := source_ground_limit_unique
    (SourceLiteratureGroundStateExtraction.chenSenFiniteGround hChen) μ hq.1
  rw [tendsto_nhds_unique (D.ground_limit q hq) hlim]
  apply div_nonneg (add_nonneg ?_ ?_) (by norm_num : (0 : ℝ) ≤ 2)
  · apply intervalIntegral.integral_nonneg_of_ae_restrict hq.1.le
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      (volume.restrict (Icc 0 q)).ae_ne (0 : ℝ)] with t ht ht0
    exact mul_nonneg (μ.xi2_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0))).le
      (radiusProfile_pos hq.1.le u ht).le
  · exact intervalIntegral.integral_nonneg hq.1.le
      (fun t ht => inv_nonneg.mpr (radiusProfile_pos hq.1.le u ht).le)

private theorem small_overlap_tap_lower (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β) (hβ : 0 < β)
    {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∃ q : ℝ, q ∈ Ioo (0 : ℝ) 1 ∧ q < a ∧ -ε < tapValue D q - D.pressure := by
  let L : ℝ := CSCompactAttainment.mixtureLipschitzConstant μ
  let g : ℝ → ℝ := fun q => Real.log (1 - q) / 2 - β ^ 2 * (2 * L * q + |μ.xi1 q|)
  have hg : ContinuousAt g 0 :=
    (((continuousAt_const.sub continuousAt_id).log (by norm_num)).div_const 2).sub
      (continuousAt_const.mul ((continuousAt_id.const_mul (2 * L)).add
        (μ.hasDerivAt_xi1 0).continuousAt.abs))
  have hg0 : g 0 = 0 := by simp [g, CSTAPTelescope.xi1_zero]
  have hev : ∀ᶠ q in 𝓝 (0 : ℝ), -ε < g q := hg.eventually
    (lt_mem_nhds (by rw [hg0]; linarith))
  obtain ⟨d, hd, hgood⟩ := Metric.eventually_nhds_iff.mp hev
  let q := min (d / 2) (min (a / 2) (1 / 2))
  have hq : q ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨lt_min (half_pos hd) (lt_min (half_pos ha) (by norm_num)), ?_⟩
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by norm_num)
  have hqa : q < a := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hqd : dist q 0 < d := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hq.1]
    exact (min_le_left _ _).trans_lt (by linarith)
  have hp := tendsto_nhds_unique D.pressure_limit (hChen μ β hβ.le)
  have hr := tendsto_nhds_unique (D.residual_limit q hq)
    (hChen (physicalResidualMixture μ q hq) β hβ.le)
  have he := variationalValue_abs_sub_le μ (physicalResidualMixture μ q hq) β
    (2 * L * q + |μ.xi1 q|) (residual_covariance_error μ hq)
  rw [← hp, ← hr] at he
  refine ⟨q, hq, hqa, ?_⟩
  have hqg := hgood hqd
  have hgn := mul_nonneg hβ.le (ground_nonneg hChen D hq)
  dsimp only [g] at hqg
  unfold tapValue
  linarith [(abs_le.mp he).2]

private theorem block_measurable {N k : ℕ} (q ρ : ℝ) :
    MeasurableSet (overlapBlock (N := N) (k := k) q ρ) := by
  simp only [overlapBlock, Set.ofPred_forall]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => ?_
  exact (isOpen_lt (by unfold overlap; fun_prop) continuous_const).measurableSet

private theorem block_log_integrable (N k : ℕ) (μ : FiniteMixture)
    (β q ρ : ℝ) : Integrable
      (fun J => Real.log (max (conditionalBlockProbability N k μ β q ρ J)
        (Real.exp (-(N : ℝ))))) (disorderLaw N μ.maxDegree) := by
  have hf : Measurable (conditionalBlockProbability N k μ β q ρ) :=
    (Kernel.measurable_coe _ (block_measurable q ρ)).ennreal_toReal
  have ha := Real.exp_pos (-(N : ℝ))
  have ha1 : Real.exp (-(N : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg N))
  refine (integrable_const (N : ℝ)).mono'
    ((hf.max measurable_const).log.aestronglyMeasurable) (.of_forall fun J => ?_)
  have hlo := Real.log_le_log ha
    (le_max_right (conditionalBlockProbability N k μ β q ρ J) _)
  rw [Real.log_exp] at hlo
  have hhi : Real.log (max (conditionalBlockProbability N k μ β q ρ J)
      (Real.exp (-(N : ℝ)))) ≤ 0 :=
    Real.log_nonpos (ha.le.trans (le_max_right _ _)) (max_le measureReal_le_one ha1)
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨hlo, by linarith [Nat.cast_nonneg (α := ℝ) N]⟩

private theorem block_rate_le_zeroBlock (N k : ℕ) (μ : FiniteMixture)
    (β q η ρ : ℝ) (hηρ : η + |q| ≤ ρ) :
    truncatedQuenchedBlockRate N k μ β q η ≤
      truncatedQuenchedBlockRate N k μ β 0 ρ := by
  have hsub : overlapBlock (N := N) (k := k) q η ⊆ overlapBlock 0 ρ := by
    intro σ hσ i j hij
    have ht : |overlap (σ i) (σ j)| ≤
        |overlap (σ i) (σ j) - q| + |q| := by
      simpa only [sub_add_cancel] using abs_add_le (overlap (σ i) (σ j) - q) q
    simpa only [sub_zero] using
      ht.trans_lt ((add_lt_add_of_lt_of_le (hσ i j hij) le_rfl).trans_le hηρ)
  unfold truncatedQuenchedBlockRate
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply integral_mono (block_log_integrable N k μ β q η)
    (block_log_integrable N k μ β 0 ρ)
  intro J
  apply Real.log_le_log
    ((Real.exp_pos (-(N : ℝ))).trans_le (le_max_right _ _))
  exact max_le_max (measureReal_mono hsub) le_rfl

private theorem tap_gap_lt_blockRate_add {μ : FiniteMixture} {β q : ℝ}
    (D : ThermodynamicData μ β) (hβ : 0 < β) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hlower : ExpectedBandLowerApproximation D)
    (n : ℕ) (hn : 1 ≤ n) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, tapValue D q - D.pressure <
      truncatedQuenchedBlockRate N n μ β q ρ / (n : ℝ) + ε := by
  let t : ℝ := ε / 4
  have ht : 0 < t := by dsimp [t]; positivity
  have h24 := LiteratureSubagProposition24Proof.proposition24 μ hβ ⟨hq.1.le, hq.2⟩
  obtain ⟨δ₀, hδ₀, ρ₀, hρ₀, K₁, hc⟩ :=
    LiteratureSubagBandLowerComparison.bandBlockRateComparison μ β q hq h24 n hn ρ t hρ ht
  obtain ⟨δ, hδ, hδsmall, η, hη, hηsmall, K₂, hl⟩ :=
    hlower q hq t ht δ₀ (min ρ₀ ρ) hδ₀ (lt_min hρ₀ hρ)
  let k := n * (max K₁ K₂ + 1)
  have hkn : n ∣ k := ⟨max K₁ K₂ + 1, rfl⟩
  have hk₁ : K₁ ≤ k := by dsimp [k]; nlinarith [le_max_left K₁ K₂]
  have hk₂ : K₂ ≤ k := by dsimp [k]; nlinarith [le_max_right K₁ K₂]
  have henergy := ((D.ground_limit q hq).const_mul β).sub D.pressure_limit
  have hevent : ∀ᶠ N : ℕ in atTop,
      β * D.ground q - D.pressure - t <
        β * expectedCenterGroundEnergy N μ q - quenchedPressure N μ β :=
    henergy.eventually (lt_mem_nhds (by linarith))
  filter_upwards [hc δ hδ hδsmall η hη hηsmall k hk₁ hkn,
    hl k hk₂, hevent, eventually_gt_atTop 0] with N hcN hlN heN hN
  let : NeZero N := ⟨hN.ne'⟩
  obtain ⟨m, hm⟩ := exists_norm_eq (Vector N) (Real.sqrt_nonneg ((N : ℝ) * q))
  have hm' : ‖m‖ ^ 2 = (N : ℝ) * q := by
    rw [hm, Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) hq.1.le)]
  have hc' := hcN m hm'
  have hl' := hlN m hm'
  have htt : 3 * t < ε := by dsimp [t]; linarith
  unfold tapValue
  linarith

/-- The all-temperature zero-contact rate follows from the positive-overlap
lower band approximation by letting its center radius tend to zero. -/
theorem zero_blockRate_tendsto_of_bandLower (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β) (hβ : 0 < β)
    (hlower : ExpectedBandLowerApproximation D) (k : ℕ) (hk : 1 ≤ k)
    {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun N => truncatedQuenchedBlockRate N k μ β 0 ρ) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hkr : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  let t := ε / (3 * (k : ℝ))
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨q, hq, hqρ, hqt⟩ := small_overlap_tap_lower hChen D hβ (half_pos hρ) ht
  filter_upwards [tap_gap_lt_blockRate_add D hβ hq hlower k hk (ρ / 2)
    (half_pos hρ) t ht] with N hN
  have hm := block_rate_le_zeroBlock N k μ β q (ρ / 2) ρ
    (by rw [abs_of_pos hq.1]; linarith)
  have hn := (truncatedQuenchedBlockRate_bounds N k μ β 0 ρ).2
  have hlow : -(2 * t) < truncatedQuenchedBlockRate N k μ β 0 ρ / (k : ℝ) := by
    have hd := div_le_div_of_nonneg_right hm hkr.le
    linarith
  have hlow' := (lt_div_iff₀ hkr).mp hlow
  rw [Real.dist_eq, sub_zero, abs_of_nonpos hn]
  dsimp only [t] at hlow'
  have he : 2 * (ε / (3 * (k : ℝ))) * (k : ℝ) = 2 * ε / 3 := by
    field_simp
  nlinarith

/-- The exact physical zero-contact lower-tail estimate, throughout the
temperature range, reduced to the single remaining lower band estimate. -/
theorem zero_blockLowerTail_tendsto_of_bandLower (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β) (hβ : 0 < β)
    (hlower : ExpectedBandLowerApproximation D) (k : ℕ) (hk : 1 ≤ k)
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    Tendsto (fun N => blockLowerTailProbability N k μ β 0 ρ ε) atTop (𝓝 0) :=
  (truncatedQuenchedBlockRate_tendsto_iff_lowerTail k μ β 0 ρ).mp
    (zero_blockRate_tendsto_of_bandLower hChen D hβ hlower k hk hρ) ε hε

/-- The exact lower-tail input of the previous Theorem 10 reduction,
simultaneously for zero and positive contacts, follows from lower bands. -/
theorem contact_blockLowerTail_tendsto_of_bandLower (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β q : ℝ} (D : ThermodynamicData μ β) (hβ : 0 < β)
    (hlower : ExpectedBandLowerApproximation D) (hc : Contact μ β q)
    (k : ℕ) (hk : 1 ≤ k) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    Tendsto (fun N => blockLowerTailProbability N k μ β q ρ ε) atTop (𝓝 0) := by
  by_cases hq : q = 0
  · subst q
    exact zero_blockLowerTail_tendsto_of_bandLower hChen D hβ hlower k hk hρ hε
  have hqp := lt_of_le_of_ne hc.1.1 (Ne.symm hq)
  apply (truncatedQuenchedBlockRate_tendsto_iff_lowerTail k μ β q ρ).mp ?_ ε hε
  apply Metric.tendsto_nhds.mpr
  intro η hη
  have hkr : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  let t := η / (2 * (k : ℝ))
  have ht : 0 < t := by dsimp [t]; positivity
  have heq := contact_tap_equality hChen D hβ hc hqp
  filter_upwards [tap_gap_lt_blockRate_add D hβ ⟨hqp, hc.1.2⟩ hlower k hk ρ hρ t ht]
    with N hN
  have hgap : tapValue D q - D.pressure = 0 := sub_eq_zero.mpr heq.symm
  rw [hgap] at hN
  have hlow : -t < truncatedQuenchedBlockRate N k μ β q ρ / (k : ℝ) := by linarith
  have hlow' := (lt_div_iff₀ hkr).mp hlow
  have hn := (truncatedQuenchedBlockRate_bounds N k μ β q ρ).2
  have he : t * (k : ℝ) = η / 2 := by dsimp [t]; field_simp
  rw [Real.dist_eq, sub_zero, abs_of_nonpos hn]
  nlinarith

/-- The complete original forward interface, with all contact-specific
probability assumptions replaced by the lower band approximation alone. -/
theorem theorem10Forward_of_bandLower (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β) (hβ : 0 < β)
    (hlower : ExpectedBandLowerApproximation D) : Theorem10Forward μ β := by
  refine ⟨hβ, fun q hc => ?_⟩
  by_cases hq : q = 0
  · subst q
    exact multiSamplable_of_truncatedQuenchedBlockRate (by norm_num)
      (fun k hk _ hρ => zero_blockRate_tendsto_of_bandLower hChen D hβ hlower k hk hρ)
  · exact positive_contact_multiSamplable_of_bandLower hChen D hβ hlower hc
      (lt_of_le_of_ne hc.1.1 (Ne.symm hq))

private theorem bands_of_bandLower {μ : FiniteMixture} {β : ℝ}
    (D : ThermodynamicData μ β) (hlower : ExpectedBandLowerApproximation D) :
    SourceMainTheoremsReducedFinal.SubagBandApproximations μ β :=
  (SourceMainTheoremsReducedFinal.subagBandApproximations_iff D).mpr
    ⟨LiteratureSubagBandUpperFinal.expectedBandUpperApproximation D, hlower⟩

namespace Endpoints

/-- `thm:th-contact(1)` with the separate Theorem 10 input removed.
The lower band approximation is the only remaining physical estimate. -/
theorem contact_iff_multiSamplable (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β) (hβ : 0 < β)
    (hlower : ExpectedBandLowerApproximation D)
    {q : ℝ} (hq : q ∈ Ico (0 : ℝ) 1) :
    MultiSamplable μ β q ↔
      CSStructure.potential μ β (canonicalMinimizer μ β).law q = 0 :=
  SourceMainTheoremsReducedFinal.contact_iff_multiSamplable_of_chen_and_bands
    hChen D (theorem10Forward_of_bandLower hChen D hβ hlower) hq
    (bands_of_bandLower D hlower)

/-- `thm:th-contact(2)`, ground profile, with all Subag and band
hypotheses removed. This conclusion uses only Chen. -/
theorem contact_ground_profile_unique (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β q : ℝ} (D : ThermodynamicData μ β)
    (hβ : 0 < β) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hV : CSStructure.potential μ β (canonicalMinimizer μ β).law q = 0) :
    let u := groundTrial (canonicalMinimizer μ β) hβ hq (le_refl (0 : ℝ))
    (∀ v : RadiusGroundProfile q, radiusFunctional μ u ≤ radiusFunctional μ v) ∧
    D.ground q = radiusFunctional μ u ∧
    (∀ v : RadiusGroundProfile q,
      (∀ w : RadiusGroundProfile q, radiusFunctional μ v ≤ radiusFunctional μ w) →
      ∀ r ∈ Icc (0 : ℝ) q,
        radiusProfile v r = β * xHat (canonicalMinimizer μ β).law r) :=
  LiteratureSubagTheorem10Proof2.contact_ground_profile_unique hChen D hβ hq
    ((contact_iff_firstVariation_zero μ β q).mpr
      ⟨⟨hq.1.le, hq.2⟩, neg_eq_zero.mp hV⟩)

/-- `prop:th-structure` with the separate Theorem 10 input removed. -/
theorem strict_oneStep_structure (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β x Q : ℝ} (h : SphericalTAPCertificate.Certificate μ β x Q)
    (D : ThermodynamicData μ β) (hlower : ExpectedBandLowerApproximation D) :
    StrictOneStepConclusions h D :=
  SourceMainTheoremsReducedFinal.strict_oneStep_structure_of_chen_and_bands
    hChen h D (theorem10Forward_of_bandLower hChen D h.beta_pos hlower)
    (bands_of_bandLower D hlower)

/-- The full-range `thm:th-subag(1)` endpoint, including zero, without
the separate zero-contact lower-tail assumption. -/
theorem source_subag_tap (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β : ℝ} (D : ThermodynamicData μ β) (hβ : 0 < β)
    (hlower : ExpectedBandLowerApproximation D)
    {q : ℝ} (hq : q ∈ Ico (0 : ℝ) 1) :
    SourceSubagReplicaCriterion.sourceTAPValue D q ≤ D.pressure ∧
      (D.pressure = SourceSubagReplicaCriterion.sourceTAPValue D q ↔
        MultiSamplable μ β q) :=
  SourceMainTheoremsReducedFinal.source_subag_tap_of_chen_and_bands D
    (fun _ k hk _ hρ _ hε =>
      zero_blockLowerTail_tendsto_of_bandLower hChen D hβ hlower k (by omega) hρ hε)
    hq hβ (bands_of_bandLower D hlower)

/-- The full-range `thm:th-subag(2)` endpoint, including zero, without
the separate zero-contact lower-tail assumption. -/
theorem source_replica_criterion (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β q : ℝ} (hβ : 0 < β)
    (hlower : ExpectedBandLowerApproximation
      (LiteratureSubagRemark25Final.chenThermodynamicData hChen μ hβ.le))
    (hq : q ∈ Ico (0 : ℝ) 1) :
    (∀ k : ℕ, 1 ≤ k → ∀ ρ : ℝ, 0 < ρ →
      limsup (fun N : ℕ => SourceSubagReplicaCriterion.replicaLogRate N k μ β q ρ)
        atTop = 0) ↔ MultiSamplable μ β q := by
  let D := LiteratureSubagRemark25Final.chenThermodynamicData hChen μ hβ.le
  exact SourceMainTheoremsReducedFinal.source_replica_criterion_of_chen_and_bands hChen
    (fun _ k hk _ hρ _ hε =>
      zero_blockLowerTail_tendsto_of_bandLower hChen D hβ hlower k (by omega) hρ hε)
    hq hβ (bands_of_bandLower D hlower)

end Endpoints

end SlowEquilibration.LiteratureSubagTheorem10Proof2

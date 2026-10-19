-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSTAPTelescope
public import SlowEquilibration.SourceGroundProfileUniqueness
public import SlowEquilibration.SourceSubagReplicaCriterion
public import SlowEquilibration.CSCDFIntegration
public import SlowEquilibration.SphericalTAPResidualMargin
public import SlowEquilibration.LatitudeGroundTrialContact
public import SlowEquilibration.SphericalOnePointContactSaddle

/-!
General ground-profile variations and the contact theorem of manuscript
`thm:th-contact`, followed by `lem:th-replica-exclusion` and the static
consequences of a strict one-step certificate. The variational profiles
are arbitrary admissible measures; cited thermodynamic results remain
explicit hypotheses.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceGeneralContactTheorem

open MeasureTheory Set Filter ProbabilityTheory CrisantiSommers
open CSTAPGroundTrialQuadratic SourceGroundProfileUniqueness
open SourceLiteratureParisi SourceLiteratureGroundState
open SourceLiteratureGroundStateCenterBridge SourceLiteratureGroundStateRadialCoefficients
open LiteratureSubagTAP LiteratureSubagContact LiteratureSubagPhysicalDefinitions
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Telescope

open MeasureTheory Set CrisantiSommers

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The manuscript's truncated affine residual map. -/
private def residualMap (q r : ℝ) : ℝ := max 0 ((r - q) / (1 - q))

private theorem residualMap_continuous (q : ℝ) : Continuous (residualMap q) := by
  unfold residualMap
  fun_prop

private theorem residualMap_mem {q Q r : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Icc (0 : ℝ) Q) :
    residualMap q r ∈ Icc (0 : ℝ) (residualMap q Q) := by
  refine ⟨le_max_left _ _, max_le_max_left 0 ?_⟩
  exact div_le_div_of_nonneg_right (sub_le_sub_right hr.2 q) (by linarith [hq.2])

private theorem residualMap_lt_one {q Q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hQ : Q < 1) : residualMap q Q < 1 := by
  apply max_lt (by norm_num)
  rw [div_lt_one (by linarith [hq.2])]
  linarith

/-- The actual pushforward measure, valid for every admissible law. -/
private def residualTrial (ζ : Admissible) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) : Admissible where
  law := ζ.law.map (residualMap q)
  probability := (Measure.isProbabilityMeasure_map_iff
    (residualMap_continuous q).measurable.aemeasurable).mpr inferInstance
  cutoff_exists := by
    refine ⟨residualMap q ζ.cutoff, le_max_left _ _,
      residualMap_lt_one hq ζ.hasCutoff.2.1, ?_⟩
    exact (ae_map_iff (residualMap_continuous q).measurable.aemeasurable
      measurableSet_Icc).mpr
        (ζ.hasCutoff.2.2.mono (fun r hr => residualMap_mem hq hr))

private theorem residualTrial_hasCutoff (ζ : Admissible) {q Q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (hQ : HasCutoff ζ.law Q) :
    HasCutoff (residualTrial ζ hq).law (residualMap q Q) := by
  refine ⟨le_max_left _ _, residualMap_lt_one hq hQ.2.1, ?_⟩
  exact (ae_map_iff (residualMap_continuous q).measurable.aemeasurable
    measurableSet_Icc).mpr
      (hQ.2.2.mono (fun r hr => residualMap_mem hq hr))

/-- The defining distribution-function identity for the residual law. -/
private theorem residualTrial_distribution (ζ : Admissible) {q t : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (ht : 0 ≤ t) :
    (residualTrial ζ hq).law (Icc 0 t) = ζ.law (Icc 0 (q + (1 - q) * t)) := by
  rw [show (residualTrial ζ hq).law = ζ.law.map (residualMap q) from rfl,
    Measure.map_apply (residualMap_continuous q).measurable measurableSet_Icc]
  apply measure_congr
  filter_upwards [ζ.hasCutoff.2.2] with r hr
  simp only [mem_preimage, mem_Icc, residualMap]
  have hs : 0 < 1 - q := by linarith [hq.2]
  have he : max 0 ((r - q) / (1 - q)) ≤ t ↔ r ≤ q + (1 - q) * t := by
    rw [max_le_iff, and_iff_right ht, div_le_iff₀ hs]
    constructor <;> intro h <;> nlinarith
  simp only [le_max_left, true_and, he, hr.1]

/-- In particular, all mass below the overlap becomes the atom at zero. -/
private theorem residualTrial_atom_zero (ζ : Admissible) {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) :
    (residualTrial ζ hq).law {0} = ζ.law (Icc 0 q) := by
  simpa using residualTrial_distribution ζ hq (t := 0) le_rfl

private theorem residual_kernel {q t r : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (ht : 0 ≤ t) :
    (1 - q) * (1 - max t (residualMap q r)) =
      1 - max (q + (1 - q) * t) r := by
  have hs : 0 < 1 - q := by linarith [hq.2]
  have he : max t (residualMap q r) = max t ((r - q) / (1 - q)) := by
    rw [residualMap, ← max_assoc, max_eq_left ht]
  rw [he]
  by_cases h : (r - q) / (1 - q) ≤ t
  · rw [max_eq_left h, max_eq_left]
    · ring
    · rw [div_le_iff₀ hs] at h
      nlinarith
  · have ht' : t ≤ (r - q) / (1 - q) := (lt_of_not_ge h).le
    rw [max_eq_right ht', max_eq_right]
    · field_simp
      ring
    · rw [le_div_iff₀ hs] at ht'
      nlinarith

/-- The integrated distribution profile transports exactly under the
residual map, including when its atom at zero has zero mass. -/
private theorem residual_xHat_scale (ζ : Admissible) {q t : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (ht : 0 ≤ t) :
    (1 - q) * xHat (residualTrial ζ hq).law t =
      xHat ζ.law (q + (1 - q) * t) := by
  unfold xHat
  rw [show (residualTrial ζ hq).law = ζ.law.map (residualMap q) from rfl,
    integral_map (residualMap_continuous q).measurable.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun r : ℝ => 1 - max t r)
        (ζ.law.map (residualMap q))), ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun r => residual_kernel hq ht)

/-- Rescaled entropy integral at any original cutoff above the overlap. -/
private theorem residual_inverse_integral (ζ : Admissible) {q Q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (hqQ : q ≤ Q) :
    (∫ t in (0 : ℝ)..((Q - q) / (1 - q)),
      (xHat (residualTrial ζ hq).law t)⁻¹) =
        ∫ v in q..Q, (xHat ζ.law v)⁻¹ := by
  have hs : 0 < 1 - q := by linarith [hq.2]
  have hQ' : 0 ≤ (Q - q) / (1 - q) := div_nonneg (sub_nonneg.mpr hqQ) hs.le
  have hcongr : ∀ t ∈ uIcc (0 : ℝ) ((Q - q) / (1 - q)),
      (xHat (residualTrial ζ hq).law t)⁻¹ =
        (1 - q) * (xHat ζ.law ((1 - q) * t + q))⁻¹ := by
    intro t ht
    rw [uIcc_of_le hQ'] at ht
    rw [add_comm ((1 - q) * t) q, ← residual_xHat_scale ζ hq ht.1,
      mul_inv, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  have hsub := intervalIntegral.integral_comp_mul_add
    (f := fun v => (xHat ζ.law v)⁻¹) (a := 0) (b := (Q - q) / (1 - q)) hs.ne' q
  have hend : (1 - q) * ((Q - q) / (1 - q)) + q = Q := by
    field_simp
    ring
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul,
    hsub, smul_eq_mul, mul_zero, zero_add, hend, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]

/-- The entropy terms of the CS functional split at every positive overlap. -/
private theorem residual_entropy (ζ : Admissible) {q Q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (hQ : HasCutoff ζ.law Q) (hqQ : q ≤ Q) :
    (∫ t in (0 : ℝ)..residualMap q Q,
        (xHat (residualTrial ζ hq).law t)⁻¹) + Real.log (1 - residualMap q Q) =
      (∫ v in q..Q, (xHat ζ.law v)⁻¹) + Real.log (1 - Q) - Real.log (1 - q) := by
  have hs : 0 < 1 - q := by linarith [hq.2]
  have hmap : residualMap q Q = (Q - q) / (1 - q) :=
    max_eq_right (div_nonneg (sub_nonneg.mpr hqQ) hs.le)
  rw [hmap, residual_inverse_integral ζ hq hqQ]
  have he : 1 - (Q - q) / (1 - q) = (1 - Q) / (1 - q) := by
    field_simp
    ring
  rw [he, Real.log_div (by linarith [hQ.2.1]) hs.ne']
  ring

private theorem xi2_continuous (μ : FiniteMixture) : Continuous μ.xi2 :=
  continuous_iff_continuousAt.mpr (fun v => (μ.hasDerivAt_xi2 v).continuousAt)

private theorem integrable_of_cutoff (ζ : Admissible) {f : ℝ → ℝ}
    (hf : Continuous f) : Integrable f ζ.law := by
  have hi := (hf.continuousOn : ContinuousOn f (Icc 0 ζ.cutoff)).integrableOn_compact
    isCompact_Icc (μ := ζ.law)
  simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem ζ.hasCutoff.2.2] using hi

private theorem energy_kernel_integrable (μ : FiniteMixture) (ζ : Admissible)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun p : ℝ × ℝ => μ.xi2 p.1 * (1 - max p.1 p.2))
      ((volume.restrict (Ioc 0 q)).prod ζ.law) := by
  have hi := ((xi2_continuous μ).norm.intervalIntegrable (μ := volume) 0 q).1.comp_fst ζ.law
  have hf : Continuous (fun p : ℝ × ℝ => μ.xi2 p.1 * (1 - max p.1 p.2)) :=
    ((xi2_continuous μ).comp continuous_fst).mul
      (continuous_const.sub (continuous_fst.max continuous_snd))
  apply hi.mono' hf.aestronglyMeasurable
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hf.norm.measurable
    (((xi2_continuous μ).norm.comp continuous_fst).measurable))).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  filter_upwards [ζ.hasCutoff.2.2] with r hr
  have hk0 : 0 ≤ 1 - max t r := by
    exact sub_nonneg.mpr (max_le (ht.2.trans hq.2.le) (hr.2.trans ζ.hasCutoff.2.1.le))
  have hk1 : 1 - max t r ≤ 1 := by
    linarith [le_max_left t r, ht.1]
  rw [norm_mul, Real.norm_eq_abs (1 - max t r), abs_of_nonneg hk0]
  exact mul_le_of_le_one_right (norm_nonneg _) hk1

private theorem energy_kernel_fubini (μ : FiniteMixture) (ζ : Admissible)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    (∫ v in (0 : ℝ)..q, μ.xi2 v * xHat ζ.law v) =
      ∫ r, (∫ v in (0 : ℝ)..q, μ.xi2 v * (1 - max v r)) ∂ζ.law := by
  have hi := energy_kernel_integrable μ ζ hq
  rw [← uIoc_of_le hq.1.le] at hi
  have hh := intervalIntegral_integral_swap (f := fun v r => μ.xi2 v * (1 - max v r)) hi
  simpa only [Function.uncurry_def, integral_const_mul, xHat] using hh

private theorem integral_xi2_triangular (μ : FiniteMixture) (r : ℝ) :
    (∫ v in (0 : ℝ)..r, (r - v) * μ.xi2 v) = μ.xi r := by
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun v => (r - v) * μ.xi1 v + μ.xi v)
    (f' := fun v => (r - v) * μ.xi2 v)
    (a := 0) (b := r)
    (fun v _ => by
      convert (((hasDerivAt_id v).const_sub r).mul (μ.hasDerivAt_xi1 v)).add
        (μ.hasDerivAt_xi v) using 1
      · funext w
        rfl
      · simp only [id_eq]
        ring)
    (((continuous_const.sub continuous_id).mul (xi2_continuous μ)).intervalIntegrable 0 r)
  simpa only [sub_self, zero_mul, zero_add, sub_zero, CSTAPTelescope.xi1_zero,
    mul_zero, FiniteMixture.xi_zero] using hh

/-- The pointwise kernel decomposition behind the energy telescope. -/
private theorem energy_kernel_identity (μ : FiniteMixture) {q r : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (hr : 0 ≤ r) :
    (∫ v in (0 : ℝ)..q, μ.xi2 v * (1 - max v r)) -
      (CSTAPTelescope.residualMixture μ hq).xi (residualMap q r) =
        μ.xi q + (1 - q) * μ.xi1 q - μ.xi r := by
  by_cases hrq : r ≤ q
  · have hk := weighted_kernel_identity (xi2_continuous μ).continuousOn hr hrq
    have htri := integral_xi2_triangular μ r
    have hfull := CSTAPTelescope.integral_xi2_mul_one_sub μ 0 q
    have hmap : residualMap q r = 0 := by
      apply max_eq_left
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hrq) (by linarith [hq.2])
    rw [hmap, FiniteMixture.xi_zero, sub_zero]
    have heq : (∫ v in (0 : ℝ)..q, μ.xi2 v * (1 - max v r)) =
        ∫ v in (0 : ℝ)..q, (1 - max v r) * μ.xi2 v := by
      apply intervalIntegral.integral_congr
      intro v _
      ring
    rw [heq, hk, htri]
    have hfull' : (∫ v in (0 : ℝ)..q, (1 - v) * μ.xi2 v) =
        μ.xi1 q * (1 - q) + μ.xi q := by
      simp only [CSTAPTelescope.xi1_zero, zero_mul, FiniteMixture.xi_zero,
        add_zero, sub_zero] at hfull
      convert hfull using 1
      apply intervalIntegral.integral_congr
      intro v _
      ring
    rw [hfull']
    ring
  · have hqr : q ≤ r := (lt_of_not_ge hrq).le
    have hmap : residualMap q r = (r - q) / (1 - q) :=
      max_eq_right (div_nonneg (sub_nonneg.mpr hqr) (by linarith [hq.2]))
    have heq : (∫ v in (0 : ℝ)..q, μ.xi2 v * (1 - max v r)) =
        (1 - r) * μ.xi1 q := by
      rw [intervalIntegral.integral_congr (g := fun v => (1 - r) * μ.xi2 v)]
      · rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_eq_sub_of_hasDerivAt
            (f := μ.xi1) (fun v _ => μ.hasDerivAt_xi1 v)
            ((xi2_continuous μ).intervalIntegrable 0 q), CSTAPTelescope.xi1_zero, sub_zero]
      · intro v hv
        rw [uIcc_of_le hq.1.le] at hv
        simp only
        rw [max_eq_right (hv.2.trans hqr)]
        ring
    rw [heq, hmap, CSTAPTelescope.residualMixture_xi]
    have ha : q + (1 - q) * ((r - q) / (1 - q)) = r := by
      field_simp [(sub_pos.mpr hq.2).ne']
      ring
    rw [ha]
    field_simp [(sub_pos.mpr hq.2).ne']
    ring

/-- Exact energy decomposition for an arbitrary probability law. -/
private theorem residual_energy (μ : FiniteMixture) (ζ : Admissible) {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) :
    μ.xi 1 - (∫ r, μ.xi r ∂ζ.law) =
      (∫ v in (0 : ℝ)..q, μ.xi2 v * xHat ζ.law v) +
        ((CSTAPTelescope.residualMixture μ hq).xi 1 -
          ∫ t, (CSTAPTelescope.residualMixture μ hq).xi t ∂(residualTrial ζ hq).law) := by
  let ψ := CSTAPTelescope.residualMixture μ hq
  have hψ : Continuous ψ.xi :=
    continuous_iff_continuousAt.mpr (fun v => (ψ.hasDerivAt_xi v).continuousAt)
  have hξ : Continuous μ.xi :=
    continuous_iff_continuousAt.mpr (fun v => (μ.hasDerivAt_xi v).continuousAt)
  have hker : Integrable (fun r => ∫ v in (0 : ℝ)..q, μ.xi2 v * (1 - max v r)) ζ.law := by
    simpa only [intervalIntegral.integral_of_le hq.1.le] using
      (energy_kernel_integrable μ ζ hq).integral_prod_right
  have hres : Integrable (fun r => ψ.xi (residualMap q r)) ζ.law :=
    integrable_of_cutoff ζ (hψ.comp (residualMap_continuous q))
  have hxi := integrable_of_cutoff ζ hξ
  have he := integral_congr_ae
    (ζ.hasCutoff.2.2.mono (fun r hr => energy_kernel_identity μ hq hr.1))
  change (∫ r, (∫ v in (0 : ℝ)..q, μ.xi2 v * (1 - max v r)) -
      ψ.xi (residualMap q r) ∂ζ.law) = _ at he
  rw [integral_sub hker hres, integral_sub (integrable_const _) hxi,
    integral_const, probReal_univ, one_smul] at he
  rw [show (residualTrial ζ hq).law = ζ.law.map (residualMap q) from rfl,
    integral_map (residualMap_continuous q).measurable.aemeasurable
      hψ.aestronglyMeasurable, energy_kernel_fubini μ ζ hq,
    CSTAPTelescope.residualMixture_xi]
  have hone : q + (1 - q) * 1 = 1 := by ring
  rw [hone]
  change (∫ r, (∫ v in (0 : ℝ)..q, μ.xi2 v * (1 - max v r)) ∂ζ.law) -
    (∫ r, ψ.xi (residualMap q r) ∂ζ.law) =
      μ.xi q + (1 - q) * μ.xi1 q - (∫ r, μ.xi r ∂ζ.law) at he
  change μ.xi 1 - (∫ r, μ.xi r ∂ζ.law) =
    (∫ r, (∫ v in (0 : ℝ)..q, μ.xi2 v * (1 - max v r)) ∂ζ.law) +
      (μ.xi 1 - μ.xi q - (1 - q) * μ.xi1 q * 1 -
        ∫ r, ψ.xi (residualMap q r) ∂ζ.law)
  linarith

/-- The arbitrary-law ground trial separates into its energy and entropy. -/
private theorem ground_trial_value (μ : FiniteMixture) (ζ : Admissible) {β q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Ioo (0 : ℝ) 1) :
    β * CSTAPGroundTrialQuadratic.functional μ β ζ.law q 0 =
      (β ^ 2 * (∫ v in (0 : ℝ)..q, μ.xi2 v * xHat ζ.law v) +
        ∫ v in (0 : ℝ)..q, (xHat ζ.law v)⁻¹) / 2 := by
  have hinv := inverse_xHat_intervalIntegrable ζ.law ζ.hasCutoff (by norm_num : (0 : ℝ) < 1) hq.2
  have hE : IntervalIntegrable (fun v => μ.xi2 v * xHat ζ.law v) volume 0 q :=
    ((xi2_continuous μ).mul (xHat_continuous ζ.law ζ.hasCutoff)).intervalIntegrable _ _
  unfold CSTAPGroundTrialQuadratic.functional CSTAPGroundTrialQuadratic.profile
  simp only [zero_mul, add_zero]
  have hsplit : (∫ v in (0 : ℝ)..q,
      μ.xi2 v * (β * xHat ζ.law v) + (β * xHat ζ.law v)⁻¹) =
      β * (∫ v in (0 : ℝ)..q, μ.xi2 v * xHat ζ.law v) +
        β⁻¹ * ∫ v in (0 : ℝ)..q, (xHat ζ.law v)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hE.const_mul β) (hinv.const_mul β⁻¹)]
    apply intervalIntegral.integral_congr
    intro v _
    simp only [mul_inv]
    ring
  rw [hsplit]
  field_simp [hβ.ne']

/-- Source `eq:th-telescope`, for every admissible probability measure.
No optimality assumption and no restriction on the number of atoms is used. -/
private theorem telescope (μ : FiniteMixture) (ζ : Admissible) {β q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Ioo (0 : ℝ) 1) :
    ζ.value β μ.xi =
      β * CSTAPGroundTrialQuadratic.functional μ β ζ.law q 0 +
        Real.log (1 - q) / 2 +
          (residualTrial ζ hq).value β (CSTAPTelescope.residualMixture μ hq).xi := by
  let Q := max ζ.cutoff q
  have hQ : HasCutoff ζ.law Q :=
    ζ.hasCutoff.mono (le_max_left _ _) (max_lt ζ.hasCutoff.2.1 hq.2)
  have hqQ : q ≤ Q := le_max_right _ _
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (inverse_xHat_intervalIntegrable ζ.law ζ.hasCutoff (by norm_num : (0 : ℝ) < 1) hq.2)
    (inverse_xHat_intervalIntegrable ζ.law ζ.hasCutoff hq.2 hQ.2.1)
  have hentropy := residual_entropy ζ hq hQ hqQ
  have henergy := residual_energy μ ζ hq
  rw [ground_trial_value μ ζ hβ hq, ζ.value_eq β μ.xi hQ,
    (residualTrial ζ hq).value_eq β _ (residualTrial_hasCutoff ζ hq hQ)]
  unfold CrisantiSommers.functional
  rw [henergy]
  linarith

/-- The source telescope for the arbitrary canonical Parisi measure. -/
private theorem canonical_telescope (μ : FiniteMixture) {β q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Ioo (0 : ℝ) 1) :
    CSParisiMeasure.variationalValue μ β =
      β * CSTAPGroundTrialQuadratic.functional μ β (CSParisiMeasure.canonicalMinimizer μ β).law q 0 +
        Real.log (1 - q) / 2 +
          (residualTrial (CSParisiMeasure.canonicalMinimizer μ β) hq).value β
            (CSTAPTelescope.residualMixture μ hq).xi :=
  telescope μ (CSParisiMeasure.canonicalMinimizer μ β) hβ hq


end Telescope

private theorem inv_add_quadratic_upper {a u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    (a+u)⁻¹ ≤ a⁻¹-u/a^2+u^2/a^3 := by
  have hp : 0 < a+u := by linarith
  have he : (a+u)⁻¹ = a⁻¹-u/a^2+u^2/a^3-u^3/(a^3*(a+u)) := by
    field_simp [ha.ne',hp.ne']
    ring
  rw [he]
  exact sub_le_self _ (by positivity)

/-- The first variation of the manuscript's ground-profile perturbation
`ℓ_ε(v) = β x̂(v) + ε(q-v)` is the negative contact potential.  This is the
integration-by-parts step in source §5 before the quantitative TAP gap. -/
theorem contact_trial_first_variation (μ : FiniteMixture) (ζ : Admissible) {β q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) :
    (∫ v in (0 : ℝ)..q,
      (β^2 * μ.xi2 v - 1 / (xHat ζ.law v)^2) * (q-v)) =
      -CSStructure.potential μ β ζ.law q := by
  let V : ℝ → ℝ := CSStructure.potential μ β ζ.law
  have hcut := ζ.hasCutoff
  have hxcont : Continuous (xHat ζ.law) := xHat_continuous ζ.law hcut
  have hxne (v : ℝ) (hv : v ∈ Icc (0 : ℝ) q) : xHat ζ.law v ≠ 0 :=
    (xHat_pos ζ.law hcut (hv.2.trans_lt hq.2)).ne'
  have hgcont : ContinuousOn
      (fun v : ℝ => (β^2*μ.xi2 v - 1/(xHat ζ.law v)^2)*(q-v))
      (Icc (0 : ℝ) q) := by
    have hξ : Continuous μ.xi2 := continuous_iff_continuousAt.mpr
      (fun v => (μ.hasDerivAt_xi2 v).continuousAt)
    have hh : ContinuousOn (fun v : ℝ => ((xHat ζ.law v)^2)⁻¹) (Icc (0 : ℝ) q) :=
      (hxcont.continuousOn.pow 2).inv₀ (fun v hv => pow_ne_zero 2 (hxne v hv))
    have hbase : ContinuousOn
        (fun v : ℝ => β^2*μ.xi2 v - ((xHat ζ.law v)^2)⁻¹)
        (Icc (0 : ℝ) q) :=
      (continuousOn_const.mul hξ.continuousOn).sub hh
    have hlin : ContinuousOn (fun v : ℝ => q-v) (Icc (0 : ℝ) q) :=
      continuousOn_const.sub continuousOn_id
    convert hbase.mul hlin using 1
    funext v
    simp only [Pi.mul_apply, one_div]
  have hgint : IntervalIntegrable
      (fun v : ℝ => (β^2*μ.xi2 v - 1/(xHat ζ.law v)^2)*(q-v))
      volume 0 q := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hq.1.le] using hgcont
  let F : ℝ → ℝ := fun v => -((q-v)*deriv V v)-V v
  have hFderiv (v : ℝ) (hv : v ∈ Icc (0 : ℝ) q) :
      HasDerivAt F ((β^2*μ.xi2 v - 1/(xHat ζ.law v)^2)*(q-v)) v := by
    have hv1 : v < 1 := hv.2.trans_lt hq.2
    have hV := CSStructure.potential_hasDerivAt μ β ζ.law hcut hv1
    have hV' := CSStructure.potential_deriv_hasDerivAt μ β ζ.law hcut hv1
    have hD : HasDerivAt V (deriv V v) v := by
      convert hV using 1
      exact hV.deriv
    dsimp [F]
    convert ((((hasDerivAt_const v q).sub (hasDerivAt_id v)).mul hV').neg.sub hD) using 1
    · funext t
      change -((q-t)*deriv V t)-V t =
        -((q-t)*deriv (CSStructure.potential μ β ζ.law) t)-V t
      rfl
    · dsimp only [Pi.sub_apply, Pi.mul_apply]
      simp only [id_eq]
      ring
  have hFint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := q) (f := F)
    (fun v hv => hFderiv v (by simpa only [uIcc_of_le hq.1.le] using hv)) hgint
  have h0 := CSStructure.potential_origin μ β ζ.law hcut
  change (∫ v in (0 : ℝ)..q,
    (β^2 * μ.xi2 v - 1 / (xHat ζ.law v)^2) * (q-v)) = -V q
  rw [hFint]
  dsimp [F]
  change V 0 = 0 ∧ deriv V 0 = 0 at h0
  rw [h0.1, h0.2]
  ring


/-- The quantitative one-parameter ground-profile trial estimate in source
§5. The actual first variation is supplied by the previous proved contact
identity; the quadratic term comes from the exact reciprocal remainder. -/
theorem ground_trial_quadratic_gap (μ : FiniteMixture) (ζ : Admissible) {β q ε : ℝ} (hβ : 0 < β)
    (hq : q ∈ Ioo (0 : ℝ) 1) (hε : 0 ≤ ε) :
    CSTAPGroundTrialQuadratic.functional μ β ζ.law q ε ≤
      CSTAPGroundTrialQuadratic.functional μ β ζ.law q 0 -
        ε*CSStructure.potential μ β ζ.law q/(2*β^2)+
        ε^2*curvature β ζ.law q/2 := by
  have hcut := ζ.hasCutoff
  have hxcont : Continuous (xHat ζ.law) := xHat_continuous ζ.law hcut
  have hxi : Continuous μ.xi2 := continuous_iff_continuousAt.mpr
    (fun v => (μ.hasDerivAt_xi2 v).continuousAt)
  have hxp (v : ℝ) (hv : v ∈ Icc (0 : ℝ) q) : 0 < xHat ζ.law v :=
    xHat_pos ζ.law hcut (hv.2.trans_lt hq.2)
  have hbasepos (v : ℝ) (hv : v ∈ Icc (0 : ℝ) q) :
      0 < β*xHat ζ.law v := mul_pos hβ (hxp v hv)
  have hprofpos (e : ℝ) (he : 0 ≤ e) (v : ℝ) (hv : v ∈ Icc (0 : ℝ) q) :
      0 < CSTAPGroundTrialQuadratic.profile β ζ.law q e v := by
    dsimp [CSTAPGroundTrialQuadratic.profile]
    have hb : 0 ≤ e*(q-v) := mul_nonneg he (sub_nonneg.mpr hv.2)
    linarith [hbasepos v hv]
  have hprofcont (e : ℝ) : Continuous (CSTAPGroundTrialQuadratic.profile β ζ.law q e) := by
    unfold CSTAPGroundTrialQuadratic.profile
    fun_prop
  have hbasecont : ContinuousOn (fun v : ℝ => (β*xHat ζ.law v)⁻¹) (Icc (0 : ℝ) q) :=
    (continuous_const.mul hxcont).continuousOn.inv₀
      (fun v hv => (hbasepos v hv).ne')
  have hlincont : ContinuousOn
      (fun v : ℝ => (μ.xi2 v-1/(β*xHat ζ.law v)^2)*(q-v))
      (Icc (0 : ℝ) q) := by
    have hrec : ContinuousOn (fun v : ℝ => ((β*xHat ζ.law v)^2)⁻¹)
        (Icc (0 : ℝ) q) :=
      ((continuous_const.mul hxcont).continuousOn.pow 2).inv₀
        (fun v hv => pow_ne_zero 2 (hbasepos v hv).ne')
    have hb : ContinuousOn (fun v : ℝ => μ.xi2 v-((β*xHat ζ.law v)^2)⁻¹)
        (Icc (0 : ℝ) q) := hxi.continuousOn.sub hrec
    have hc : ContinuousOn (fun v : ℝ => q-v) (Icc (0 : ℝ) q) :=
      continuousOn_const.sub continuousOn_id
    convert hb.mul hc using 1
    funext v
    simp only [Pi.mul_apply, one_div]
  have hquadcont : ContinuousOn
      (fun v : ℝ => (q-v)^2/(β*xHat ζ.law v)^3)
      (Icc (0 : ℝ) q) := by
    have hc : ContinuousOn (fun v : ℝ => q-v) (Icc (0 : ℝ) q) :=
      continuousOn_const.sub continuousOn_id
    exact (hc.pow 2).div ((continuous_const.mul hxcont).continuousOn.pow 3)
      (fun v hv => pow_ne_zero 3 (hbasepos v hv).ne')
  have hfuncont (e : ℝ) (he : 0 ≤ e) : ContinuousOn
      (fun v : ℝ => μ.xi2 v*CSTAPGroundTrialQuadratic.profile β ζ.law q e v+(CSTAPGroundTrialQuadratic.profile β ζ.law q e v)⁻¹)
      (Icc (0 : ℝ) q) :=
    (hxi.continuousOn.mul (hprofcont e).continuousOn).add
      ((hprofcont e).continuousOn.inv₀ (fun v hv => (hprofpos e he v hv).ne'))
  have hi (e : ℝ) (he : 0 ≤ e) : IntervalIntegrable
      (fun v : ℝ => μ.xi2 v*CSTAPGroundTrialQuadratic.profile β ζ.law q e v+(CSTAPGroundTrialQuadratic.profile β ζ.law q e v)⁻¹)
      volume 0 q := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hq.1.le] using hfuncont e he
  have hlinI : IntervalIntegrable
      (fun v : ℝ => (μ.xi2 v-1/(β*xHat ζ.law v)^2)*(q-v))
      volume 0 q := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hq.1.le] using hlincont
  have hquadI : IntervalIntegrable
      (fun v : ℝ => (q-v)^2/(β*xHat ζ.law v)^3)
      volume 0 q := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hq.1.le] using hquadcont
  have hpt (v : ℝ) (hv : v ∈ Icc (0 : ℝ) q) :
      μ.xi2 v*CSTAPGroundTrialQuadratic.profile β ζ.law q ε v+(CSTAPGroundTrialQuadratic.profile β ζ.law q ε v)⁻¹ ≤
        (μ.xi2 v*CSTAPGroundTrialQuadratic.profile β ζ.law q 0 v+(CSTAPGroundTrialQuadratic.profile β ζ.law q 0 v)⁻¹)+
          ε*((μ.xi2 v-1/(β*xHat ζ.law v)^2)*(q-v))+
          ε^2*((q-v)^2/(β*xHat ζ.law v)^3) := by
    let a := β*xHat ζ.law v
    let u := ε*(q-v)
    have ha : 0 < a := hbasepos v hv
    have hu : 0 ≤ u := mul_nonneg hε (sub_nonneg.mpr hv.2)
    have hh := inv_add_quadratic_upper ha hu
    have he : CSTAPGroundTrialQuadratic.profile β ζ.law q ε v = a+u := rfl
    have he0 : CSTAPGroundTrialQuadratic.profile β ζ.law q 0 v = a := by simp [CSTAPGroundTrialQuadratic.profile,a]
    rw [he,he0]
    calc
      μ.xi2 v*(a+u)+(a+u)⁻¹ ≤
          μ.xi2 v*(a+u)+(a⁻¹-u/a^2+u^2/a^3) := by
            simpa only [add_comm] using add_le_add_left hh (μ.xi2 v*(a+u))
      _ = (μ.xi2 v*a+a⁻¹)+ε*((μ.xi2 v-1/a^2)*(q-v))+
          ε^2*((q-v)^2/a^3) := by dsimp [u]; ring
  have hR : IntervalIntegrable
      (fun v : ℝ =>
        (μ.xi2 v*CSTAPGroundTrialQuadratic.profile β ζ.law q 0 v+(CSTAPGroundTrialQuadratic.profile β ζ.law q 0 v)⁻¹)+
          ε*((μ.xi2 v-1/(β*xHat ζ.law v)^2)*(q-v))+
          ε^2*((q-v)^2/(β*xHat ζ.law v)^3)) volume 0 q :=
    ((hi 0 (by norm_num)).add (hlinI.const_mul ε)).add (hquadI.const_mul (ε^2))
  have hbound := intervalIntegral.integral_mono_on hq.1.le (hi ε hε) hR hpt
  have hcontact := contact_trial_first_variation μ ζ (β := β) hq
  have hlinEq (v : ℝ) :
      (μ.xi2 v-1/(β*xHat ζ.law v)^2)*(q-v) =
        ((β^2*μ.xi2 v-1/(xHat ζ.law v)^2)*(q-v))/β^2 := by
    by_cases hx : xHat ζ.law v = 0
    · simp only [hx, mul_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0),
        div_zero, sub_zero]
      field_simp [hβ.ne']
    · field_simp [hβ.ne',hx]
  have hlinval : (∫ v in (0 : ℝ)..q,
      (μ.xi2 v-1/(β*xHat ζ.law v)^2)*(q-v)) =
        -CSStructure.potential μ β ζ.law q/β^2 := by
    simp_rw [hlinEq]
    rw [intervalIntegral.integral_div]
    exact congrArg (fun t : ℝ => t/β^2) hcontact
  unfold CSTAPGroundTrialQuadratic.functional curvature
  rw [intervalIntegral.integral_add ((hi 0 (by norm_num)).add (hlinI.const_mul ε))
    (hquadI.const_mul (ε^2)), intervalIntegral.integral_add (hi 0 (by norm_num))
    (hlinI.const_mul ε), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hlinval] at hbound
  dsimp [CSTAPGroundTrialQuadratic.profile] at hbound ⊢
  convert (div_le_div_of_nonneg_right hbound (by norm_num : 0 ≤ (2 : ℝ))) using 1
  all_goals ring



/-- The hatted profile is nonincreasing for every admissible measure. -/
theorem xHat_antitone (ζ : Admissible) : Antitone (xHat ζ.law) := by
  intro u v huv
  unfold xHat
  exact integral_mono (kernel_integrable ζ.law ζ.hasCutoff v)
    (kernel_integrable ζ.law ζ.hasCutoff u)
    (fun r => sub_le_sub_left (max_le_max_right r huv) 1)

/-- The trial curvature is exactly the manuscript's factored integral `M_q`. -/
theorem curvature_eq_source (β : ℝ) (ζ : Measure ℝ) (q : ℝ) :
    curvature β ζ q = 1/β^3 * ∫ v in (0 : ℝ)..q, (q-v)^2/(xHat ζ v)^3 := by
  unfold curvature
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v _
  simp only [mul_pow, div_eq_mul_inv, mul_inv]
  ring

/-- The literal coefficient `M_q` is strictly positive without a one-step assumption. -/
theorem ground_trial_curvature_pos (ζ : Admissible) {β q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Ioo (0 : ℝ) 1) :
    0 < curvature β ζ.law q := by
  have hxcont := xHat_continuous ζ.law ζ.hasCutoff
  have hxpos (v : ℝ) (hv : v ∈ Icc (0 : ℝ) q) : 0 < β*xHat ζ.law v :=
    mul_pos hβ (xHat_pos ζ.law ζ.hasCutoff (hv.2.trans_lt hq.2))
  have hc : ContinuousOn (fun v : ℝ => (q-v)^2/(β*xHat ζ.law v)^3)
      (Icc (0 : ℝ) q) := by
    exact ((continuous_const.sub continuous_id).pow 2).continuousOn.div
      ((continuous_const.mul hxcont).pow 3).continuousOn
      (fun v hv => pow_ne_zero 3 (hxpos v hv).ne')
  apply intervalIntegral.integral_pos hq.1 hc
  · intro v hv
    exact div_nonneg (sq_nonneg _) (pow_nonneg (hxpos v ⟨hv.1.le,hv.2⟩).le _)
  · refine ⟨q/2, ⟨by linarith [hq.1], by linarith [hq.1]⟩, ?_⟩
    exact div_pos (sq_pos_of_ne_zero (by linarith [hq.1]))
      (pow_pos (hxpos (q/2) ⟨by linarith [hq.1], by linarith [hq.1]⟩) _)

/-- The printed upper bound on `M_q`, valid for an arbitrary Parisi profile. -/
theorem ground_trial_curvature_le (ζ : Admissible) {β q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Ioo (0 : ℝ) 1) :
    curvature β ζ.law q ≤ q^3/(3*β^3*xHat ζ.law q^3) := by
  have hxcont := xHat_continuous ζ.law ζ.hasCutoff
  have hxpos (v : ℝ) (hv : v ∈ Icc (0 : ℝ) q) : 0 < β*xHat ζ.law v :=
    mul_pos hβ (xHat_pos ζ.law ζ.hasCutoff (hv.2.trans_lt hq.2))
  have hi : IntervalIntegrable (fun v : ℝ => (q-v)^2/(β*xHat ζ.law v)^3)
      volume 0 q := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hq.1.le]
    exact ((continuous_const.sub continuous_id).pow 2).continuousOn.div
      ((continuous_const.mul hxcont).pow 3).continuousOn
      (fun v hv => pow_ne_zero 3 (hxpos v hv).ne')
  have hb : (∫ v in (0 : ℝ)..q, (q-v)^2/(β*xHat ζ.law v)^3) ≤
      ∫ v in (0 : ℝ)..q, (q-v)^2/(β*xHat ζ.law q)^3 := by
    apply intervalIntegral.integral_mono_on hq.1.le hi
      ((((continuous_const.sub continuous_id).pow 2).div_const _).intervalIntegrable 0 q)
    intro v hv
    exact div_le_div_of_nonneg_left (sq_nonneg _)
      (pow_pos (hxpos q ⟨hq.1.le, le_rfl⟩) 3)
      (pow_le_pow_left₀ (hxpos q ⟨hq.1.le, le_rfl⟩).le
        (mul_le_mul_of_nonneg_left (xHat_antitone ζ hv.2) hβ.le) 3)
  have hpoly : (∫ v in (0 : ℝ)..q, (q-v)^2) = q^3/3 := by
    calc
      _ = -(q-q)^3/3 - -(q-0)^3/3 := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun v : ℝ => -(q-v)^3/3)
        · intro v _
          convert ((((hasDerivAt_const v q).sub (hasDerivAt_id v)).pow 3).neg.div_const 3)
            using 1
          · funext w; rfl
          · dsimp only [Pi.sub_apply, id_eq]; ring
        · exact ((continuous_const.sub continuous_id).pow 2).intervalIntegrable _ _
      _ = _ := by ring
  change (∫ v in (0 : ℝ)..q, (q-v)^2/(β*xHat ζ.law v)^3) ≤ _
  calc
    _ ≤ _ := hb
    _ = _ := by rw [intervalIntegral.integral_div, hpoly, mul_pow]; ring

/-- The optimized general trial estimate, with exactly the source denominator. -/
theorem ground_trial_strict_contact_gap (μ : FiniteMixture) (ζ : Admissible)
    {β q : ℝ} (hβ : 0 < β) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hV : 0 < CSStructure.potential μ β ζ.law q) :
    CSTAPGroundTrialQuadratic.functional μ β ζ.law q
        (CSStructure.potential μ β ζ.law q / (2*β^2*curvature β ζ.law q)) ≤
      CSTAPGroundTrialQuadratic.functional μ β ζ.law q 0 -
        (CSStructure.potential μ β ζ.law q)^2/(8*β^4*curvature β ζ.law q) := by
  have hM := ground_trial_curvature_pos ζ hβ hq
  have hε : 0 ≤ CSStructure.potential μ β ζ.law q /
      (2*β^2*curvature β ζ.law q) := by positivity
  convert ground_trial_quadratic_gap μ ζ hβ hq hε using 1
  field_simp [hβ.ne', hM.ne']
  ring

private theorem cdf_primitive (ζ : Admissible) {v : ℝ} (hv : v ≤ 1) :
    (∫ w in (0 : ℝ)..v, cdf ζ.law w) = xHat ζ.law 0 - xHat ζ.law v := by
  have h : (∫ w in (0 : ℝ)..v, cdf ζ.law w) + (∫ w in v..1, cdf ζ.law w) =
      ∫ w in (0 : ℝ)..1, cdf ζ.law w :=
    intervalIntegral.integral_add_adjacent_intervals
      ((monotone_cdf ζ.law).intervalIntegrable (a := 0) (b := v))
      ((monotone_cdf ζ.law).intervalIntegrable (a := v) (b := 1))
  rw [← xHat_integrated_cdf ζ.law ζ.hasCutoff hv,
    ← xHat_integrated_cdf ζ.law ζ.hasCutoff zero_le_one] at h
  linarith

private theorem trial_mass (ζ : Admissible) (β ε : ℝ) {v : ℝ} (hv : v ≤ 1) :
    (∫ w in (0 : ℝ)..v, β*cdf ζ.law w+ε) =
      β*(xHat ζ.law 0-xHat ζ.law v)+ε*v := by
  rw [intervalIntegral.integral_add
    ((monotone_cdf ζ.law).intervalIntegrable.const_mul β) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, cdf_primitive ζ hv]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- The explicit trial is in the full manuscript ground-profile domain. -/
def groundTrial (ζ : Admissible) {β q ε : ℝ} (hβ : 0 < β)
    (hq : q ∈ Ioo (0 : ℝ) 1) (hε : 0 ≤ ε) : RadiusGroundProfile q where
  L := β*xHat ζ.law 0+ε*q
  alpha := fun v => β*cdf ζ.law v+ε
  alpha_nonnegative := fun v _ =>
    add_nonneg (mul_nonneg hβ.le (cdf_nonneg ζ.law v)) hε
  alpha_monotone := fun v _ w _ hvw =>
    add_le_add (mul_le_mul_of_nonneg_left ((monotone_cdf ζ.law) hvw) hβ.le) le_rfl
  alpha_rightContinuous := fun v _ =>
    (continuousWithinAt_const.mul ((cdf ζ.law).right_continuous v)).add
      continuousWithinAt_const
  alpha_integrable :=
    ((monotone_cdf ζ.law).intervalIntegrable.const_mul β).add intervalIntegrable_const
  height_gt_mass := by
    rw [trial_mass ζ β ε hq.2.le]
    nlinarith [mul_pos hβ (xHat_pos ζ.law ζ.hasCutoff hq.2)]

/-- The radius trial is literally `ℓ_ε(v)=β x̂(v)+ε(q-v)`. -/
theorem radiusProfile_groundTrial (ζ : Admissible) {β q ε : ℝ} (hβ : 0 < β)
    (hq : q ∈ Ioo (0 : ℝ) 1) (hε : 0 ≤ ε) {v : ℝ} (hv : v ≤ 1) :
    radiusProfile (groundTrial ζ hβ hq hε) v = CSTAPGroundTrialQuadratic.profile β ζ.law q ε v := by
  unfold radiusProfile groundTrial CSTAPGroundTrialQuadratic.profile
  rw [trial_mass ζ β ε hv]
  ring

/-- The full radius variational objective agrees with the general trial integral. -/
theorem radiusFunctional_groundTrial (μ : FiniteMixture) (ζ : Admissible)
    {β q ε : ℝ} (hβ : 0 < β) (hq : q ∈ Ioo (0 : ℝ) 1) (hε : 0 ≤ ε) :
    radiusFunctional μ (groundTrial ζ hβ hq hε) = CSTAPGroundTrialQuadratic.functional μ β ζ.law q ε := by
  have hp : ∀ v ∈ uIcc (0 : ℝ) q,
      radiusProfile (groundTrial ζ hβ hq hε) v = CSTAPGroundTrialQuadratic.profile β ζ.law q ε v := by
    intro v hv
    rw [uIcc_of_le hq.1.le] at hv
    exact radiusProfile_groundTrial ζ hβ hq hε (hv.2.trans hq.2.le)
  have hxcont := xHat_continuous ζ.law ζ.hasCutoff
  have hc : Continuous (CSTAPGroundTrialQuadratic.profile β ζ.law q ε) := by unfold CSTAPGroundTrialQuadratic.profile; fun_prop
  have hp0 (v : ℝ) (hv : v ∈ uIcc (0 : ℝ) q) : 0 < CSTAPGroundTrialQuadratic.profile β ζ.law q ε v := by
    rw [uIcc_of_le hq.1.le] at hv
    unfold CSTAPGroundTrialQuadratic.profile
    exact add_pos_of_pos_of_nonneg
      (mul_pos hβ (xHat_pos ζ.law ζ.hasCutoff (hv.2.trans_lt hq.2)))
      (mul_nonneg hε (sub_nonneg.mpr hv.2))
  have hxi : Continuous μ.xi2 := continuous_iff_continuousAt.mpr
    (fun v => (μ.hasDerivAt_xi2 v).continuousAt)
  have he : (∫ v in (0 : ℝ)..q, μ.xi2 v*radiusProfile (groundTrial ζ hβ hq hε) v) =
      ∫ v in (0 : ℝ)..q, μ.xi2 v*CSTAPGroundTrialQuadratic.profile β ζ.law q ε v :=
    intervalIntegral.integral_congr (fun v hv => by rw [hp v hv])
  have hi : (∫ v in (0 : ℝ)..q, (radiusProfile (groundTrial ζ hβ hq hε) v)⁻¹) =
      ∫ v in (0 : ℝ)..q, (CSTAPGroundTrialQuadratic.profile β ζ.law q ε v)⁻¹ :=
    intervalIntegral.integral_congr (fun v hv => by rw [hp v hv])
  unfold radiusFunctional CSTAPGroundTrialQuadratic.functional
  rw [he, hi]
  congr 1
  exact (intervalIntegral.integral_add
    (f := fun v => μ.xi2 v*CSTAPGroundTrialQuadratic.profile β ζ.law q ε v)
    (g := fun v => (CSTAPGroundTrialQuadratic.profile β ζ.law q ε v)⁻¹)
    ((hxi.mul hc).intervalIntegrable 0 q)
    (hc.continuousOn.inv₀ (fun v hv => (hp0 v hv).ne')).intervalIntegrable).symm




/-- A compact subset of the noncontact region has a uniform strictly positive
lower bound for the exact ratio in `thm:th-contact`(3), including the empty set. -/
theorem compact_uniform_contact_gap (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β)
    {K : Set ℝ} (hK : IsCompact K) (hKsub : K ⊆ Ioo (0 : ℝ) 1)
    (hKzero : ∀ q ∈ K,
      CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ q ∈ K,
      c ≤ (CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q)^2 /
        curvature β (CSParisiMeasure.canonicalMinimizer μ β).law q := by
  let ζ := CSParisiMeasure.canonicalMinimizer μ β
  by_cases hne : K.Nonempty
  · have hcont : ContinuousOn (CSStructure.potential μ β ζ.law) K := by
      intro q hq
      exact (CSStructure.potential_hasDerivAt μ β ζ.law ζ.hasCutoff
        (hKsub hq).2).continuousAt.continuousWithinAt
    obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hne hcont
    obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hne continuousOn_id
    have hapos : 0 < CSStructure.potential μ β ζ.law a :=
      lt_of_le_of_ne ((ThermalPhysicalZeroContact.canonical_zero_contact μ β).2.1 a
        ⟨(hKsub ha).1.le, (hKsub ha).2⟩) (Ne.symm (hKzero a ha))
    let B := 1/(3*β^3*xHat ζ.law b^3)
    have hB : 0 < B := by
      dsimp [B]
      have hx := xHat_pos ζ.law ζ.hasCutoff (hKsub hb).2
      positivity
    refine ⟨(CSStructure.potential μ β ζ.law a)^2/B, div_pos (sq_pos_of_pos hapos) hB, ?_⟩
    intro q hq
    have hqr := hKsub hq
    have hxq := xHat_pos ζ.law ζ.hasCutoff hqr.2
    have hxb := xHat_pos ζ.law ζ.hasCutoff (hKsub hb).2
    have hM := ground_trial_curvature_pos ζ hβ hqr
    have hMB : curvature β ζ.law q ≤ B := by
      calc
        _ ≤ q^3/(3*β^3*xHat ζ.law q^3) := ground_trial_curvature_le ζ hβ hqr
        _ ≤ 1/(3*β^3*xHat ζ.law q^3) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          simpa only [one_pow] using pow_le_pow_left₀ hqr.1.le hqr.2.le 3
        _ ≤ B := by
          apply div_le_div_of_nonneg_left zero_le_one (by positivity)
          gcongr
          exact xHat_antitone ζ (hmax hq)
    have hVq : CSStructure.potential μ β ζ.law a ≤ CSStructure.potential μ β ζ.law q := hmin hq
    apply (le_div_iff₀ hM).mpr
    have hsq : (CSStructure.potential μ β ζ.law a)^2 ≤
        (CSStructure.potential μ β ζ.law q)^2 := by nlinarith
    calc
      (CSStructure.potential μ β ζ.law a)^2/B * curvature β ζ.law q
          ≤ (CSStructure.potential μ β ζ.law a)^2/B * B :=
            mul_le_mul_of_nonneg_left hMB (by positivity)
      _ = (CSStructure.potential μ β ζ.law a)^2 := div_mul_cancel₀ _ hB.ne'
      _ ≤ _ := hsq
  · refine ⟨1, zero_lt_one, ?_⟩
    intro q hq
    exact (hne ⟨q,hq⟩).elim


private theorem ground_le_trial (hChenSen : ChenSenFiniteGround)
    {μ : FiniteMixture} {β q ε : ℝ} (D : ThermodynamicData μ β)
    (hβ : 0 < β) (hq : q ∈ Ioo (0 : ℝ) 1) (hε : 0 ≤ ε) :
    D.ground q ≤ CSTAPGroundTrialQuadratic.functional μ β (CSParisiMeasure.canonicalMinimizer μ β).law q ε := by
  obtain ⟨u, hmin, hlim, _⟩ := source_ground_limit_unique hChenSen μ hq.1
  have hG := tendsto_nhds_unique (D.ground_limit q hq) hlim
  rw [hG, ← radiusFunctional_groundTrial μ _ hβ hq hε]
  exact hmin _

private theorem residual_le_trial (hChen : Chen2013FiniteParisi)
    {μ : FiniteMixture} {β q : ℝ} (D : ThermodynamicData μ β)
    (hβ : 0 < β) (hq : q ∈ Ioo (0 : ℝ) 1) :
    D.residual q ≤ (Telescope.residualTrial (CSParisiMeasure.canonicalMinimizer μ β) hq).value
      β (CSTAPTelescope.residualMixture μ hq).xi := by
  have hR := tendsto_nhds_unique (D.residual_limit q hq)
    (hChen (physicalResidualMixture μ q hq) β hβ.le)
  rw [hR]
  exact CSParisiMeasure.canonicalMinimizer_isMinimizer _ β _

/-- `thm:th-contact`(3): the quantitative physical TAP gap at every positive
potential of an arbitrary finite-mixture Parisi measure. -/
theorem tapValue_le_pressure_sub_gap (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround) {μ : FiniteMixture} {β q : ℝ}
    (hβ : 0 < β) (D : ThermodynamicData μ β) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hV : 0 < CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q) :
    tapValue D q ≤ D.pressure -
      (CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q)^2 /
        (8*β^3*curvature β (CSParisiMeasure.canonicalMinimizer μ β).law q) := by
  let ζ := CSParisiMeasure.canonicalMinimizer μ β
  let V := CSStructure.potential μ β ζ.law q
  let M := curvature β ζ.law q
  have hM : 0 < M := ground_trial_curvature_pos ζ hβ hq
  have hε : 0 ≤ V/(2*β^2*M) := by dsimp [V]; positivity
  have hground : D.ground q ≤ CSTAPGroundTrialQuadratic.functional μ β ζ.law q 0 - V^2/(8*β^4*M) :=
    (ground_le_trial hChenSen D hβ hq hε).trans
      (ground_trial_strict_contact_gap μ ζ hβ hq hV)
  have hres := residual_le_trial hChen D hβ hq
  have hP := tendsto_nhds_unique D.pressure_limit (hChen μ β hβ.le)
  have htel := Telescope.canonical_telescope μ hβ hq
  have hscale : β*(V^2/(8*β^4*M)) = V^2/(8*β^3*M) := by
    field_simp [hβ.ne', hM.ne']
  have hβg := mul_le_mul_of_nonneg_left hground hβ.le
  unfold tapValue
  rw [hP, htel]
  change β*D.ground q+Real.log (1-q)/2+D.residual q ≤
    β*CSTAPGroundTrialQuadratic.functional μ β ζ.law q 0+Real.log (1-q)/2+
      (Telescope.residualTrial ζ hq).value β (CSTAPTelescope.residualMixture μ hq).xi -
        V^2/(8*β^3*M)
  nlinarith

/-- Every positive noncontact has a strict physical TAP gap, for arbitrary
Parisi measures, conditional only on Chen and Chen–Sen. -/
theorem strict_tap_gap (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    {μ : FiniteMixture} {β q : ℝ} (hβ : 0 < β) (D : ThermodynamicData μ β)
    (hq : q ∈ Ioo (0 : ℝ) 1)
    (hV : 0 < CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q) :
    tapValue D q < D.pressure := by
  have h := tapValue_le_pressure_sub_gap hChen hChenSen hβ D hq hV
  have hM := ground_trial_curvature_pos (CSParisiMeasure.canonicalMinimizer μ β) hβ hq
  have hgap : 0 <
      (CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q)^2 /
        (8*β^3*curvature β (CSParisiMeasure.canonicalMinimizer μ β).law q) := by positivity
  linarith

private theorem multiSamplable_of_zero_potential {μ : FiniteMixture} {β q : ℝ}
    (h10 : Theorem10Forward μ β) (hq : q ∈ Ico (0 : ℝ) 1)
    (hV : CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q = 0) :
    MultiSamplable μ β q := by
  apply h10.2 q
  refine ⟨hq, ?_⟩
  have hzero := neg_eq_zero.mp hV
  intro r hr
  rw [hzero]
  exact (ThermalPhysicalZeroContact.minimizer_firstVariation_maximum_zero μ β
    (CSParisiMeasure.canonicalMinimizer μ β)
    (CSParisiMeasure.canonicalMinimizer_isMinimizer μ β)).1 r hr

/-- `thm:th-contact`(1), on the entire printed interval `[0,1)`, for every
finite mixture. The Subag inputs are precisely the existing explicit interfaces. -/
theorem contact_iff_multiSamplable (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround) {μ : FiniteMixture} {β : ℝ}
    (D : ThermodynamicData μ β) (h5 : LiteratureSubagTAP.Theorem5 D)
    (h10 : Theorem10Forward μ β) {q : ℝ} (hq : q ∈ Ico (0 : ℝ) 1) :
    MultiSamplable μ β q ↔
      CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q = 0 := by
  constructor
  · intro hm
    have hnonneg := (ThermalPhysicalZeroContact.canonical_zero_contact μ β).2.1 q hq
    by_contra hne
    have hV := lt_of_le_of_ne hnonneg (Ne.symm hne)
    have hq0 : q ≠ 0 := by
      intro hz
      rw [hz, (ThermalPhysicalZeroContact.canonical_zero_contact μ β).1] at hV
      exact (lt_irrefl 0) hV
    exact LiteratureSubagTAP.not_multiSamplable_of_strictTAPGap D h5
      ⟨lt_of_le_of_ne hq.1 (Ne.symm hq0), hq.2⟩
      (strict_tap_gap hChen hChenSen h5.1 D
        ⟨lt_of_le_of_ne hq.1 (Ne.symm hq0), hq.2⟩ hV) hm
  · exact multiSamplable_of_zero_potential h10 hq

private theorem contact_saturation (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround) {μ : FiniteMixture} {β q : ℝ}
    (D : ThermodynamicData μ β) (h5 : LiteratureSubagTAP.Theorem5 D)
    (h10 : Theorem10Forward μ β) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hV : CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q = 0) :
    D.ground q = CSTAPGroundTrialQuadratic.functional μ β (CSParisiMeasure.canonicalMinimizer μ β).law q 0 ∧
    D.residual q = (Telescope.residualTrial (CSParisiMeasure.canonicalMinimizer μ β) hq).value
      β (CSTAPTelescope.residualMixture μ hq).xi := by
  have hG := ground_le_trial hChenSen D h5.1 hq (le_refl (0 : ℝ))
  have hR := residual_le_trial hChen D h5.1 hq
  have hP := tendsto_nhds_unique D.pressure_limit (hChen μ β h5.1.le)
  have htel := Telescope.canonical_telescope μ h5.1 hq
  have heq := (h5.2 q hq).1.mpr (multiSamplable_of_zero_potential h10 ⟨hq.1.le,hq.2⟩ hV)
  unfold tapValue at heq
  rw [hP, htel] at heq
  constructor <;> nlinarith [h5.1]

/-- `thm:th-contact`(2), ground clause: the explicit restricted profile is
a minimizer over the full source domain, gives the physical energy, and is
identical on `[0,q]` to every other minimizer. -/
theorem contact_ground_profile_unique (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround) {μ : FiniteMixture} {β q : ℝ}
    (D : ThermodynamicData μ β) (h5 : LiteratureSubagTAP.Theorem5 D)
    (h10 : Theorem10Forward μ β) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hV : CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q = 0) :
    let u := groundTrial (CSParisiMeasure.canonicalMinimizer μ β) h5.1 hq (le_refl (0 : ℝ))
    (∀ v : RadiusGroundProfile q, radiusFunctional μ u ≤ radiusFunctional μ v) ∧
    D.ground q = radiusFunctional μ u ∧
    (∀ v : RadiusGroundProfile q,
      (∀ w : RadiusGroundProfile q, radiusFunctional μ v ≤ radiusFunctional μ w) →
      ∀ r ∈ Icc (0 : ℝ) q,
        radiusProfile v r = β*xHat (CSParisiMeasure.canonicalMinimizer μ β).law r) := by
  dsimp only
  let u := groundTrial (CSParisiMeasure.canonicalMinimizer μ β) h5.1 hq (le_refl (0 : ℝ))
  obtain ⟨v, hmin, hlim, _⟩ := source_ground_limit_unique hChenSen μ hq.1
  have heq : D.ground q = radiusFunctional μ u := by
    rw [radiusFunctional_groundTrial]
    exact (contact_saturation hChen hChenSen D h5 h10 hq hV).1
  have hG := tendsto_nhds_unique (D.ground_limit q hq) hlim
  have hu : ∀ w : RadiusGroundProfile q, radiusFunctional μ u ≤ radiusFunctional μ w := by
    rw [← heq, hG]
    exact hmin
  refine ⟨hu, heq, ?_⟩
  intro w hw r hr
  rw [radius_minimizer_profile_unique μ hq.1 w u hw hu r hr,
    radiusProfile_groundTrial _ h5.1 hq (le_refl (0 : ℝ)) (hr.2.trans hq.2.le)]
  simp [CSTAPGroundTrialQuadratic.profile]

/-- `thm:th-contact`(2), residual clause: its unique canonical Parisi law is
the literal pushforward of the arbitrary original Parisi measure. -/
theorem contact_residual_canonical (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround) {μ : FiniteMixture} {β q : ℝ}
    (D : ThermodynamicData μ β) (h5 : LiteratureSubagTAP.Theorem5 D)
    (h10 : Theorem10Forward μ β) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hV : CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q = 0) :
    (CSParisiMeasure.canonicalMinimizer (physicalResidualMixture μ q hq) β).law =
      (CSParisiMeasure.canonicalMinimizer μ β).law.map
        (fun r => max 0 ((r-q)/(1-q))) := by
  let ζ := CSParisiMeasure.canonicalMinimizer μ β
  let ν := Telescope.residualTrial ζ hq
  have hsat := (contact_saturation hChen hChenSen D h5 h10 hq hV).2
  have hR := tendsto_nhds_unique (D.residual_limit q hq)
    (hChen (physicalResidualMixture μ q hq) β h5.1.le)
  have hν : ν.IsMinimizer β (physicalResidualMixture μ q hq).xi := by
    intro w
    have he : ν.value β (physicalResidualMixture μ q hq).xi =
        CSParisiMeasure.variationalValue (physicalResidualMixture μ q hq) β := hsat.symm.trans hR
    rw [he]
    exact CSParisiMeasure.canonicalMinimizer_isMinimizer _ β w
  exact (congrArg Admissible.law
    (CSParisiMeasure.eq_canonicalMinimizer_of_isMinimizer _ β ν hν)).symm

/-- Source `lem:th-replica-exclusion` for every finite mixture and every
positive noncontact: all three constants are fixed before dimension. -/
theorem replica_exclusion_of_positive_potential (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround) {μ : FiniteMixture} {β q : ℝ}
    (D : ThermodynamicData μ β) (h5 : LiteratureSubagTAP.Theorem5 D)
    (h25 : LiteratureSubagReplicaExclusion.Remark25Contrapositive μ β)
    (hq : q ∈ Ioo (0 : ℝ) 1)
    (hV : 0 < CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ ρ ∈ Ioo (0 : ℝ) 1, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        expectedOverlapBlockProbability N k μ β q ρ ≤ Real.exp (-c*(N : ℝ)) :=
  SourceSubagReplicaCriterion.source_replica_exclusion_of_strict_tap_gap D h5 h25 hq
    (strict_tap_gap hChen hChenSen h5.1 D hq hV)


open TwoAtomStationarity SphericalTAPCertificate

/-- The explicit ground potential in source `(eq:th-g)`, including endpoints. -/
theorem certificate_ground_potential_formula {μ : FiniteMixture} {β x Q : ℝ}
    (h : Certificate μ β x Q) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    CSStructure.potential μ β (twoAtom x Q) (Q*r)/β^2 =
      μ.xi Q-μ.xi (Q*r)-markA μ Q *
        ((1+markZ x Q)/(markZ x Q)^2 *
          Real.log (1+(1-r)*markZ x Q)-(1-r)/markZ x Q) := by
  let F : ℝ → ℝ := fun t => CSStructure.potential μ β (twoAtom x Q) (Q*t)/β^2
  let G : ℝ → ℝ := fun t => μ.xi Q-μ.xi (Q*t)-markA μ Q *
    ((1+markZ x Q)/(markZ x Q)^2*Real.log (1+(1-t)*markZ x Q)-(1-t)/markZ x Q)
  have hz : 0 < markZ x Q :=
    div_pos (mul_pos h.weight_range.1 h.overlap_range.1) (sub_pos.mpr h.overlap_range.2)
  have : IsProbabilityMeasure (twoAtom x Q) :=
    twoAtom_probability ⟨h.weight_range.1.le,h.weight_range.2.le⟩
  have hcut : HasCutoff (twoAtom x Q) Q :=
    twoAtom_hasCutoff ⟨h.overlap_range.1.le,h.overlap_range.2⟩
  have hFG : EqOn F G (Ioo (0 : ℝ) 1) := by
    intro t ht
    have hi := (LatitudeGroundTrial.slack_eq_contact μ h ht).symm
    simpa only [F, G, LatitudeGroundTrial.slack, LatitudeGroundTrial.D,
      SphericalParisiConditionedLatitudeCovariance.centerCovariance,
      SphericalParisiConditionedLatitudeCovariance.gradientVariance,
      SphericalParisiConditionedLatitudeCovariance.centerFirst, mul_one, markA] using hi
  have hF : ContinuousOn F (Icc (0 : ℝ) 1) := by
    intro t ht
    have hQt : Q*t < 1 := by
      calc Q*t ≤ Q*1 := mul_le_mul_of_nonneg_left ht.2 h.overlap_range.1.le
           _ < 1 := by simpa only [mul_one] using h.overlap_range.2
    exact (((CSStructure.potential_hasDerivAt μ β (twoAtom x Q) hcut hQt).continuousAt.comp
      ((continuous_const.mul continuous_id).continuousAt :
        ContinuousAt (fun u : ℝ => Q*u) t)).div_const (β^2)).continuousWithinAt
  have hxi : Continuous (fun t : ℝ => μ.xi (Q*t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (μ.hasDerivAt_xi (Q*t)).continuousAt.comp
      ((continuous_const.mul continuous_id).continuousAt : ContinuousAt (fun u : ℝ => Q*u) t)
  have hD : ContinuousOn (fun t : ℝ => 1+(1-t)*markZ x Q) (Icc (0 : ℝ) 1) := by fun_prop
  have hlog : ContinuousOn (fun t : ℝ => Real.log (1+(1-t)*markZ x Q))
      (Icc (0 : ℝ) 1) := by
    apply hD.log
    intro t ht
    have hn : 0 ≤ (1-t)*markZ x Q := mul_nonneg (sub_nonneg.mpr ht.2) hz.le
    exact (show 0 < 1+(1-t)*markZ x Q by linarith).ne'
  have hG : ContinuousOn G (Icc (0 : ℝ) 1) := by
    dsimp only [G]
    exact (continuousOn_const.sub hxi.continuousOn).sub
      (continuousOn_const.mul ((continuousOn_const.mul hlog).sub
        ((continuousOn_const.sub continuousOn_id).div_const (markZ x Q))))
  have hclosed : EqOn F G (Icc (0 : ℝ) 1) :=
    hFG.of_subset_closure hF hG Ioo_subset_Icc_self
      (by rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)])
  exact hclosed hr

/-- The exact energy-to-variance mark ratio in source `(eq:th-marks)`. -/
theorem certificate_mark_ratio {μ : FiniteMixture} {β x Q : ℝ}
    (h : Certificate μ β x Q) :
    μ.xi Q/markA μ Q =
      ((1+markZ x Q)*Real.log (1+markZ x Q)-markZ x Q)/(markZ x Q)^2 := by
  let z := markZ x Q
  let a := markA μ Q
  have hz : 0 < z :=
    div_pos (mul_pos h.weight_range.1 h.overlap_range.1) (sub_pos.mpr h.overlap_range.2)
  have ha : 0 < a := mul_pos h.overlap_range.1 (μ.xi1_pos h.overlap_range.1)
  have hz1 : 0 < 1+z := by linarith
  have hred := SphericalMarkedWindows.sourceContact_reduced_equation μ h
  rw [markY_sq_from_contact μ h.beta_pos h.weight_range h.overlap_range
    h.contact_value h.contact_derivative] at hred
  change z^2*μ.xi Q/((1+z)*a) = Real.log (1+z)-z/(1+z) at hred
  have hscaled : z^2*μ.xi Q = (Real.log (1+z)-z/(1+z))*((1+z)*a) :=
    (div_eq_iff (mul_ne_zero hz1.ne' ha.ne')).mp hred
  have hcancel : (Real.log (1+z)-z/(1+z))*((1+z)*a) =
      ((1+z)*Real.log (1+z)-z)*a := by field_simp [hz1.ne']
  rw [hcancel] at hscaled
  change μ.xi Q/a = ((1+z)*Real.log (1+z)-z)/z^2
  apply (div_eq_div_iff ha.ne' (pow_ne_zero 2 hz.ne')).mpr
  nlinarith only [hscaled]

/-- All five parts of source `prop:th-structure`, as conclusions rather than
additional assumptions. `ground_unique` quantifies over the full source domain. -/
structure StrictOneStepConclusions {μ : FiniteMixture} {β x Q : ℝ}
    (h : Certificate μ β x Q) (D : ThermodynamicData μ β) : Prop where
  parisi_law : (CSParisiMeasure.canonicalMinimizer μ β).law = twoAtom x Q
  stationarity : β^2*μ.xi1 Q = Q/((1-Q)*profileConstant x Q) ∧
    β^2*x^2*μ.xi Q = Real.log (profileConstant x Q/(1-Q))-x*Q/profileConstant x Q
  pressure : D.pressure = (β^2*(μ.xi 1-(1-x)*μ.xi Q)+
    Real.log (profileConstant x Q/(1-Q))/x+Real.log (1-Q))/2
  replicon : β^2*(1-Q)^2*μ.xi2 Q < 1
  residual_identity : ∀ t ∈ Ioo (0 : ℝ) 1,
    β^2*(physicalResidualMixture μ Q h.overlap_range).xi t+t+Real.log (1-t) =
      -CSStructure.potential μ β (twoAtom x Q) (Q+(1-Q)*t)
  residual_strict : ∀ t ∈ Ioo (0 : ℝ) 1,
    β^2*(physicalResidualMixture μ Q h.overlap_range).xi t+t+Real.log (1-t) < 0
  residual_margin : ∃ κ : ℝ, 0 < κ ∧ ∀ t ∈ Ioo (0 : ℝ) 1,
    κ*t^2 ≤ CSStructure.potential μ β (twoAtom x Q) (Q+(1-Q)*t)
  residual_law : (CSParisiMeasure.canonicalMinimizer
    (physicalResidualMixture μ Q h.overlap_range) β).law = Measure.dirac (0 : ℝ)
  residual_curvature : β^2*(physicalResidualMixture μ Q h.overlap_range).xi2 0 < 1
  residual_pressure : D.residual Q = β^2*residualAtOne μ Q/2
  ground_minimizer : ∀ v : RadiusGroundProfile Q,
    radiusFunctional μ (groundTrial (CSParisiMeasure.canonicalMinimizer μ β)
      h.beta_pos h.overlap_range (le_refl (0 : ℝ))) ≤ radiusFunctional μ v
  ground_unique : ∀ v : RadiusGroundProfile Q,
    (∀ w : RadiusGroundProfile Q, radiusFunctional μ v ≤ radiusFunctional μ w) →
    ∀ r ∈ Icc (0 : ℝ) Q, radiusProfile v r = β*(profileConstant x Q-x*r)
  ground_energy : D.ground Q = markE μ β x Q
  ground_endpoints : CSStructure.potential μ β (twoAtom x Q) (Q*0)/β^2 = 0 ∧
    CSStructure.potential μ β (twoAtom x Q) (Q*1)/β^2 = 0
  ground_positive : ∀ r ∈ Ioo (0 : ℝ) 1,
    0 < CSStructure.potential μ β (twoAtom x Q) (Q*r)/β^2
  ground_formula : ∀ r ∈ Icc (0 : ℝ) 1,
    CSStructure.potential μ β (twoAtom x Q) (Q*r)/β^2 =
      μ.xi Q-μ.xi (Q*r)-markA μ Q*((1+markZ x Q)/(markZ x Q)^2 *
        Real.log (1+(1-r)*markZ x Q)-(1-r)/markZ x Q)
  marks : (markY β Q)^2 = (1+markZ x Q)*markA μ Q ∧
    μ.xi Q/markA μ Q = ((1+markZ x Q)*Real.log (1+markZ x Q)-markZ x Q)/(markZ x Q)^2 ∧
    markZ x Q/markY β Q = β*x ∧ β*x < β
  edge : markB μ Q/(markY β Q)^2 = β^2*(1-Q)^2*μ.xi2 Q ∧
    markB μ Q/(markY β Q)^2 < 1 ∧
    markK μ β Q-2*Real.sqrt (markB μ Q) =
      (markY β Q-Real.sqrt (markB μ Q))^2/markY β Q ∧
    0 < markK μ β Q-2*Real.sqrt (markB μ Q)
  tap_identity : D.pressure = β*markE μ β x Q+Real.log (1-Q)/2+β^2*residualAtOne μ Q/2
  multisamplable : ∀ q ∈ Ico (0 : ℝ) 1, MultiSamplable μ β q ↔ q = 0 ∨ q = Q
  tap_gap : ∀ q ∈ Ioo (0 : ℝ) 1, q ≠ Q →
    tapValue D q ≤ D.pressure-(CSStructure.potential μ β (twoAtom x Q) q)^2 /
      (8*β^3*curvature β (twoAtom x Q) q)

/-- The complete general finite-mixture static-structure assembly, conditional
on the existing Chen, Chen–Sen and Subag Theorems 5 and 10 interfaces. -/
theorem strict_oneStep_structure (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround) {μ : FiniteMixture} {β x Q : ℝ}
    (h : Certificate μ β x Q) (D : ThermodynamicData μ β)
    (h5 : LiteratureSubagTAP.Theorem5 D) (h10 : Theorem10Forward μ β) :
    StrictOneStepConclusions h D := by
  have hP := tendsto_nhds_unique D.pressure_limit (hChen μ β h.beta_pos.le)
  have hR : D.residual Q = β^2*residualAtOne μ Q/2 :=
    tendsto_nhds_unique (D.residual_limit Q h.overlap_range)
      (SphericalTAPResidual.residual_physical_pressure h)
  have hV : CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law Q = 0 := by
    rw [h.canonical_law]; exact h.contact_value
  have hground := contact_ground_profile_unique hChen hChenSen D h5 h10 h.overlap_range hV
  have hG : D.ground Q = markE μ β x Q := by
    have ht := (h5.2 Q h.overlap_range).1.mpr
      (multiSamplable_of_zero_potential h10 ⟨h.overlap_range.1.le,h.overlap_range.2⟩ hV)
    unfold tapValue at ht
    rw [hP, h.variational_TAP, hR] at ht
    nlinarith [h.beta_pos]
  refine ⟨h.canonical_law, h.contact_equations, hP.trans h.variational_pressure, ?_,
    ?_, ?_, SphericalTAPResidualMargin.certificate_residual_margin h,
    SphericalTAPResidual.residual_canonical_law h, SphericalTAPResidual.residual_replicon_lt_one h,
    hR, hground.1, ?_, hG, ?_, ?_, ?_, ?_, ?_, hP.trans h.variational_TAP, ?_, ?_⟩
  · rw [← markB_div_markY_sq μ h.beta_pos h.overlap_range]
    exact h.edge_margin.1
  · intro t ht
    exact SphericalTAPResidual.residual_Phi_eq_neg_potential h ht
  · intro t ht
    exact SphericalTAPResidual.residual_Phi_neg h t ht
  · intro v hv r hr
    rw [hground.2.2 v hv r hr, h.canonical_law]
    have he := CSTAPTelescope.xHat_twoAtom_le
      ⟨h.weight_range.1.le,h.weight_range.2.le⟩ hr
    rw [he]
    rfl
  · constructor
    · have ho := (ThermalPhysicalZeroContact.canonical_zero_contact μ β).1
      rw [h.canonical_law] at ho
      simp only [mul_zero, ho, zero_div]
    · simp only [mul_one, h.contact_value, zero_div]
  · intro r hr
    have hQr : Q*r ∈ Ioo (0 : ℝ) 1 :=
      ⟨mul_pos h.overlap_range.1 hr.1,
        (mul_lt_of_lt_one_right h.overlap_range.1 hr.2).trans h.overlap_range.2⟩
    exact div_pos (h.positive_off_contact _ hQr
      (ne_of_lt (mul_lt_of_lt_one_right h.overlap_range.1 hr.2))) (sq_pos_of_pos h.beta_pos)
  · exact fun r hr => certificate_ground_potential_formula h hr
  · exact ⟨markY_sq_from_contact μ h.beta_pos h.weight_range h.overlap_range
      h.contact_value h.contact_derivative, certificate_mark_ratio h,
      markZ_div_markY h.beta_pos h.overlap_range,
      (mul_lt_mul_of_pos_left h.weight_range.2 h.beta_pos).trans_le (by simp)⟩
  · exact ⟨markB_div_markY_sq μ h.beta_pos h.overlap_range, h.edge_margin⟩
  · intro q hq
    rw [contact_iff_multiSamplable hChen hChenSen D h5 h10 hq, h.canonical_law]
    constructor
    · intro hz
      by_cases hq0 : q = 0
      · exact Or.inl hq0
      · right
        by_contra hqQ
        have hp := h.positive_off_contact q ⟨lt_of_le_of_ne hq.1 (Ne.symm hq0), hq.2⟩ hqQ
        rw [hz] at hp
        exact (lt_irrefl 0) hp
    · rintro (rfl | rfl)
      · have ho := (ThermalPhysicalZeroContact.canonical_zero_contact μ β).1
        rwa [h.canonical_law] at ho
      · exact h.contact_value
  · intro q hq hqQ
    have hg := tapValue_le_pressure_sub_gap hChen hChenSen h.beta_pos D hq
      (by rw [h.canonical_law]; exact h.positive_off_contact q hq hqQ)
    simpa only [h.canonical_law] using hg


/-- The literal positive compact infimum in `thm:th-contact`(3), with the
nonnegative extended-real convention that also handles the empty compact set. -/
theorem compact_inf_contact_gap (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β)
    {K : Set ℝ} (hK : IsCompact K) (hKsub : K ⊆ Ioo (0 : ℝ) 1)
    (hKzero : ∀ q ∈ K,
      CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q ≠ 0) :
    0 < ⨅ q : K, ENNReal.ofReal
      ((CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q)^2 /
        curvature β (CSParisiMeasure.canonicalMinimizer μ β).law q) := by
  obtain ⟨c, hc, hb⟩ := compact_uniform_contact_gap μ hβ hK hKsub hKzero
  exact (ENNReal.ofReal_pos.mpr hc).trans_le (le_iInf (fun q =>
    ENNReal.ofReal_le_ofReal (hb q q.property)))

/-- The general contact gap is uniform in the physical TAP value on every
compact subset of the positive noncontact region. Only Chen and Chen–Sen enter. -/
theorem compact_uniform_tap_gap (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround) {μ : FiniteMixture} {β : ℝ} (hβ : 0 < β)
    (D : ThermodynamicData μ β) {K : Set ℝ} (hK : IsCompact K)
    (hKsub : K ⊆ Ioo (0 : ℝ) 1)
    (hKzero : ∀ q ∈ K,
      CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ K, tapValue D q ≤ D.pressure-δ := by
  obtain ⟨c, hc, hb⟩ := compact_uniform_contact_gap μ hβ hK hKsub hKzero
  refine ⟨c/(8*β^3), by positivity, ?_⟩
  intro q hq
  have hV : 0 < CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q :=
    lt_of_le_of_ne ((ThermalPhysicalZeroContact.canonical_zero_contact μ β).2.1 q
      ⟨(hKsub hq).1.le, (hKsub hq).2⟩) (Ne.symm (hKzero q hq))
  have hg := tapValue_le_pressure_sub_gap hChen hChenSen hβ D (hKsub hq) hV
  have hscale :
      (CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q)^2 /
          (8*β^3*curvature β (CSParisiMeasure.canonicalMinimizer μ β).law q) =
        ((CSStructure.potential μ β (CSParisiMeasure.canonicalMinimizer μ β).law q)^2 /
          curvature β (CSParisiMeasure.canonicalMinimizer μ β).law q)/(8*β^3) := by ring
  rw [hscale] at hg
  exact hg.trans (sub_le_sub_left (div_le_div_of_nonneg_right (hb q hq) (by positivity)) _)

end SlowEquilibration.SourceGeneralContactTheorem

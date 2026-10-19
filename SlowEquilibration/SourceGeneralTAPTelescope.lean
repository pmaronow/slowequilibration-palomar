-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSTAPTelescope

/-!
# The TAP telescope for arbitrary admissible measures

The decomposition `eq:th-telescope` in Section 5 of the manuscript holds for
an arbitrary admissible probability law, without a restriction on the number
of its atoms. The residual measure is the literal image under the truncated
affine map in `eq:th-residual-measure`.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceGeneralTAPTelescope

open MeasureTheory Set CrisantiSommers

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The manuscript's truncated affine residual map. -/
def residualMap (q r : ℝ) : ℝ := max 0 ((r - q) / (1 - q))

theorem residualMap_continuous (q : ℝ) : Continuous (residualMap q) := by
  unfold residualMap
  fun_prop

theorem residualMap_mem {q Q r : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hr : r ∈ Icc (0 : ℝ) Q) :
    residualMap q r ∈ Icc (0 : ℝ) (residualMap q Q) := by
  refine ⟨le_max_left _ _, max_le_max_left 0 ?_⟩
  exact div_le_div_of_nonneg_right (sub_le_sub_right hr.2 q) (by linarith [hq.2])

theorem residualMap_lt_one {q Q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hQ : Q < 1) : residualMap q Q < 1 := by
  apply max_lt (by norm_num)
  rw [div_lt_one (by linarith [hq.2])]
  linarith

/-- The actual pushforward measure, valid for every admissible law. -/
def residualTrial (ζ : Admissible) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) : Admissible where
  law := ζ.law.map (residualMap q)
  probability := (Measure.isProbabilityMeasure_map_iff
    (residualMap_continuous q).measurable.aemeasurable).mpr inferInstance
  cutoff_exists := by
    refine ⟨residualMap q ζ.cutoff, le_max_left _ _,
      residualMap_lt_one hq ζ.hasCutoff.2.1, ?_⟩
    exact (ae_map_iff (residualMap_continuous q).measurable.aemeasurable
      measurableSet_Icc).mpr
        (ζ.hasCutoff.2.2.mono (fun r hr => residualMap_mem hq hr))

theorem residualTrial_hasCutoff (ζ : Admissible) {q Q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (hQ : HasCutoff ζ.law Q) :
    HasCutoff (residualTrial ζ hq).law (residualMap q Q) := by
  refine ⟨le_max_left _ _, residualMap_lt_one hq hQ.2.1, ?_⟩
  exact (ae_map_iff (residualMap_continuous q).measurable.aemeasurable
    measurableSet_Icc).mpr
      (hQ.2.2.mono (fun r hr => residualMap_mem hq hr))

/-- The defining distribution-function identity for the residual law. -/
theorem residualTrial_distribution (ζ : Admissible) {q t : ℝ}
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
theorem residualTrial_atom_zero (ζ : Admissible) {q : ℝ}
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
theorem residual_xHat_scale (ζ : Admissible) {q t : ℝ}
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
theorem residual_inverse_integral (ζ : Admissible) {q Q : ℝ}
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
theorem residual_entropy (ζ : Admissible) {q Q : ℝ}
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
theorem energy_kernel_identity (μ : FiniteMixture) {q r : ℝ}
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
theorem residual_energy (μ : FiniteMixture) (ζ : Admissible) {q : ℝ}
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
theorem ground_trial_value (μ : FiniteMixture) (ζ : Admissible) {β q : ℝ}
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
theorem telescope (μ : FiniteMixture) (ζ : Admissible) {β q : ℝ}
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
theorem canonical_telescope (μ : FiniteMixture) {β q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Ioo (0 : ℝ) 1) :
    CSParisiMeasure.variationalValue μ β =
      β * CSTAPGroundTrialQuadratic.functional μ β (CSParisiMeasure.canonicalMinimizer μ β).law q 0 +
        Real.log (1 - q) / 2 +
          (residualTrial (CSParisiMeasure.canonicalMinimizer μ β) hq).value β
            (CSTAPTelescope.residualMixture μ hq).xi :=
  telescope μ (CSParisiMeasure.canonicalMinimizer μ β) hβ hq

end SlowEquilibration.SourceGeneralTAPTelescope

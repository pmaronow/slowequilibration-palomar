-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSTAPGroundTrialQuadratic
public import SlowEquilibration.FiniteMixtureTaylorResidual

/-!
# The Crisanti–Sommers telescope at a positive overlap

Source Section 5, proof of the contact theorem, equation
`eq:th-telescope`: for every `q ∈ (0,1)`,
`F(β) = β 𝒬_q(ℓ_q) + ½ log(1-q) + 𝒫_β(ζ_{β,q}; ψ_q)`.
Here `ℓ_q = β x̂` is the ground trial profile on `[0,q]`, `ψ_q` is the exact
Taylor residual covariance, and `ζ_{β,q}` is the image of the Parisi measure
under `τ(r) = max 0 ((r-q)/(1-q))`.

Under the strict one-step certificate the Parisi measure is the literal
two-atom law `x δ₀ + (1-x) δ_Q`, and `ζ_{β,q}` is again a two-atom law,
with second atom `max 0 ((Q-q)/(1-q))`. Both sides are computed exactly.
No thermodynamic limit enters this file.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.CSTAPTelescope

open MeasureTheory Set CrisantiSommers SphericalTAPCertificate
open CSTAPGroundTrialQuadratic

set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem xi1_zero (μ : FiniteMixture) : μ.xi1 0 = 0 := by
  unfold FiniteMixture.xi1
  apply Finset.sum_eq_zero
  intro p hp
  have hp2 := μ.degree_ge_two hp
  rw [zero_pow (show p - 1 ≠ 0 by omega), mul_zero]

/-- The image of the second atom under `τ(r) = max 0 ((r-q)/(1-q))`. -/
def residualAtom (Q q : ℝ) : ℝ := max 0 ((Q - q) / (1 - q))

theorem residualAtom_mem {Q q : ℝ} (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (hq : q ∈ Ioo (0 : ℝ) 1) : residualAtom Q q ∈ Ico (0 : ℝ) 1 := by
  refine ⟨le_max_left _ _, max_lt (by norm_num) ?_⟩
  rw [div_lt_one (by linarith [hq.2])]
  linarith [hQ.2]

/-- The source residual trial measure `ζ_{β,q}` of a two-atom law. -/
def residualTrial {x Q q : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hQ : Q ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) : Admissible :=
  twoAtomAdmissible ⟨hx.1.le, hx.2.le⟩ (residualAtom_mem hQ hq)

/-- The source residual covariance `ψ_q`. -/
def residualMixture (μ : FiniteMixture) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    FiniteMixture :=
  μ.taylorResidual hq.1 (sub_pos.mpr hq.2)

theorem residualMixture_xi (μ : FiniteMixture) {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    (residualMixture μ hq).xi t =
      μ.xi (q + (1 - q) * t) - μ.xi q - (1 - q) * μ.xi1 q * t :=
  FiniteMixture.taylorResidual_xi μ hq.1 (sub_pos.mpr hq.2) t

/-! ### The two-atom profile -/

theorem xHat_twoAtom_le {x Q v : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) Q) :
    xHat (twoAtom x Q) v = (1 - Q + x * Q) - x * v := by
  rw [xHat_twoAtom hx hv.1, ite_eq_left hv.2]

theorem xHat_twoAtom_ge {x Q v : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hQ : 0 ≤ Q) (hv : Q ≤ v) :
    xHat (twoAtom x Q) v = 1 - v := by
  rw [xHat_twoAtom hx (hQ.trans hv)]
  split_ifs with h
  · have : v = Q := le_antisymm h hv
    subst this
    ring
  · rfl

/-! ### Energy part of the ground trial -/

private theorem linear_hasDerivAt (C x v : ℝ) :
    HasDerivAt (fun w : ℝ => C - x * w) (-x) v := by
  simpa using ((hasDerivAt_id v).const_mul x).const_sub C

/-- `∫₀^b ξ''(v) (C - x v) dv = ξ'(b)(C - x b) + x ξ(b)`. -/
theorem integral_xi2_mul_linear (μ : FiniteMixture) (C x b : ℝ) :
    (∫ v in (0 : ℝ)..b, μ.xi2 v * (C - x * v)) =
      μ.xi1 b * (C - x * b) + x * μ.xi b := by
  have hxi2 : Continuous μ.xi2 := continuous_iff_continuousAt.mpr
    (fun v => (μ.hasDerivAt_xi2 v).continuousAt)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun v => μ.xi1 v * (C - x * v) + x * μ.xi v)]
  · simp [xi1_zero, FiniteMixture.xi_zero]
  · intro v _
    have h := ((μ.hasDerivAt_xi1 v).mul (linear_hasDerivAt C x v)).add
      ((μ.hasDerivAt_xi v).const_mul x)
    convert h using 1
    ring
  · exact (hxi2.mul (continuous_const.sub (continuous_const.mul continuous_id))).intervalIntegrable _ _

/-- `∫_a^b ξ''(v)(1 - v) dv = [ξ'(v)(1-v) + ξ(v)]_a^b`. -/
theorem integral_xi2_mul_one_sub (μ : FiniteMixture) (a b : ℝ) :
    (∫ v in a..b, μ.xi2 v * (1 - v)) =
      (μ.xi1 b * (1 - b) + μ.xi b) - (μ.xi1 a * (1 - a) + μ.xi a) := by
  have hxi2 : Continuous μ.xi2 := continuous_iff_continuousAt.mpr
    (fun v => (μ.hasDerivAt_xi2 v).continuousAt)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun v => μ.xi1 v * (1 - v) + μ.xi v)
  · intro v _
    have h := ((μ.hasDerivAt_xi1 v).mul (linear_hasDerivAt 1 1 v)).add
      (μ.hasDerivAt_xi v)
    convert h using 1
    · funext w
      simp only [Pi.add_apply, Pi.mul_apply, one_mul]
    · ring
  · exact (hxi2.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _

/-- The energy integral of the zero-temperature trial `β x̂` on `[0,q]`. -/
theorem ground_energy_twoAtom (μ : FiniteMixture) {x Q q : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hQ : Q ∈ Ioo (0 : ℝ) 1) (hq : 0 ≤ q) :
    (∫ v in (0 : ℝ)..q, μ.xi2 v * xHat (twoAtom x Q) v) =
      if q ≤ Q then μ.xi1 q * (1 - Q + x * Q - x * q) + x * μ.xi q
      else μ.xi1 q * (1 - q) + μ.xi q - (1 - x) * μ.xi Q := by
  have hxi2 : Continuous μ.xi2 := continuous_iff_continuousAt.mpr
    (fun v => (μ.hasDerivAt_xi2 v).continuousAt)
  have : IsProbabilityMeasure (twoAtom x Q) := twoAtom_probability hx
  have hcut : HasCutoff (twoAtom x Q) Q := twoAtom_hasCutoff ⟨hQ.1.le, hQ.2⟩
  have hint (a b : ℝ) : IntervalIntegrable
      (fun v => μ.xi2 v * xHat (twoAtom x Q) v) volume a b :=
    (hxi2.mul (xHat_continuous _ hcut)).intervalIntegrable _ _
  split_ifs with hqQ
  · rw [intervalIntegral.integral_congr (g := fun v => μ.xi2 v * ((1 - Q + x * Q) - x * v))]
    · exact integral_xi2_mul_linear μ _ x q
    · intro v hv
      rw [uIcc_of_le hq] at hv
      simp only
      rw [xHat_twoAtom_le hx ⟨hv.1, hv.2.trans hqQ⟩]
  · have hQq : Q ≤ q := (lt_of_not_ge hqQ).le
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 Q) (hint Q q)]
    rw [intervalIntegral.integral_congr (a := 0) (b := Q)
      (g := fun v => μ.xi2 v * ((1 - Q + x * Q) - x * v))]
    · rw [intervalIntegral.integral_congr (a := Q) (b := q)
        (g := fun v => μ.xi2 v * (1 - v))]
      · rw [integral_xi2_mul_linear, integral_xi2_mul_one_sub]
        ring
      · intro v hv
        rw [uIcc_of_le hQq] at hv
        simp only
        rw [xHat_twoAtom_ge hx hQ.1.le hv.1]
    · intro v hv
      rw [uIcc_of_le hQ.1.le] at hv
      simp only
      rw [xHat_twoAtom_le hx hv]

/-! ### Entropy part -/

set_option linter.unusedVariables false in
/-- Below the second atom, the residual profile is the rescaled original
profile: `(1-q) x̂_{ζ_{β,q}}(t) = x̂(q + (1-q) t)`. -/
theorem residual_xHat_scale {x Q q t : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hq : q ∈ Ioo (0 : ℝ) 1) (hqQ : q ≤ Q)
    (ht : t ∈ Icc (0 : ℝ) ((Q - q) / (1 - q))) :
    (1 - q) * xHat (twoAtom x ((Q - q) / (1 - q))) t =
      xHat (twoAtom x Q) ((1 - q) * t + q) := by
  have hs : 0 < 1 - q := sub_pos.mpr hq.2
  have hst : (1 - q) * t ≤ Q - q := by
    have := mul_le_mul_of_nonneg_left ht.2 hs.le
    rwa [mul_div_cancel₀ _ hs.ne'] at this
  have hlo : 0 ≤ (1 - q) * t + q := by
    have := mul_nonneg hs.le ht.1
    linarith [hq.1]
  rw [xHat_twoAtom_le hx ht, xHat_twoAtom_le hx ⟨hlo, by linarith⟩]
  field_simp [hs.ne']
  ring

set_option linter.unusedVariables false in
theorem integral_inv_residual_profile {x Q q : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hQ : Q ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) (hqQ : q ≤ Q) :
    (∫ t in (0 : ℝ)..((Q - q) / (1 - q)),
        (xHat (twoAtom x ((Q - q) / (1 - q))) t)⁻¹) =
      ∫ v in q..Q, (xHat (twoAtom x Q) v)⁻¹ := by
  have hs : 0 < 1 - q := sub_pos.mpr hq.2
  have hQ' : 0 ≤ (Q - q) / (1 - q) := div_nonneg (sub_nonneg.mpr hqQ) hs.le
  have hcongr : ∀ t ∈ uIcc (0 : ℝ) ((Q - q) / (1 - q)),
      (xHat (twoAtom x ((Q - q) / (1 - q))) t)⁻¹ =
        (1 - q) * (xHat (twoAtom x Q) ((1 - q) * t + q))⁻¹ := by
    intro t ht
    rw [uIcc_of_le hQ'] at ht
    rw [← residual_xHat_scale hx hq hqQ ht, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ hs.ne', one_mul]
  have hsub : (∫ t in (0 : ℝ)..((Q - q) / (1 - q)),
      (xHat (twoAtom x Q) ((1 - q) * t + q))⁻¹) =
      (1 - q)⁻¹ * ∫ v in ((1 - q) * 0 + q)..((1 - q) * ((Q - q) / (1 - q)) + q),
        (xHat (twoAtom x Q) v)⁻¹ :=
    intervalIntegral.integral_comp_mul_add (f := fun v => (xHat (twoAtom x Q) v)⁻¹)
      hs.ne' q
  have hend : (1 - q) * ((Q - q) / (1 - q)) + q = Q := by
    field_simp [hs.ne']
    ring
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul, hsub,
    mul_zero, zero_add, hend, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]

theorem integral_inv_one_sub {a b : ℝ} (hab : a ≤ b) (hb : b < 1) :
    (∫ v in a..b, (1 - v)⁻¹) = Real.log (1 - a) - Real.log (1 - b) := by
  have hpos : ∀ v ∈ uIcc a b, 1 - v ≠ 0 := by
    intro v hv
    rw [uIcc_of_le hab] at hv
    exact (sub_pos.mpr (hv.2.trans_lt hb)).ne'
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun v : ℝ => -Real.log (1 - v))
    (a := a) (b := b) (f' := fun v => (1 - v)⁻¹)
    (fun v hv => by
      convert (((hasDerivAt_id v).const_sub 1).log (hpos v hv)).neg using 1
      · funext w
        simp only [Pi.neg_apply, id_eq]
      · simp only [id_eq, neg_div, neg_neg, one_div])
    ((continuous_const.sub continuous_id).continuousOn.inv₀ hpos).intervalIntegrable
  simpa only [neg_sub_neg] using h

/-! ### The telescope identity -/

/-- The certificate's Parisi value, at the cutoff `Q`. -/
theorem variationalValue_certificate {μ : FiniteMixture} {β x Q : ℝ}
    (h : Certificate μ β x Q) :
    CSParisiMeasure.variationalValue μ β =
      (β ^ 2 * (μ.xi 1 - (1 - x) * μ.xi Q) +
        (∫ t in (0 : ℝ)..Q, (xHat (twoAtom x Q) t)⁻¹) + Real.log (1 - Q)) / 2 := by
  have hx : x ∈ Icc (0 : ℝ) 1 := ⟨h.weight_range.1.le, h.weight_range.2.le⟩
  have hcut : HasCutoff (CSParisiMeasure.canonicalMinimizer μ β).law Q := by
    rw [h.canonical_law]
    exact twoAtom_hasCutoff ⟨h.overlap_range.1.le, h.overlap_range.2⟩
  unfold CSParisiMeasure.variationalValue
  rw [(CSParisiMeasure.canonicalMinimizer μ β).value_eq β μ.xi hcut,
    CrisantiSommers.functional, h.canonical_law, integral_twoAtom hx,
    FiniteMixture.xi_zero]
  ring

/-- The residual trial value. -/
theorem residualTrial_value (μ : FiniteMixture) {β x Q q : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hQ : Q ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    (residualTrial hx hQ hq).value β (residualMixture μ hq).xi =
      (β ^ 2 * ((residualMixture μ hq).xi 1 -
          (1 - x) * (residualMixture μ hq).xi (residualAtom Q q)) +
        (∫ t in (0 : ℝ)..residualAtom Q q,
          (xHat (twoAtom x (residualAtom Q q)) t)⁻¹) +
        Real.log (1 - residualAtom Q q)) / 2 := by
  have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have hres0 : (residualMixture μ hq).xi 0 = 0 := FiniteMixture.xi_zero _
  have hcut := twoAtom_hasCutoff (x := x) (residualAtom_mem hQ hq)
  rw [residualTrial, Admissible.value_eq
    (twoAtomAdmissible ⟨hx.1.le, hx.2.le⟩ (residualAtom_mem hQ hq)) β _ hcut]
  change CrisantiSommers.functional β _ (twoAtom x (residualAtom Q q)) (residualAtom Q q) = _
  rw [CrisantiSommers.functional, integral_twoAtom hx', hres0]
  ring

/-- The zero-temperature trial value at `ε = 0`, split into energy and
entropy. -/
theorem ground_trial_value (μ : FiniteMixture) {β x Q q : ℝ} (hβ : 0 < β)
    (hx : x ∈ Icc (0 : ℝ) 1) (hQ : Q ∈ Ioo (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    β * functional μ β (twoAtom x Q) q 0 =
      (β ^ 2 * (∫ v in (0 : ℝ)..q, μ.xi2 v * xHat (twoAtom x Q) v) +
        ∫ v in (0 : ℝ)..q, (xHat (twoAtom x Q) v)⁻¹) / 2 := by
  have hxi2 : Continuous μ.xi2 := continuous_iff_continuousAt.mpr
    (fun v => (μ.hasDerivAt_xi2 v).continuousAt)
  have : IsProbabilityMeasure (twoAtom x Q) := twoAtom_probability hx
  have hcut : HasCutoff (twoAtom x Q) Q := twoAtom_hasCutoff ⟨hQ.1.le, hQ.2⟩
  have hxc : Continuous (xHat (twoAtom x Q)) := xHat_continuous _ hcut
  have hxpos : ∀ v ∈ uIcc (0 : ℝ) q, xHat (twoAtom x Q) v ≠ 0 := by
    intro v hv
    rw [uIcc_of_le hq.1.le] at hv
    exact (xHat_pos _ hcut (hv.2.trans_lt hq.2)).ne'
  have hinv : IntervalIntegrable (fun v => (xHat (twoAtom x Q) v)⁻¹) volume 0 q :=
    (ContinuousOn.inv₀ hxc.continuousOn hxpos).intervalIntegrable
  have hE : IntervalIntegrable (fun v => μ.xi2 v * xHat (twoAtom x Q) v) volume 0 q :=
    (hxi2.mul hxc).intervalIntegrable _ _
  unfold CSTAPGroundTrialQuadratic.functional profile
  simp only [zero_mul, add_zero]
  have hsplit : (∫ v in (0 : ℝ)..q,
      μ.xi2 v * (β * xHat (twoAtom x Q) v) + (β * xHat (twoAtom x Q) v)⁻¹) =
      β * (∫ v in (0 : ℝ)..q, μ.xi2 v * xHat (twoAtom x Q) v) +
        β⁻¹ * ∫ v in (0 : ℝ)..q, (xHat (twoAtom x Q) v)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hE.const_mul β) (hinv.const_mul β⁻¹)]
    apply intervalIntegral.integral_congr
    intro v _
    simp only [mul_inv]
    ring
  rw [hsplit]
  field_simp [hβ.ne']

/-- Source `eq:th-telescope` for a strict one-step certificate, at every
`q ∈ (0,1)`. -/
theorem telescope {μ : FiniteMixture} {β x Q : ℝ} (h : Certificate μ β x Q)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    CSParisiMeasure.variationalValue μ β =
      β * functional μ β (twoAtom x Q) q 0 + Real.log (1 - q) / 2 +
        (residualTrial h.weight_range h.overlap_range hq).value β
          (residualMixture μ hq).xi := by
  have hx : x ∈ Icc (0 : ℝ) 1 := ⟨h.weight_range.1.le, h.weight_range.2.le⟩
  have hQ := h.overlap_range
  have hs : 0 < 1 - q := sub_pos.mpr hq.2
  have : IsProbabilityMeasure (twoAtom x Q) := twoAtom_probability hx
  have hcut : HasCutoff (twoAtom x Q) Q := twoAtom_hasCutoff ⟨hQ.1.le, hQ.2⟩
  have hxc : Continuous (xHat (twoAtom x Q)) := xHat_continuous _ hcut
  have hinv (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a < 1) (hb1 : b < 1) :
      IntervalIntegrable (fun v => (xHat (twoAtom x Q) v)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply hxc.continuousOn.inv₀
    intro v hv
    have hv1 : v < 1 := by
      rcases le_total a b with hab | hab
      · rw [uIcc_of_le hab] at hv; exact hv.2.trans_lt hb1
      · rw [uIcc_of_ge hab] at hv; exact hv.2.trans_lt ha1
    exact (xHat_pos _ hcut hv1).ne'
  rw [variationalValue_certificate h, ground_trial_value μ h.beta_pos hx hQ hq,
    residualTrial_value μ h.weight_range hQ hq, ground_energy_twoAtom μ hx hQ hq.1.le]
  simp only [residualMixture_xi]
  by_cases hqQ : q ≤ Q
  · rw [ite_eq_left hqQ]
    have hatom : residualAtom Q q = (Q - q) / (1 - q) :=
      max_eq_right (div_nonneg (sub_nonneg.mpr hqQ) hs.le)
    rw [hatom, integral_inv_residual_profile hx hQ hq hqQ,
      ← intervalIntegral.integral_add_adjacent_intervals
        (hinv 0 q le_rfl hq.1.le (by norm_num) hq.2)
        (hinv q Q hq.1.le hQ.1.le hq.2 hQ.2)]
    have hlog : Real.log (1 - (Q - q) / (1 - q)) + Real.log (1 - q) =
        Real.log (1 - Q) := by
      rw [← Real.log_mul]
      · congr 1
        field_simp
        ring
      · have : (Q - q) / (1 - q) < 1 := by
          rw [div_lt_one hs]; linarith [hQ.2]
        linarith
      · exact hs.ne'
    have hpt : q + (1 - q) * ((Q - q) / (1 - q)) = Q := by
      field_simp
      ring
    rw [hpt, ← hlog]
    have hone : q + (1 - q) * 1 = 1 := by ring
    rw [hone]
    field_simp [hs.ne']
    ring
  · rw [ite_eq_right hqQ]
    have hQq : Q ≤ q := (lt_of_not_ge hqQ).le
    have hatom : residualAtom Q q = 0 :=
      max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hs.le)
    rw [hatom, ← intervalIntegral.integral_add_adjacent_intervals
        (hinv 0 Q le_rfl hQ.1.le (by norm_num) hQ.2)
        (hinv Q q hQ.1.le hq.1.le hQ.2 hq.2)]
    rw [intervalIntegral.integral_congr (a := Q) (b := q)
      (g := fun v => (1 - v)⁻¹)]
    · rw [integral_inv_one_sub hQq hq.2]
      simp only [intervalIntegral.integral_same, sub_zero, Real.log_one, mul_zero,
        add_zero]
      have hone : q + (1 - q) * 1 = 1 := by ring
      rw [hone]
      ring
    · intro v hv
      rw [uIcc_of_le hQq] at hv
      simp only
      rw [xHat_twoAtom_ge hx hQ.1.le hv.1]

end SlowEquilibration.CSTAPTelescope

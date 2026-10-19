-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CrisantiSommers
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The Crisanti--Sommers supporting inequality

This file proves the variational lower bound directly from the ordinary
Crisanti--Sommers functional. All distribution functions, potentials,
probability measures and integrals are the definitions in `CrisantiSommers`.
-/

@[expose] public section

namespace SlowEquilibration.CrisantiSommers

open MeasureTheory Set Filter
open scoped Topology

/-- Convexity of the reciprocal in the exact supporting-line form needed
for the entropy term of the functional. -/
theorem reciprocal_supporting_inequality {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    -(y - x) / x ^ 2 ≤ y⁻¹ - x⁻¹ := by
  have hx0 : x ≠ 0 := hx.ne'
  have hy0 : y ≠ 0 := hy.ne'
  apply (div_le_iff₀ (sq_pos_of_pos hx)).mpr
  rw [sub_mul]
  field_simp
  nlinarith [sq_nonneg (x-y)]

private noncomputable def weight (ζ : Measure ℝ) (t : ℝ) : ℝ :=
  ((xHat ζ t)^2)⁻¹

private lemma weight_continuousOn (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q : ℝ} (hq : HasCutoff ζ q) : ContinuousOn (weight ζ) (Icc 0 q) := by
  apply ((xHat_continuous ζ hq).continuousOn.pow 2).inv₀
  intro t ht
  exact pow_ne_zero _ (xHat_pos ζ hq (ht.2.trans_lt hq.2.1)).ne'

private lemma weight_measurable (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q : ℝ} (hq : HasCutoff ζ q) : Measurable (weight ζ) := by
  exact ((xHat_continuous ζ hq).measurable.pow_const 2).inv

private lemma integrable_of_cutoff (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q : ℝ} (hq : HasCutoff μ q) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 q)) : Integrable f μ := by
  have hi := hf.integrableOn_compact isCompact_Icc (μ := μ)
  simpa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hq.2.2] using hi

private lemma weighted_kernel_integrable (μ ζ : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ζ]
    {q : ℝ} (hμ : HasCutoff μ q) (hζ : HasCutoff ζ q) :
    Integrable (fun p : ℝ × ℝ => (1 - max p.1 p.2) * weight ζ p.1)
      ((volume.restrict (Ioc 0 q)).prod μ) := by
  have hqpos : 0 < 1-q := sub_pos.mpr hζ.2.1
  have hk : Measurable (fun p : ℝ × ℝ => (1 - max p.1 p.2) * weight ζ p.1) :=
    (measurable_const.sub (measurable_fst.max measurable_snd)).mul
      ((weight_measurable ζ hζ).comp measurable_fst)
  apply (integrable_const ((1-q)^2)⁻¹).mono'
  · exact hk.aestronglyMeasurable
  · apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hk.norm measurable_const)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    filter_upwards [hμ.2.2] with s hs
    have hx : 0 < xHat ζ t := xHat_pos ζ hζ (ht.2.trans_lt hζ.2.1)
    have hlower := xHat_ge_one_sub_cutoff ζ hζ ht.2
    have hsq : (1-q)^2 ≤ (xHat ζ t)^2 := by nlinarith
    have hw0 : 0 ≤ weight ζ t := by unfold weight; positivity
    have hw1 : weight ζ t ≤ ((1-q)^2)⁻¹ := by
      unfold weight
      exact inv_anti₀ (sq_pos_of_pos hqpos) hsq
    have hf0 : 0 ≤ 1 - max t s := by
      apply sub_nonneg.mpr
      exact (max_le ht.2 hs.2).trans hζ.2.1.le
    have hf1 : 1 - max t s ≤ 1 := by
      have := le_max_left t s
      linarith [ht.1]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hf0 hw0)]
    exact (mul_le_of_le_one_left hw0 hf1).trans hw1

private lemma intervalIntegrable_on_cutoff {q a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 q)) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ q) :
    IntervalIntegrable f volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact hf.mono (fun _ ht => ⟨ha.trans ht.1, ht.2.trans hb⟩)

/-- The kernel in xHat differs from the first-variation triangular kernel
by a term independent of the support point. -/
theorem weighted_kernel_identity {q s : ℝ} {w : ℝ → ℝ}
    (hw : ContinuousOn w (Icc 0 q)) (hs0 : 0 ≤ s) (hsq : s ≤ q) :
    (∫ t in (0:ℝ)..q, (1-max t s)*w t) =
      (∫ t in (0:ℝ)..q, (1-t)*w t) - (∫ t in (0:ℝ)..s, (s-t)*w t) := by
  have hF : ContinuousOn (fun t => (1-max t s)*w t) (Icc 0 q) :=
    (continuous_const.continuousOn.sub
      (continuous_id.max continuous_const).continuousOn).mul hw
  have hA : ContinuousOn (fun t => (1-t)*w t) (Icc 0 q) :=
    (continuous_const.continuousOn.sub continuous_id.continuousOn).mul hw
  have hB : ContinuousOn (fun t => (s-t)*w t) (Icc 0 q) :=
    (continuous_const.continuousOn.sub continuous_id.continuousOn).mul hw
  have hF0s := intervalIntegrable_on_cutoff hF (le_refl 0) hs0 hsq
  have hFsq := intervalIntegrable_on_cutoff hF hs0 hsq (le_refl q)
  have hA0s := intervalIntegrable_on_cutoff hA (le_refl 0) hs0 hsq
  have hAsq := intervalIntegrable_on_cutoff hA hs0 hsq (le_refl q)
  have hB0s := intervalIntegrable_on_cutoff hB (le_refl 0) hs0 hsq
  have heq0s : (∫ t in (0:ℝ)..s, (1-max t s)*w t) =
      (∫ t in (0:ℝ)..s, (1-t)*w t) - (∫ t in (0:ℝ)..s, (s-t)*w t) := by
    rw [← intervalIntegral.integral_sub hA0s hB0s]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [uIcc_of_le hs0] at ht
    rw [max_eq_right ht.2]
    ring
  have heqsq : (∫ t in s..q, (1-max t s)*w t) =
      ∫ t in s..q, (1-t)*w t := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [uIcc_of_le hsq] at ht
    rw [max_eq_left ht.1]
  have hsplitF := intervalIntegral.integral_add_adjacent_intervals hF0s hFsq
  have hsplitA := intervalIntegral.integral_add_adjacent_intervals hA0s hAsq
  rw [heq0s, heqsq] at hsplitF
  linarith

private lemma weighted_kernel_fubini (μ ζ : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ζ]
    {q : ℝ} (hμ : HasCutoff μ q) (hζ : HasCutoff ζ q) :
    (∫ t in (0:ℝ)..q, xHat μ t * weight ζ t) =
      ∫ s, (∫ t in (0:ℝ)..q, (1-max t s)*weight ζ t) ∂μ := by
  have hi := weighted_kernel_integrable μ ζ hμ hζ
  rw [← uIoc_of_le hμ.1] at hi
  have hswap := intervalIntegral_integral_swap
    (f := fun t s => (1-max t s)*weight ζ t) (a := 0) (b := q) (μ := μ) hi
  simpa only [Function.uncurry_def, integral_mul_const, xHat] using hswap

private lemma firstVariation_integrable_and_integral (β : ℝ) (η : ℝ → ℝ)
    (μ ζ : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ζ]
    {q : ℝ} (hμ : HasCutoff μ q) (hζ : HasCutoff ζ q)
    (hη : ContinuousOn η (Icc 0 q)) :
    Integrable (firstVariation β η ζ) μ ∧
      (∫ s, firstVariation β η ζ s ∂μ) = β^2*(∫ s, η s ∂μ) -
        (∫ t in (0:ℝ)..q, (1-t)*weight ζ t) +
        (∫ t in (0:ℝ)..q, xHat μ t*weight ζ t) := by
  let C : ℝ := ∫ t in (0:ℝ)..q, (1-t)*weight ζ t
  let G : ℝ → ℝ := fun s => ∫ t in (0:ℝ)..q, (1-max t s)*weight ζ t
  have hG : Integrable G μ := by
    have h := (weighted_kernel_integrable μ ζ hμ hζ).integral_prod_right
    simpa only [G, intervalIntegral.integral_of_le hμ.1] using h
  have hiη := integrable_of_cutoff μ hμ hη
  have hmodel : Integrable (fun s => β^2*η s-C+G s) μ :=
    ((hiη.const_mul (β^2)).sub (integrable_const C)).add hG
  have heq : (firstVariation β η ζ) =ᵐ[μ] fun s => β^2*η s-C+G s := by
    filter_upwards [hμ.2.2] with s hs
    have h := weighted_kernel_identity (weight_continuousOn ζ hζ) hs.1 hs.2
    change G s = C - (∫ t in (0:ℝ)..s, (s-t)*weight ζ t) at h
    unfold firstVariation
    simp only [div_eq_mul_inv]
    change β^2*η s - (∫ t in (0:ℝ)..s, (s-t)*weight ζ t) = β^2*η s-C+G s
    linarith
  constructor
  · exact hmodel.congr heq.symm
  · have hadd : (∫ s, β^2*η s-C+G s ∂μ) =
        (∫ s, β^2*η s-C ∂μ)+(∫ s, G s ∂μ) :=
      integral_add ((hiη.const_mul (β^2)).sub (integrable_const C)) hG
    have hsub : (∫ s, β^2*η s-C ∂μ) = β^2*(∫ s, η s ∂μ)-C := by
      calc
        (∫ s, β^2*η s-C ∂μ) = (∫ s, β^2*η s ∂μ)-(∫ s, C ∂μ) :=
          integral_sub (hiη.const_mul (β^2)) (integrable_const C)
        _ = β^2*(∫ s, η s ∂μ)-C := by simp [integral_const_mul]
    rw [integral_congr_ae heq, hadd, hsub]
    change β^2 * (∫ s, η s ∂μ) - C + (∫ s, G s ∂μ) = _
    rw [← weighted_kernel_fubini μ ζ hμ hζ]

/-- The first-variation potential is genuinely integrable against every
candidate probability measure with a common cutoff below one. -/
theorem firstVariation_integrable (β : ℝ) (η : ℝ → ℝ)
    (μ ζ : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ζ]
    {q : ℝ} (hμ : HasCutoff μ q) (hζ : HasCutoff ζ q)
    (hη : ContinuousOn η (Icc 0 q)) :
    Integrable (firstVariation β η ζ) μ :=
  (firstVariation_integrable_and_integral β η μ ζ hμ hζ hη).1

/-- Fubini proves the first-variation identity from the xHat kernel;
this is the identity used in the supporting inequality, rather than a premise. -/
theorem firstVariation_integral_identity (β : ℝ) (η : ℝ → ℝ)
    (μ ζ : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ζ]
    {q : ℝ} (hμ : HasCutoff μ q) (hζ : HasCutoff ζ q)
    (hη : ContinuousOn η (Icc 0 q)) :
    (∫ s, firstVariation β η ζ s ∂μ) = β^2*(∫ s, η s ∂μ) -
      (∫ t in (0:ℝ)..q, (1-t)/((xHat ζ t)^2)) +
      (∫ t in (0:ℝ)..q, (xHat μ t)/((xHat ζ t)^2)) := by
  simpa only [weight, div_eq_mul_inv] using
    (firstVariation_integrable_and_integral β η μ ζ hμ hζ hη).2

private lemma reciprocal_integral_supporting (μ ζ : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ζ]
    {q : ℝ} (hμ : HasCutoff μ q) (hζ : HasCutoff ζ q) :
    (∫ t in (0:ℝ)..q, (xHat ζ t)/((xHat ζ t)^2)) -
      (∫ t in (0:ℝ)..q, (xHat μ t)/((xHat ζ t)^2)) ≤
      (∫ t in (0:ℝ)..q, (xHat μ t)⁻¹) -
        (∫ t in (0:ℝ)..q, (xHat ζ t)⁻¹) := by
  have hw := weight_continuousOn ζ hζ
  have hleftζ := intervalIntegrable_on_cutoff
    ((xHat_continuous ζ hζ).continuousOn.mul hw) (le_refl 0) hμ.1 (le_refl q)
  have hleftμ := intervalIntegrable_on_cutoff
    ((xHat_continuous μ hμ).continuousOn.mul hw) (le_refl 0) hμ.1 (le_refl q)
  have hinvμ := inverse_xHat_intervalIntegrable μ hμ (a := 0) (by norm_num) hμ.2.1
  have hinvζ := inverse_xHat_intervalIntegrable ζ hζ (a := 0) (by norm_num) hζ.2.1
  have hmono := intervalIntegral.integral_mono_on hμ.1
    (hleftζ.sub hleftμ) (hinvμ.sub hinvζ) (fun t ht => ?_)
  · have hsubleft : (∫ t in (0:ℝ)..q, xHat ζ t*weight ζ t-xHat μ t*weight ζ t) =
        (∫ t in (0:ℝ)..q, xHat ζ t*weight ζ t) -
          (∫ t in (0:ℝ)..q, xHat μ t*weight ζ t) :=
      intervalIntegral.integral_sub hleftζ hleftμ
    have hsubright : (∫ t in (0:ℝ)..q, (xHat μ t)⁻¹-(xHat ζ t)⁻¹) =
        (∫ t in (0:ℝ)..q, (xHat μ t)⁻¹) - (∫ t in (0:ℝ)..q, (xHat ζ t)⁻¹) :=
      intervalIntegral.integral_sub hinvμ hinvζ
    change (∫ t in (0:ℝ)..q, xHat ζ t*weight ζ t-xHat μ t*weight ζ t) ≤
      (∫ t in (0:ℝ)..q, (xHat μ t)⁻¹-(xHat ζ t)⁻¹) at hmono
    rw [hsubleft, hsubright] at hmono
    simpa only [weight, div_eq_mul_inv] using hmono
  · calc
      xHat ζ t*weight ζ t-xHat μ t*weight ζ t =
          -(xHat μ t-xHat ζ t)/((xHat ζ t)^2) := by
        unfold weight
        rw [div_eq_mul_inv]
        ring
      _ ≤ (xHat μ t)⁻¹-(xHat ζ t)⁻¹ :=
        reciprocal_supporting_inequality (xHat_pos ζ hζ (ht.2.trans_lt hζ.2.1))
          (xHat_pos μ hμ (ht.2.trans_lt hμ.2.1))

/-- The variational inequality `eq:pre-variation-inequality`, proved from
the actual functional by reciprocal convexity and Fubini. -/
theorem functional_variation_inequality (β : ℝ) (η : ℝ → ℝ)
    (μ ζ : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ζ]
    {q : ℝ} (hμ : HasCutoff μ q) (hζ : HasCutoff ζ q)
    (hη : ContinuousOn η (Icc 0 q)) :
    ((∫ s, firstVariation β η ζ s ∂ζ) - (∫ s, firstVariation β η ζ s ∂μ))/2 ≤
      functional β η μ q-functional β η ζ q := by
  have hconv := reciprocal_integral_supporting μ ζ hμ hζ
  have hfζ := firstVariation_integral_identity β η ζ ζ hζ hζ hη
  have hfμ := firstVariation_integral_identity β η μ ζ hμ hζ hη
  unfold functional
  nlinarith

/-- Supporting the measure on maximizers of its first variation forces
minimality among all competitors with the same cutoff. -/
theorem functional_minimal_same_cutoff (β : ℝ) (η : ℝ → ℝ)
    (μ ζ : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ζ]
    {q : ℝ} (hμ : HasCutoff μ q) (hζ : HasCutoff ζ q)
    (hη : ContinuousOn η (Icc 0 q)) (m : ℝ)
    (hmax : ∀ s ∈ Icc 0 q, firstVariation β η ζ s ≤ m)
    (hsupport : ∀ᵐ s ∂ζ, firstVariation β η ζ s = m) :
    functional β η ζ q ≤ functional β η μ q := by
  have hiζ := firstVariation_integrable β η ζ ζ hζ hζ hη
  have hiμ := firstVariation_integrable β η μ ζ hμ hζ hη
  have hζint : (∫ s, firstVariation β η ζ s ∂ζ) = m := by
    rw [integral_congr_ae hsupport]
    simp
  have hμint : (∫ s, firstVariation β η ζ s ∂μ) ≤ m := by
    have h := integral_mono_ae hiμ (integrable_const m)
      (hμ.2.2.mono (fun s hs => hmax s hs))
    simpa using h
  have hvar := functional_variation_inequality β η μ ζ hμ hζ hη
  rw [hζint] at hvar
  linarith

/-- The sufficient direction of the actual Crisanti--Sommers support
criterion, with unrestricted admissible competitor cutoffs. The common
cutoff is constructed, and cutoff independence compares the original
functional values. -/
theorem functional_minimal_of_firstVariation_maximum (β : ℝ) (η : ℝ → ℝ)
    (μ ζ : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ζ]
    {qμ qζ : ℝ} (hμ : HasCutoff μ qμ) (hζ : HasCutoff ζ qζ)
    (hη : ContinuousOn η (Ico 0 1)) (m : ℝ)
    (hmax : ∀ s ∈ Ico 0 1, firstVariation β η ζ s ≤ m)
    (hsupport : ∀ᵐ s ∂ζ, firstVariation β η ζ s = m) :
    functional β η ζ qζ ≤ functional β η μ qμ := by
  let q := max qμ qζ
  have hq1 : q < 1 := max_lt hμ.2.1 hζ.2.1
  have hμq : HasCutoff μ q := hμ.mono (le_max_left _ _) hq1
  have hζq : HasCutoff ζ q := hζ.mono (le_max_right _ _) hq1
  have hηq : ContinuousOn η (Icc 0 q) :=
    hη.mono (fun s hs => ⟨hs.1, hs.2.trans_lt hq1⟩)
  have hmaxq : ∀ s ∈ Icc 0 q, firstVariation β η ζ s ≤ m :=
    fun s hs => hmax s ⟨hs.1, hs.2.trans_lt hq1⟩
  have hmin := functional_minimal_same_cutoff β η μ ζ hμq hζq hηq m hmaxq hsupport
  rw [functional_cutoff_independent ζ β η hζ hζq,
    functional_cutoff_independent μ β η hμ hμq]
  exact hmin

end SlowEquilibration.CrisantiSommers

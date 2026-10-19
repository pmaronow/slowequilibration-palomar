-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSVariation
public import SlowEquilibration.CSTwoAtom
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Mixture derivatives and the necessary support criterion

Mixtures are ordinary nonnegative measures. Their functional is differentiated
within the interval of probability weights, including its boundary at zero.
-/

@[expose] public section

namespace SlowEquilibration.CrisantiSommers

open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- The actual affine mixture of two probability laws, for weights in [0,1]. -/
noncomputable def mixture (ζ μ : Measure ℝ) (t : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1-t) • ζ + ENNReal.ofReal t • μ

theorem mixture_isProbability (ζ μ : Measure ℝ)
    [IsProbabilityMeasure ζ] [IsProbabilityMeasure μ]
    {t : ℝ} (ht : t ∈ Icc 0 1) : IsProbabilityMeasure (mixture ζ μ t) := by
  constructor
  simp only [mixture, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr ht.2) ht.1]
  simp

@[simp] theorem mixture_zero (ζ μ : Measure ℝ) : mixture ζ μ 0 = ζ := by
  simp [mixture]

@[simp] theorem mixture_one (ζ μ : Measure ℝ) : mixture ζ μ 1 = μ := by
  simp [mixture]

theorem mixture_cutoff (ζ μ : Measure ℝ) {q t : ℝ}
    (hζ : HasCutoff ζ q) (hμ : HasCutoff μ q) : HasCutoff (mixture ζ μ t) q := by
  refine ⟨hζ.1, hζ.2.1, ?_⟩
  exact ae_add_measure_iff.mpr ⟨Measure.ae_smul_measure hζ.2.2 _, Measure.ae_smul_measure hμ.2.2 _⟩

/-- Integration against the genuine mixture is affine in its weight. -/
theorem integral_mixture (ζ μ : Measure ℝ) {f : ℝ → ℝ}
    (hζ : Integrable f ζ) (hμ : Integrable f μ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (∫ s, f s ∂mixture ζ μ t) = (1-t)*(∫ s, f s ∂ζ)+t*(∫ s, f s ∂μ) := by
  unfold mixture
  rw [integral_add_measure (hζ.smul_measure ENNReal.ofReal_ne_top)
    (hμ.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure]
  simp [ENNReal.toReal_ofReal (sub_nonneg.mpr ht.2), ENNReal.toReal_ofReal ht.1,
    smul_eq_mul]

/-- The hatted distribution of the actual mixture is exactly affine. -/
theorem xHat_mixture (ζ μ : Measure ℝ) [IsProbabilityMeasure ζ] [IsProbabilityMeasure μ]
    {q t : ℝ} (hζ : HasCutoff ζ q) (hμ : HasCutoff μ q) (ht : t ∈ Icc 0 1) (s : ℝ) :
    xHat (mixture ζ μ t) s = (1-t)*xHat ζ s+t*xHat μ s :=
  integral_mixture ζ μ (kernel_integrable ζ hζ s) (kernel_integrable μ hμ s) ht

private lemma integrable_cutoff (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q : ℝ} (hq : HasCutoff μ q) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 q)) : Integrable f μ := by
  have hi := hf.integrableOn_compact isCompact_Icc (μ := μ)
  simpa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hq.2.2] using hi

private noncomputable def affineHat (ζ μ : Measure ℝ) (t s : ℝ) : ℝ :=
  (1-t)*xHat ζ s+t*xHat μ s

private lemma affineHat_pos (ζ μ : Measure ℝ)
    [IsProbabilityMeasure ζ] [IsProbabilityMeasure μ]
    {q t s : ℝ} (hζ : HasCutoff ζ q) (hμ : HasCutoff μ q)
    (ht : t ∈ Icc 0 1) (hs : s ≤ q) : 0 < affineHat ζ μ t s := by
  have hz := xHat_ge_one_sub_cutoff ζ hζ hs
  have hm := xHat_ge_one_sub_cutoff μ hμ hs
  have hlo := add_le_add (mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left hm ht.1)
  have heq : (1-t)*(1-q)+t*(1-q) = 1-q := by ring
  rw [heq] at hlo
  exact (sub_pos.mpr hζ.2.1).trans_le hlo

private lemma affineHat_inverse_integrable (ζ μ : Measure ℝ)
    [IsProbabilityMeasure ζ] [IsProbabilityMeasure μ]
    {q t : ℝ} (hζ : HasCutoff ζ q) (hμ : HasCutoff μ q) (ht : t ∈ Icc 0 1) :
    Integrable (fun s => (affineHat ζ μ t s)⁻¹) (volume.restrict (Ioc 0 q)) := by
  have : IsProbabilityMeasure (mixture ζ μ t) := mixture_isProbability ζ μ ht
  have hmix := mixture_cutoff ζ μ hζ hμ (t := t)
  have h := inverse_xHat_intervalIntegrable (mixture ζ μ t) hmix
    (a := 0) (b := q) (by norm_num) hζ.2.1
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hζ.1] at h
  simpa only [IntegrableOn, xHat_mixture ζ μ hζ hμ ht, affineHat] using h

private noncomputable def inverseDifferenceQuotient (ζ μ : Measure ℝ) (t s : ℝ) : ℝ :=
  -(xHat μ s-xHat ζ s)/(affineHat ζ μ t s*xHat ζ s)

private lemma inverseDifferenceQuotient_bound (ζ μ : Measure ℝ)
    [IsProbabilityMeasure ζ] [IsProbabilityMeasure μ]
    {q t s : ℝ} (hζ : HasCutoff ζ q) (hμ : HasCutoff μ q)
    (ht : t ∈ Icc 0 1) (hs : s ∈ Ioc 0 q) :
    ‖inverseDifferenceQuotient ζ μ t s‖ ≤ ((1-q)^2)⁻¹ := by
  have hq : 0 < 1-q := sub_pos.mpr hζ.2.1
  have hx := xHat_ge_one_sub_cutoff ζ hζ hs.2
  have hy := xHat_ge_one_sub_cutoff μ hμ hs.2
  have hx1 : xHat ζ s ≤ 1 := (xHat_upper_bound ζ hζ s).trans (by linarith [hs.1])
  have hy1 : xHat μ s ≤ 1 := (xHat_upper_bound μ hμ s).trans (by linarith [hs.1])
  have hAlo : 1-q ≤ affineHat ζ μ t s := by
    have h := add_le_add (mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left hy ht.1)
    dsimp only [affineHat]
    nlinarith
  have hAp : 0 < affineHat ζ μ t s := hq.trans_le hAlo
  have hxp : 0 < xHat ζ s := hq.trans_le hx
  have hprod : (1-q)^2 ≤ affineHat ζ μ t s*xHat ζ s := by nlinarith
  have hdiff : |xHat μ s-xHat ζ s| ≤ 1 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  unfold inverseDifferenceQuotient
  rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (mul_pos hAp hxp)]
  rw [← one_div]
  apply (div_le_div_iff₀ (mul_pos hAp hxp) (sq_pos_of_pos hq)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hdiff (sq_nonneg (1-q))]

private lemma inverseDifferenceQuotient_tendsto (ζ μ : Measure ℝ)
    [IsProbabilityMeasure ζ] [IsProbabilityMeasure μ]
    {q s : ℝ} (hζ : HasCutoff ζ q) (_hμ : HasCutoff μ q) (hs : s ≤ q)
    (l : Filter ℝ) (hl : l ≤ 𝓝 0) :
    Tendsto (fun t => inverseDifferenceQuotient ζ μ t s) l
      (𝓝 (-(xHat μ s-xHat ζ s)/((xHat ζ s)^2))) := by
  have hx : 0 < xHat ζ s := xHat_pos ζ hζ (hs.trans_lt hζ.2.1)
  have hA : Continuous (fun t => affineHat ζ μ t s) := by
    unfold affineHat
    fun_prop
  have hA0 : Tendsto (fun t => affineHat ζ μ t s) (𝓝 (0:ℝ)) (𝓝 (xHat ζ s)) := by
    simpa [affineHat] using (hA.continuousAt (x := 0)).tendsto
  have hden : Tendsto (fun t => affineHat ζ μ t s*xHat ζ s)
      (𝓝 (0:ℝ)) (𝓝 ((xHat ζ s)^2)) := by
    simpa [pow_two] using hA0.mul
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => xHat ζ s) (𝓝 (0:ℝ)) (𝓝 (xHat ζ s)))
  have h : Tendsto (fun t => -(xHat μ s-xHat ζ s)/(affineHat ζ μ t s*xHat ζ s))
      (𝓝 (0:ℝ)) (𝓝 (-(xHat μ s-xHat ζ s)/((xHat ζ s)^2))) :=
    tendsto_const_nhds.div hden (pow_ne_zero 2 hx.ne')
  exact h.mono_left hl

private lemma inverse_integral_hasDerivWithinAt (ζ μ : Measure ℝ)
    [IsProbabilityMeasure ζ] [IsProbabilityMeasure μ]
    {q : ℝ} (hζ : HasCutoff ζ q) (hμ : HasCutoff μ q) :
    HasDerivWithinAt (fun t => ∫ s in (0:ℝ)..q, (affineHat ζ μ t s)⁻¹)
      (∫ s in (0:ℝ)..q, -(xHat μ s-xHat ζ s)/((xHat ζ s)^2)) (Icc 0 1) 0 := by
  let ν : Measure ℝ := volume.restrict (Ioc 0 q)
  let l : Filter ℝ := 𝓝[Icc 0 1 \ {0}] 0
  have hmeas : ∀ᶠ t in l, AEStronglyMeasurable (inverseDifferenceQuotient ζ μ t) ν := by
    apply Eventually.of_forall
    intro t
    unfold inverseDifferenceQuotient affineHat
    have hz := (xHat_continuous ζ hζ).measurable
    have hm := (xHat_continuous μ hμ).measurable
    exact ((hm.sub hz).neg.div
      (((hz.const_mul (1-t)).add (hm.const_mul t)).mul hz)).aestronglyMeasurable
  have hbound : ∀ᶠ t in l, ∀ᵐ s ∂ν,
      ‖inverseDifferenceQuotient ζ μ t s‖ ≤ ((1-q)^2)⁻¹ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact inverseDifferenceQuotient_bound ζ μ hζ hμ ht.1 hs
  have hlim : ∀ᵐ s ∂ν, Tendsto (fun t => inverseDifferenceQuotient ζ μ t s) l
      (𝓝 (-(xHat μ s-xHat ζ s)/((xHat ζ s)^2))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact inverseDifferenceQuotient_tendsto ζ μ hζ hμ hs.2 l nhdsWithin_le_nhds
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (μ := ν) (fun _ => ((1-q)^2)⁻¹) hmeas hbound (integrable_const _) hlim
  rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [intervalIntegral.integral_of_le hζ.1]
  apply hDCT.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := by simpa only [mem_singleton_iff] using ht.2
  have htint := affineHat_inverse_integrable ζ μ hζ hμ ht.1
  have h0int := affineHat_inverse_integrable ζ μ hζ hμ (t := 0) (by simp)
  rw [slope_def_field, sub_zero]
  symm
  calc
    ((∫ s, (affineHat ζ μ t s)⁻¹ ∂ν)-(∫ s, (affineHat ζ μ 0 s)⁻¹ ∂ν))/t =
        ∫ s, ((affineHat ζ μ t s)⁻¹-(affineHat ζ μ 0 s)⁻¹)/t ∂ν := by
      rw [integral_div, integral_sub htint h0int]
    _ = ∫ s, inverseDifferenceQuotient ζ μ t s ∂ν := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hx := (xHat_pos ζ hζ (hs.2.trans_lt hζ.2.1)).ne'
      have hA := (affineHat_pos ζ μ hζ hμ ht.1 hs.2).ne'
      simp only [affineHat, sub_zero, one_mul, zero_mul, add_zero]
      unfold inverseDifferenceQuotient affineHat
      unfold affineHat at hA
      field_simp [hx, ht0, hA]
      ring

private lemma xHat_div_square_intervalIntegrable (μ ζ : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ζ]
    {q : ℝ} (hμ : HasCutoff μ q) (hζ : HasCutoff ζ q) :
    IntervalIntegrable (fun s => xHat μ s/((xHat ζ s)^2)) volume 0 q := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hμ.1]
  apply (xHat_continuous μ hμ).continuousOn.div ((xHat_continuous ζ hζ).continuousOn.pow 2)
  intro s hs
  exact pow_ne_zero 2 (xHat_pos ζ hζ (hs.2.trans_lt hζ.2.1)).ne'

/-- The derivative at zero of the actual mixture functional, with its
first-variation expression derived by dominated convergence and Fubini. -/
theorem functional_mixture_hasDerivWithinAt (β : ℝ) (η : ℝ → ℝ)
    (ζ μ : Measure ℝ) [IsProbabilityMeasure ζ] [IsProbabilityMeasure μ]
    {q : ℝ} (hζ : HasCutoff ζ q) (hμ : HasCutoff μ q)
    (hη : ContinuousOn η (Icc 0 q)) :
    HasDerivWithinAt (fun t => functional β η (mixture ζ μ t) q)
      (((∫ s, firstVariation β η ζ s ∂ζ)-(∫ s, firstVariation β η ζ s ∂μ))/2)
      (Icc 0 1) 0 := by
  let A : ℝ := ∫ s, η s ∂ζ
  let B : ℝ := ∫ s, η s ∂μ
  let g : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..q, (affineHat ζ μ t s)⁻¹
  let D : ℝ := ∫ s in (0:ℝ)..q, -(xHat μ s-xHat ζ s)/((xHat ζ s)^2)
  have hlinraw : HasDerivAt (fun t => (1-t)*A+t*B) ((0-1)*A+1*B) 0 :=
    (((hasDerivAt_const (0:ℝ) 1).sub (hasDerivAt_id 0)).mul_const A).add
      ((hasDerivAt_id 0).mul_const B)
  have hlin : HasDerivAt (fun t => (1-t)*A+t*B) (B-A) 0 := by
    convert hlinraw using 1
    ring
  have henergyraw : HasDerivAt (fun t => β^2*(η 1-((1-t)*A+t*B))) (β^2*(0-(B-A))) 0 :=
    ((hasDerivAt_const (0:ℝ) (η 1)).sub hlin).const_mul (β^2)
  have henergy : HasDerivAt (fun t => β^2*(η 1-((1-t)*A+t*B))) (β^2*(A-B)) 0 := by
    convert henergyraw using 1
    ring
  have hg : HasDerivWithinAt g D (Icc 0 1) 0 :=
    inverse_integral_hasDerivWithinAt ζ μ hζ hμ
  have hpath := ((henergy.hasDerivWithinAt.add hg).add_const (Real.log (1-q))).div_const 2
  have hD : D = (∫ s in (0:ℝ)..q, xHat ζ s/((xHat ζ s)^2))-
      (∫ s in (0:ℝ)..q, xHat μ s/((xHat ζ s)^2)) := by
    calc
      D = ∫ s in (0:ℝ)..q, xHat ζ s/((xHat ζ s)^2)-xHat μ s/((xHat ζ s)^2) := by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp only
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        ring
      _ = _ := intervalIntegral.integral_sub
        (xHat_div_square_intervalIntegrable ζ ζ hζ hζ)
        (xHat_div_square_intervalIntegrable μ ζ hμ hζ)
  have hfζ := firstVariation_integral_identity β η ζ ζ hζ hζ hη
  have hfμ := firstVariation_integral_identity β η μ ζ hμ hζ hη
  have hder : (β^2*(A-B)+D)/2 =
      ((∫ s, firstVariation β η ζ s ∂ζ)-(∫ s, firstVariation β η ζ s ∂μ))/2 := by
    dsimp only [A, B]
    rw [hD]
    nlinarith
  rw [hder] at hpath
  apply hpath.congr_of_mem _ (by simp)
  intro t ht
  have hηζ := integrable_cutoff ζ hζ hη
  have hημ := integrable_cutoff μ hμ hη
  unfold functional
  rw [integral_mixture ζ μ hηζ hημ ht]
  simp only [xHat_mixture ζ μ hζ hμ ht, affineHat, A, B, g, Pi.add_apply]

/-- A minimum along the genuine mixture segment forces the first
variation to have nonpositive average displacement. -/
theorem firstVariation_integral_le_of_segment_minimum (β : ℝ) (η : ℝ → ℝ)
    (ζ μ : Measure ℝ) [IsProbabilityMeasure ζ] [IsProbabilityMeasure μ]
    {q : ℝ} (hζ : HasCutoff ζ q) (hμ : HasCutoff μ q)
    (hη : ContinuousOn η (Icc 0 q))
    (hmin : ∀ t ∈ Icc 0 1, functional β η ζ q ≤ functional β η (mixture ζ μ t) q) :
    (∫ s, firstVariation β η ζ s ∂μ) ≤ ∫ s, firstVariation β η ζ s ∂ζ := by
  have hder := functional_mixture_hasDerivWithinAt β η ζ μ hζ hμ hη
  have hlocal : IsLocalMinOn (fun t => functional β η (mixture ζ μ t) q) (Icc 0 1) 0 := by
    apply IsMinOn.isLocalMinOn
    intro t ht
    simpa using hmin t ht
  have hcone : (1:ℝ) ∈ posTangentConeAt (Icc (0:ℝ) 1) 0 := by
    have h := sub_mem_posTangentConeAt_of_segment_subset
      (x := (0:ℝ)) (y := (1:ℝ)) (by rw [segment_eq_Icc (by norm_num)])
    simpa using h
  have hn := hlocal.hasFDerivWithinAt_nonneg hder.hasFDerivWithinAt hcone
  simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at hn
  linarith

/-- The variational necessity inequality for arbitrary admissible
competitor cutoffs, derived from the actual mixture derivative. -/
theorem firstVariation_integral_le_of_minimizer (β : ℝ) (η : ℝ → ℝ)
    (ζ μ : Measure ℝ) [IsProbabilityMeasure ζ] [IsProbabilityMeasure μ]
    {qζ qμ : ℝ} (hζ : HasCutoff ζ qζ) (hμ : HasCutoff μ qμ)
    (hη : ContinuousOn η (Ico 0 1))
    (hmin : ∀ ν : Measure ℝ, ∀ (_ : IsProbabilityMeasure ν), ∀ r : ℝ,
      HasCutoff ν r → functional β η ζ qζ ≤ functional β η ν r) :
    (∫ s, firstVariation β η ζ s ∂μ) ≤ ∫ s, firstVariation β η ζ s ∂ζ := by
  let q := max qζ qμ
  have hq1 : q < 1 := max_lt hζ.2.1 hμ.2.1
  have hζq : HasCutoff ζ q := hζ.mono (le_max_left _ _) hq1
  have hμq : HasCutoff μ q := hμ.mono (le_max_right _ _) hq1
  have hηq : ContinuousOn η (Icc 0 q) :=
    hη.mono (fun s hs => ⟨hs.1, hs.2.trans_lt hq1⟩)
  apply firstVariation_integral_le_of_segment_minimum β η ζ μ hζq hμq hηq
  intro t ht
  have h := hmin (mixture ζ μ t) (mixture_isProbability ζ μ ht) q
    (mixture_cutoff ζ μ hζq hμq)
  rwa [functional_cutoff_independent ζ β η hζ hζq] at h

/-- Every point below one is an admissible Dirac competitor. -/
theorem dirac_hasCutoff {r : ℝ} (hr : r ∈ Ico 0 1) : HasCutoff (Measure.dirac r) r := by
  refine ⟨hr.1, hr.2, ?_⟩
  simpa using hr.1

/-- Dirac competitors turn variational necessity into a pointwise global
upper bound for the genuine first-variation potential. -/
theorem firstVariation_le_integral_of_minimizer (β : ℝ) (η : ℝ → ℝ)
    (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {qζ : ℝ} (hζ : HasCutoff ζ qζ) (hη : ContinuousOn η (Ico 0 1))
    (hmin : ∀ ν : Measure ℝ, ∀ (_ : IsProbabilityMeasure ν), ∀ r : ℝ,
      HasCutoff ν r → functional β η ζ qζ ≤ functional β η ν r) :
    ∀ r ∈ Ico 0 1, firstVariation β η ζ r ≤ ∫ s, firstVariation β η ζ s ∂ζ := by
  intro r hr
  have h := firstVariation_integral_le_of_minimizer β η ζ (Measure.dirac r)
    hζ (dirac_hasCutoff hr) hη hmin
  simpa using h

/-- A genuine minimizer is supported almost everywhere on the global
maximum of its first variation. The maximizing value is its own average. -/
theorem firstVariation_support_of_minimizer (β : ℝ) (η : ℝ → ℝ)
    (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {qζ : ℝ} (hζ : HasCutoff ζ qζ) (hη : ContinuousOn η (Ico 0 1))
    (hmin : ∀ ν : Measure ℝ, ∀ (_ : IsProbabilityMeasure ν), ∀ r : ℝ,
      HasCutoff ν r → functional β η ζ qζ ≤ functional β η ν r) :
    ∀ᵐ r ∂ζ, firstVariation β η ζ r = ∫ s, firstVariation β η ζ s ∂ζ := by
  let m : ℝ := ∫ s, firstVariation β η ζ s ∂ζ
  have hηq : ContinuousOn η (Icc 0 qζ) :=
    hη.mono (fun s hs => ⟨hs.1, hs.2.trans_lt hζ.2.1⟩)
  have hi := firstVariation_integrable β η ζ ζ hζ hζ hηq
  have hpoint := firstVariation_le_integral_of_minimizer β η ζ hζ hη hmin
  have hnonneg : 0 ≤ᵐ[ζ] fun r => m-firstVariation β η ζ r := by
    filter_upwards [hζ.2.2] with r hr
    exact sub_nonneg.mpr (hpoint r ⟨hr.1, hr.2.trans_lt hζ.2.1⟩)
  have hint : (∫ r, m-firstVariation β η ζ r ∂ζ) = 0 := by
    rw [integral_sub (integrable_const m) hi]
    simp [m]
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg
    ((integrable_const m).sub hi)).mp hint
  filter_upwards [hae] with r hr
  change m-firstVariation β η ζ r=0 at hr
  linarith

/-- The full necessary-and-sufficient support criterion in the canonical
admissible class. Its necessity comes from proved mixture derivatives;
its sufficiency comes from the proved supporting inequality. -/
theorem Admissible.minimizer_iff_support_on_maximum (ζ : Admissible)
    (β : ℝ) (η : ℝ → ℝ) (hη : ContinuousOn η (Ico 0 1)) :
    ζ.IsMinimizer β η ↔ ∃ m : ℝ,
      (∀ s ∈ Ico (0:ℝ) 1, firstVariation β η ζ.law s ≤ m) ∧
      (∀ᵐ s ∂ζ.law, firstVariation β η ζ.law s = m) := by
  constructor
  · intro hmin
    have hraw : ∀ ν : Measure ℝ, ∀ (_ : IsProbabilityMeasure ν), ∀ r : ℝ,
        HasCutoff ν r → functional β η ζ.law ζ.cutoff ≤ functional β η ν r := by
      intro ν hν r hr
      let νA : Admissible := ⟨ν, hν, ⟨r, hr⟩⟩
      have h := hmin νA
      rw [ζ.value_eq β η ζ.hasCutoff, νA.value_eq β η hr] at h
      exact h
    refine ⟨∫ s, firstVariation β η ζ.law s ∂ζ.law, ?_, ?_⟩
    · exact firstVariation_le_integral_of_minimizer β η ζ.law ζ.hasCutoff hη hraw
    · exact firstVariation_support_of_minimizer β η ζ.law ζ.hasCutoff hη hraw
  · rintro ⟨m, hmax, hsupport⟩
    exact ζ.minimizer_of_support_on_maximum β η hη m hmax hsupport

end SlowEquilibration.CrisantiSommers

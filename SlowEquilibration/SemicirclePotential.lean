-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.JacobiLogLimit
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-!
# The actual semicircle density and outside-edge logarithmic potential

The density is the literal `sqrt(4-t^2)/(2*pi)`. Its normalization follows the
ordinary Gaussian/semicircle integration in the pinned OpenAI source
`OAI/Probability/SKGap/Localization/SemicircleDensity.lean` (Apache-2.0,
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb). All subsequent identities use actual
Lebesgue integrals, derivatives and integration by parts.
-/

namespace SlowEquilibration.SemicirclePotential

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Filter
open OAI.CriticalSK GOELogPotential JacobiLogLimit
open scoped Topology ENNReal NNReal Interval

def density (t : ℝ) : ℝ := Real.sqrt (4 - t ^ 2) / (2 * Real.pi)

def law : Measure ℝ := volume.withDensity (fun t => ENNReal.ofReal (density t))

lemma density_continuous : Continuous density := by unfold density; fun_prop

lemma density_nonneg (t : ℝ) : 0 ≤ density t := div_nonneg (Real.sqrt_nonneg _) (by positivity)

lemma density_eq_zero_outside {t : ℝ} (ht : t ∉ Icc (-2 : ℝ) 2) : density t = 0 := by
  have hn : 4 - t ^ 2 ≤ 0 := by
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht <;> nlinarith [sq_nonneg (t + 2), sq_nonneg (t - 2)]
  simp only [density, Real.sqrt_eq_zero_of_nonpos hn, zero_div]

lemma density_integrable : Integrable density volume := by
  apply density_continuous.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro t ht
  by_contra hh
  exact ht (density_eq_zero_outside hh)

lemma integral_density : (∫ t, density t) = 1 := by
  have he (u : ℝ) : Real.sqrt (4 - (2 * u) ^ 2) = 2 * Real.sqrt (1 - u ^ 2) := by
    rw [show 4 - (2 * u) ^ 2 = (2 : ℝ) ^ 2 * (1 - u ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg (2 : ℝ))]
    norm_num
  have hh := intervalIntegral.smul_integral_comp_mul_left
    (a := (-1 : ℝ)) (b := (1 : ℝ)) (fun u : ℝ => Real.sqrt (4 - u ^ 2)) (2 : ℝ)
  simp only [he, intervalIntegral.integral_const_mul, smul_eq_mul,
    integral_sqrt_one_sub_sq] at hh
  norm_num only [mul_neg, mul_one] at hh
  have hi : (∫ t in (-2 : ℝ)..2, density t) = 1 := by
    unfold density
    rw [intervalIntegral.integral_div, ← hh]
    field_simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => density_eq_zero_outside ht)]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
  exact hi

instance law_probability : IsProbabilityMeasure law where
  measure_univ := by
    rw [law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal density_integrable (ae_of_all _ density_nonneg), integral_density]
    norm_num

lemma law_supported : law (Icc (-2 : ℝ) 2)ᶜ = 0 := by
  rw [law]
  rw [withDensity_apply (fun t => ENNReal.ofReal (density t))
    (show MeasurableSet (Icc (-2 : ℝ) 2)ᶜ by exact measurableSet_Icc.compl)]
  apply setLIntegral_eq_zero measurableSet_Icc.compl
  intro t ht
  change ENNReal.ofReal (density t) = 0
  rw [density_eq_zero_outside ht]
  simp

lemma integral_law (f : ℝ → ℝ) : (∫ t, f t ∂law) = ∫ t, density t * f t := by
  rw [law, integral_withDensity_eq_integral_toReal_smul
    density_continuous.measurable.ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (density_nonneg _), smul_eq_mul]

lemma integral_law_interval (f : ℝ → ℝ) :
    (∫ t, f t ∂law) = ∫ t in (-2 : ℝ)..2, density t * f t := by
  rw [integral_law]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun t ht => by rw [density_eq_zero_outside ht, zero_mul])]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2)]

lemma density_integral_interval : (∫ t in (-2 : ℝ)..2, density t) = 1 := by
  rw [intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2), ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => density_eq_zero_outside ht), integral_density]

def resolvent (z : ℝ) : ℝ := ∫ t in (-2 : ℝ)..2, density t / (z - t)

def resolventSquare (z : ℝ) : ℝ := ∫ t in (-2 : ℝ)..2, density t / (z - t) ^ 2

def potential (z : ℝ) : ℝ := ∫ t, Real.log |z - t| ∂law

lemma resolvent_integrable {z : ℝ} (hz : 2 < z) :
    Integrable (fun t => density t / (z - t)) (volume.restrict (Icc (-2 : ℝ) 2)) := by
  apply ContinuousOn.integrableOn_Icc
  apply density_continuous.continuousOn.div (continuousOn_const.sub continuousOn_id)
  intro t ht
  exact (sub_pos.mpr (ht.2.trans_lt hz)).ne'

lemma resolventSquare_integrable {z : ℝ} (hz : 2 < z) :
    Integrable (fun t => density t / (z - t) ^ 2) (volume.restrict (Icc (-2 : ℝ) 2)) := by
  apply ContinuousOn.integrableOn_Icc
  apply density_continuous.continuousOn.div ((continuousOn_const.sub continuousOn_id).pow 2)
  intro t ht
  exact pow_ne_zero 2 (sub_pos.mpr (ht.2.trans_lt hz)).ne'

lemma potential_integrable {z : ℝ} (hz : 2 < z) :
    Integrable (fun t => density t * Real.log (z - t)) (volume.restrict (Icc (-2 : ℝ) 2)) := by
  apply ContinuousOn.integrableOn_Icc
  apply density_continuous.continuousOn.mul
  apply (continuousOn_const.sub continuousOn_id).log
  intro t ht
  exact (sub_pos.mpr (ht.2.trans_lt hz)).ne'

lemma potential_eq_interval (z : ℝ) :
    potential z = ∫ t in (-2 : ℝ)..2, density t * Real.log (z - t) := by
  rw [potential, integral_law_interval]
  simp only [Real.log_abs]

lemma resolvent_hasDerivAt {z : ℝ} (hz : 2 < z) : HasDerivAt resolvent (-resolventSquare z) z := by
  let μ := volume.restrict (Icc (-2 : ℝ) 2)
  let d := (z - 2) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hs : Ioi (2 + d) ∈ 𝓝 z := Ioi_mem_nhds (by dsimp [d]; linarith)
  have hm : ∀ u : ℝ, AEStronglyMeasurable (fun t => density t / (u - t)) μ := fun u => ((density_continuous.measurable.div (measurable_const.sub measurable_id)).aestronglyMeasurable)
  have hm' : AEStronglyMeasurable (fun t => -density t / (z - t) ^ 2) μ :=
    (density_continuous.measurable.neg.div ((measurable_const.sub measurable_id).pow_const 2)).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂μ, ∀ u ∈ Ioi (2 + d), ‖-density t / (u - t) ^ 2‖ ≤ density t / d ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht u hu
    change 2 + d < u at hu
    have hgap : d ≤ u - t := by linarith [ht.2]
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg (density_nonneg _), abs_of_nonneg (sq_nonneg _)]
    exact div_le_div_of_nonneg_left (density_nonneg _) (sq_pos_of_pos hd)
      (by nlinarith [sq_nonneg (u - t - d)])
  have hdiff : ∀ᵐ t ∂μ, ∀ u ∈ Ioi (2 + d),
      HasDerivAt (fun u => density t / (u - t)) (-density t / (u - t) ^ 2) u := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht u hu
    change 2 + d < u at hu
    have hgap : 0 < u - t := by linarith [ht.2]
    convert (hasDerivAt_const u (density t)).div ((hasDerivAt_id u).sub_const t) hgap.ne' using 1
    · funext v; rfl
    · simp only [zero_mul, mul_one, zero_sub, id_eq]
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun u t => density t / (u - t)) (F' := fun u t => -density t / (u - t) ^ 2)
    (bound := fun t => density t / d ^ 2) hs (.of_forall hm) (resolvent_integrable hz) hm'
    hbound (density_continuous.continuousOn.integrableOn_Icc.div_const _) hdiff
  have hres : (fun u => ∫ t, density t / (u - t) ∂μ) = resolvent := by
    funext u
    rw [resolvent, intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2), integral_Icc_eq_integral_Ioc]
  rw [hres] at hi
  convert hi.2 using 1
  rw [resolventSquare, intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2), integral_Icc_eq_integral_Ioc,
    ← integral_neg]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by
    change -(density t / (z - t) ^ 2) = -density t / (z - t) ^ 2
    rw [neg_div])

lemma potential_hasDerivAt {z : ℝ} (hz : 2 < z) : HasDerivAt potential (resolvent z) z := by
  let μ := volume.restrict (Icc (-2 : ℝ) 2)
  let d := (z - 2) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hs : Ioi (2 + d) ∈ 𝓝 z := Ioi_mem_nhds (by dsimp [d]; linarith)
  have hm : ∀ u : ℝ, AEStronglyMeasurable (fun t => density t * Real.log (u - t)) μ := fun u =>
    (density_continuous.measurable.mul (measurable_const.sub measurable_id).log).aestronglyMeasurable
  have hm' : AEStronglyMeasurable (fun t => density t / (z - t)) μ :=
    (density_continuous.measurable.div (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂μ, ∀ u ∈ Ioi (2 + d), ‖density t / (u - t)‖ ≤ density t / d := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht u hu
    change 2 + d < u at hu
    have hgap : d ≤ u - t := by linarith [ht.2]
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (density_nonneg _), abs_of_pos (hd.trans_le hgap)]
    exact div_le_div_of_nonneg_left (density_nonneg _) hd hgap
  have hdiff : ∀ᵐ t ∂μ, ∀ u ∈ Ioi (2 + d),
      HasDerivAt (fun u => density t * Real.log (u - t)) (density t / (u - t)) u := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht u hu
    change 2 + d < u at hu
    have hgap : 0 < u - t := by linarith [ht.2]
    simpa only [id_eq, one_div, div_eq_mul_inv, one_mul, mul_one] using
      (((hasDerivAt_id u).sub_const t).log hgap.ne').const_mul (density t)
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun u t => density t * Real.log (u - t)) (F' := fun u t => density t / (u - t))
    (bound := fun t => density t / d) hs (.of_forall hm) (potential_integrable hz) hm'
    hbound (density_continuous.continuousOn.integrableOn_Icc.div_const _) hdiff
  have hfun : (fun u => ∫ t, density t * Real.log (u - t) ∂μ) = potential := by
    funext u
    rw [potential_eq_interval, intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2), integral_Icc_eq_integral_Ioc]
  rw [hfun] at hi
  convert hi.2 using 1
  rw [resolvent, intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2), integral_Icc_eq_integral_Ioc]

lemma resolvent_nonneg {z : ℝ} (hz : 2 < z) : 0 ≤ resolvent z := by
  unfold resolvent
  apply intervalIntegral.integral_nonneg (by norm_num : (-2 : ℝ) ≤ 2)
  intro t ht
  exact div_nonneg (density_nonneg _) (sub_pos.mpr (ht.2.trans_lt hz)).le

lemma resolvent_le_inv_gap {z : ℝ} (hz : 2 < z) : resolvent z ≤ 1 / (z - 2) := by
  have hi := resolvent_integrable hz
  have hi' : IntervalIntegrable (fun t => density t / (z - t)) volume (-2 : ℝ) 2 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-2 : ℝ) ≤ 2)).mpr hi
  have hconst : IntervalIntegrable (fun t => density t / (z - 2)) volume (-2 : ℝ) 2 :=
    density_continuous.intervalIntegrable (-2 : ℝ) 2 |>.div_const _
  unfold resolvent
  calc
    _ ≤ ∫ t in (-2 : ℝ)..2, density t / (z - 2) := by
      apply intervalIntegral.integral_mono_on (by norm_num : (-2 : ℝ) ≤ 2) hi' hconst
      intro t ht
      exact div_le_div_of_nonneg_left (density_nonneg _) (by linarith : 0 < z - 2) (by linarith [ht.2])
    _ = _ := by rw [intervalIntegral.integral_div, density_integral_interval]

lemma resolvent_tendsto_zero : Tendsto resolvent atTop (𝓝 0) := by
  have hbound : ∀ᶠ z : ℝ in atTop, 0 ≤ resolvent z ∧ resolvent z ≤ 1 / (z - 2) := by
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with z hz
    exact ⟨resolvent_nonneg (by linarith), resolvent_le_inv_gap (by linarith)⟩
  apply squeeze_zero' (hbound.mono fun _ h => h.1) (hbound.mono fun _ h => h.2)
  have hz : Tendsto (fun z : ℝ => z - 2) atTop atTop := by
    simpa only [id_eq, sub_eq_add_neg] using tendsto_id.atTop_add (tendsto_const_nhds (x := (-2 : ℝ)))
  exact hz.const_div_atTop 1

/-- Integration by parts for the literal density gives its resolvent equation. -/
lemma resolvent_integration_by_parts {z : ℝ} (hz : 2 < z) :
    (4 - z ^ 2) * resolventSquare z - z * resolvent z + 2 = 0 := by
  let f : ℝ → ℝ := fun t => density t * (4 - t ^ 2) / (z - t)
  let g : ℝ → ℝ := fun t => density t *
    ((4 - z ^ 2) / (z - t) ^ 2 - z / (z - t) + 2)
  have hc : ContinuousOn f (Icc (-2 : ℝ) 2) := by
    apply (density_continuous.continuousOn.mul (continuousOn_const.sub (continuousOn_id.pow 2))).div
      (continuousOn_const.sub continuousOn_id)
    intro t ht
    exact (sub_pos.mpr (ht.2.trans_lt hz)).ne'
  have hg : ContinuousOn g (Icc (-2 : ℝ) 2) := by
    apply density_continuous.continuousOn.mul
    apply ContinuousOn.add _ continuousOn_const
    apply ContinuousOn.sub
    · apply continuousOn_const.div ((continuousOn_const.sub continuousOn_id).pow 2)
      intro t ht
      exact pow_ne_zero 2 (sub_pos.mpr (ht.2.trans_lt hz)).ne'
    · apply continuousOn_const.div (continuousOn_const.sub continuousOn_id)
      intro t ht
      exact (sub_pos.mpr (ht.2.trans_lt hz)).ne'
  have hd : ∀ t ∈ Ioo (-2 : ℝ) 2, HasDerivAt f (g t) t := by
    intro t ht
    have hD : 0 < 4 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have hr : Real.sqrt (4 - t ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hD).ne'
    have hgap : z - t ≠ 0 := (sub_pos.mpr (ht.2.trans hz)).ne'
    have hderD := (hasDerivAt_const t (4 : ℝ)).sub ((hasDerivAt_id t).pow 2)
    have hder := (((hderD.sqrt hD.ne').div_const (2 * Real.pi)).mul hderD).div
      ((hasDerivAt_const t z).sub (hasDerivAt_id t)) hgap
    convert hder using 1
    · funext u; rfl
    · dsimp [g, density]
      simp only [pow_one, mul_one, zero_sub]
      have hsq := Real.sq_sqrt hD.le
      field_simp
      nlinarith [hsq]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (-2 : ℝ) ≤ 2) hc hd (hg.intervalIntegrable_of_Icc (by norm_num))
  have hf2 : f 2 = 0 := by dsimp [f]; norm_num [density]
  have hfm2 : f (-2) = 0 := by dsimp [f]; norm_num [density]
  rw [hf2, hfm2, sub_self] at hi
  have hI1 : IntervalIntegrable (fun t => density t / (z - t) ^ 2) volume (-2 : ℝ) 2 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-2 : ℝ) ≤ 2)).mpr
      (resolventSquare_integrable hz)
  have hI2 : IntervalIntegrable (fun t => density t / (z - t)) volume (-2 : ℝ) 2 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-2 : ℝ) ≤ 2)).mpr
      (resolvent_integrable hz)
  have heq : g = fun t => (4 - z ^ 2) * (density t / (z - t) ^ 2) -
      z * (density t / (z - t)) + 2 * density t := by
    funext t; dsimp [g]; ring
  rw [heq, intervalIntegral.integral_add ((hI1.const_mul _).sub (hI2.const_mul _))
    (density_continuous.intervalIntegrable _ _ |>.const_mul _),
    intervalIntegral.integral_sub (hI1.const_mul _) (hI2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, density_integral_interval, mul_one] at hi
  exact hi

lemma resolvent_ode {z : ℝ} (hz : 2 < z) :
    (z ^ 2 - 4) * deriv resolvent z - z * resolvent z + 2 = 0 := by
  rw [(resolvent_hasDerivAt hz).deriv]
  have h := resolvent_integration_by_parts hz
  nlinarith

lemma zero_of_derivative_zero_and_limit {f : ℝ → ℝ}
    (hder : ∀ z : ℝ, 2 < z → HasDerivAt f 0 z)
    (hlim : Tendsto f atTop (𝓝 0)) {z : ℝ} (hz : 2 < z) : f z = 0 := by
  obtain ⟨c, hc⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero
    (convex_Ioi (2 : ℝ)).isPreconnected
    (fun u hu => (hder u hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (hder u hu).deriv)
  have hconst : Tendsto f atTop (𝓝 c) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with u hu
    exact (hc u hu).symm
  exact (hc z hz).trans (tendsto_nhds_unique hconst hlim)

def resolventDifferenceRatio (z : ℝ) : ℝ :=
  (resolvent z - semicircleResolvent (z - 2)) / Real.sqrt (z ^ 2 - 4)

lemma resolventDifferenceRatio_hasDerivAt {z : ℝ} (hz : 2 < z) :
    HasDerivAt resolventDifferenceRatio 0 z := by
  have hdisc : 0 < z ^ 2 - 4 := by nlinarith
  have hs : 0 < z - 2 := by linarith
  have hroot := Real.sqrt_pos.mpr hdisc
  have hsq := Real.sq_sqrt hdisc.le
  have hpoly : (z - 2) * (4 + (z - 2)) = z ^ 2 - 4 := by ring
  have hdR := (semicircleResolvent_hasDerivAt hs).comp z ((hasDerivAt_id z).sub_const 2)
  simp only [mul_one] at hdR
  rw [hpoly] at hdR
  have hrootD := (((hasDerivAt_id z).pow 2).sub_const 4).sqrt hdisc.ne'
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at hrootD
  have hd := ((resolvent_hasDerivAt hz).sub hdR).div hrootD hroot.ne'
  simp only [id_eq, Pi.pow_apply, Function.comp_apply, Pi.sub_apply] at hd
  change HasDerivAt resolventDifferenceRatio _ z at hd
  convert hd using 1
  have hode := resolvent_integration_by_parts hz
  have hq := resolvent_quadratic hs
  have hp := resolvent_root_product hs
  rw [hpoly] at hp
  have hRdef : 2 * semicircleResolvent (z - 2) = z - Real.sqrt (z ^ 2 - 4) := by
    unfold semicircleResolvent
    rw [hpoly]
    ring
  have hpair : semicircleResolvent (z - 2) * (Real.sqrt (z ^ 2 - 4) + z) = 2 := by
    nlinarith [hq, hp]
  have hnum : (-resolventSquare z * Real.sqrt (z ^ 2 - 4) + semicircleResolvent (z - 2)) *
      Real.sqrt (z ^ 2 - 4) - (resolvent z - semicircleResolvent (z - 2)) * z = 0 := by
    calc
      _ = -resolventSquare z * (z ^ 2 - 4) - z * resolvent z +
          semicircleResolvent (z - 2) * (Real.sqrt (z ^ 2 - 4) + z) := by
        calc
          _ = -resolventSquare z * Real.sqrt (z ^ 2 - 4) ^ 2 - z * resolvent z +
              semicircleResolvent (z - 2) * (Real.sqrt (z ^ 2 - 4) + z) := by ring
          _ = _ := by rw [hsq]
      _ = 0 := by nlinarith [hode, hpair]
  field_simp
  nlinarith [hnum]

lemma resolventDifferenceRatio_tendsto_zero :
    Tendsto resolventDifferenceRatio atTop (𝓝 0) := by
  have hshift : Tendsto (fun z : ℝ => z - 2) atTop atTop := by
    simpa only [id_eq, sub_eq_add_neg] using tendsto_id.atTop_add
      (tendsto_const_nhds (x := (-2 : ℝ)))
  have hdiff := resolvent_tendsto_zero.sub (JacobiLogLimit.resolvent_tendsto_zero.comp hshift)
  have habs := hdiff.abs
  simp only [sub_zero, abs_zero] at habs
  have hbound : ∀ᶠ z : ℝ in atTop,
      0 ≤ |resolventDifferenceRatio z| ∧
      |resolventDifferenceRatio z| ≤ |resolvent z - semicircleResolvent (z - 2)| := by
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with z hz
    have hroot : 1 ≤ Real.sqrt (z ^ 2 - 4) := by
      apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by nlinarith : 0 ≤ z ^ 2 - 4)).mpr
      nlinarith
    refine ⟨abs_nonneg _, ?_⟩
    rw [resolventDifferenceRatio, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_self (abs_nonneg _) hroot
  have ht := squeeze_zero' (hbound.mono fun _ h => h.1) (hbound.mono fun _ h => h.2) habs
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using ht)

/-- The actual semicircle-density resolvent is its derived quadratic root.
This closes the density identification without postulating its transform. -/
theorem resolvent_eq_semicircleResolvent {z : ℝ} (hz : 2 < z) :
    resolvent z = semicircleResolvent (z - 2) := by
  have heq := zero_of_derivative_zero_and_limit
    (fun u hu => resolventDifferenceRatio_hasDerivAt hu)
    resolventDifferenceRatio_tendsto_zero hz
  unfold resolventDifferenceRatio at heq
  have hroot : Real.sqrt (z ^ 2 - 4) ≠ 0 :=
    (Real.sqrt_pos.mpr (by nlinarith : 0 < z ^ 2 - 4)).ne'
  exact sub_eq_zero.mp ((div_eq_zero_iff).mp heq |>.resolve_right hroot)

/-- The density-integral potential has its ordinary logarithmic normalization
at infinity, with an explicit integrable majorant. -/
lemma potential_log_anchor_bound {z : ℝ} (hz : 2 < z) :
    |potential z - Real.log z| ≤ 2 / (z - 2) := by
  have hg : 0 < z - 2 := by linarith
  have hI : IntervalIntegrable (fun t => density t * Real.log (z - t)) volume (-2 : ℝ) 2 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-2 : ℝ) ≤ 2)).mpr
      (potential_integrable hz)
  have hIconst : IntervalIntegrable (fun t => density t * Real.log z) volume (-2 : ℝ) 2 :=
    density_continuous.intervalIntegrable _ _ |>.mul_const _
  have heq : potential z - Real.log z =
      ∫ t in (-2 : ℝ)..2, density t * (Real.log (z - t) - Real.log z) := by
    rw [potential_eq_interval]
    have hc : Real.log z = ∫ t in (-2 : ℝ)..2, density t * Real.log z := by
      rw [intervalIntegral.integral_mul_const, density_integral_interval, one_mul]
    conv_lhs => rw [hc]
    rw [← intervalIntegral.integral_sub hI hIconst]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  rw [heq, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ t in (-2 : ℝ)..2, density t * (2 / (z - 2)) := by
      apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (-2 : ℝ) ≤ 2)
        (ae_of_all _ _) (density_continuous.intervalIntegrable _ _ |>.mul_const _)
      intro t ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (density_nonneg _)]
      have hlog := SpectralTraceLipschitz.log_difference_le hg
        (by linarith [ht.2] : z - 2 ≤ z - t) (by linarith : z - 2 ≤ z)
      apply mul_le_mul_of_nonneg_left _ (density_nonneg _)
      apply hlog.trans
      apply div_le_div_of_nonneg_right _ hg.le
      rw [show z - t - z = -t by ring, abs_neg]
      exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    _ = _ := by rw [intervalIntegral.integral_mul_const, density_integral_interval, one_mul]

lemma potential_minus_log_tendsto :
    Tendsto (fun z : ℝ => potential z - Real.log z) atTop (𝓝 0) := by
  have hshift : Tendsto (fun z : ℝ => z - 2) atTop atTop := by
    simpa only [id_eq, sub_eq_add_neg] using tendsto_id.atTop_add
      (tendsto_const_nhds (x := (-2 : ℝ)))
  have hbound : ∀ᶠ z : ℝ in atTop,
      0 ≤ |potential z - Real.log z| ∧ |potential z - Real.log z| ≤ 2 / (z - 2) := by
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with z hz
    exact ⟨abs_nonneg _, potential_log_anchor_bound (by linarith)⟩
  have ht := squeeze_zero' (hbound.mono fun _ h => h.1) (hbound.mono fun _ h => h.2)
    (hshift.const_div_atTop 2)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using ht)

/-- The manuscript's literal semicircle-density logarithmic potential equals
its actual explicit outside-edge primitive. -/
theorem potential_eq_outsideSpectralPotential {z : ℝ} (hz : 2 < z) :
    potential z = outsideSpectralPotential (z - 2) := by
  let f : ℝ → ℝ := fun z => potential z - outsideSpectralPotential (z - 2)
  have hder : ∀ z : ℝ, 2 < z → HasDerivAt f 0 z := by
    intro z hz
    have hd := (outsideSpectralPotential_hasDerivAt (by linarith : 0 < z - 2)).comp z
      ((hasDerivAt_id z).sub_const 2)
    simp only [mul_one] at hd
    have he := (potential_hasDerivAt hz).sub hd
    rw [resolvent_eq_semicircleResolvent hz, sub_self] at he
    exact he
  have hshift : Tendsto (fun z : ℝ => z - 2) atTop atTop := by
    simpa only [id_eq, sub_eq_add_neg] using tendsto_id.atTop_add
      (tendsto_const_nhds (x := (-2 : ℝ)))
  have hlim := potential_minus_log_tendsto.sub
    (outsideSpectralPotential_minus_log_tendsto.comp hshift)
  have hf : Tendsto f atTop (𝓝 0) := by
    convert hlim using 1
    · funext z
      dsimp [f, Function.comp_def]
      rw [show 2 + (z - 2) = z by ring]
      ring
    · simp
  exact sub_eq_zero.mp (zero_of_derivative_zero_and_limit hder hf hz)

/-- The logarithm of the expectation of the ordinary absolute determinant,
divided by its actual GOE dimension, converges to the manuscript's literal Ω.
No expected spectral measure or potential identity is assumed. -/
theorem log_expected_absolute_det_tendsto_potential {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => logMeanAbsoluteDet n s) atTop (𝓝 (potential (2 + s))) := by
  rw [potential_eq_outsideSpectralPotential (by linarith : 2 < 2 + s)]
  simp only [add_sub_cancel_left]
  exact JacobiLogLimit.log_expected_absolute_det_tendsto hs

/-- The classical outside-edge formula is proved for the actual density
integral, including its logarithmic additive constant. -/
theorem potential_explicit {z : ℝ} (hz : 2 < z) :
    potential z = z ^ 2 / 4 - 1 / 2 - z * Real.sqrt (z ^ 2 - 4) / 4 +
      Real.log ((z + Real.sqrt (z ^ 2 - 4)) / 2) := by
  have hs : 0 < z - 2 := by linarith
  have hpoly : (z - 2) * (4 + (z - 2)) = z ^ 2 - 4 := by ring
  have hq := resolvent_quadratic hs
  have hp := resolvent_root_product hs
  rw [hpoly] at hp
  have hRdef : 2 * semicircleResolvent (z - 2) = z - Real.sqrt (z ^ 2 - 4) := by
    unfold semicircleResolvent
    rw [hpoly]
    ring
  have hinv : (z + Real.sqrt (z ^ 2 - 4)) / 2 = (semicircleResolvent (z - 2))⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    nlinarith [hq, hp]
  rw [potential_eq_outsideSpectralPotential hz, outsideSpectralPotential,
    hinv, Real.log_inv]
  have hmul := congrArg (fun a : ℝ => a * z) hRdef
  nlinarith [hq, hmul]

/-- The actual semicircle potential has the source outside-edge derivative. -/
theorem potential_hasDerivAt_explicit {z : ℝ} (hz : 2 < z) :
    HasDerivAt potential ((z - Real.sqrt (z ^ 2 - 4)) / 2) z := by
  have h := potential_hasDerivAt hz
  rw [resolvent_eq_semicircleResolvent hz] at h
  have hp : (z - 2) * (4 + (z - 2)) = z ^ 2 - 4 := by ring
  rw [semicircleResolvent, hp, show 2 + (z - 2) = z by ring] at h
  exact h

/-- The logarithmic potential is an actual integrable expectation under the
probability law; its Bochner integral does not use a nonintegrability default. -/
theorem log_abs_integrable_law {z : ℝ} (hz : 2 < z) :
    Integrable (fun t => Real.log |z - t|) law := by
  have hi := (integrable_indicator_iff measurableSet_Icc).mpr (potential_integrable hz)
  have heq : (Icc (-2 : ℝ) 2).indicator (fun t => density t * Real.log (z - t)) =
      (fun t => density t * Real.log (z - t)) := by
    funext t
    by_cases ht : t ∈ Icc (-2 : ℝ) 2
    · exact indicator_of_mem ht _
    · rw [indicator_of_notMem ht, density_eq_zero_outside ht, zero_mul]
  rw [heq] at hi
  rw [law, integrable_withDensity_iff density_continuous.measurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  convert hi using 1
  funext t
  rw [ENNReal.toReal_ofReal (density_nonneg _), Real.log_abs]
  ring

end
end SlowEquilibration.SemicirclePotential

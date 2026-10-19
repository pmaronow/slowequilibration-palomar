-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceLiteratureGroundStateProof
public import SlowEquilibration.SourceGroundProfileUniqueness
public import SlowEquilibration.LiteratureSubagProposition24Proof

/-!
# Recovery at zero temperature for the full Chen–Sen profile class

The recovery construction in Chen–Sen, arXiv:1512.08492v2, Section 2.2,
uses truncated distribution functions and a terminal atom. The cutoff used
here is slightly shifted to make the construction admissible at every
positive integer inverse temperature. All limits use the actual ordinary
Crisanti–Sommers functional and the full encoded ground-profile domain.

Recovery is fully proved. The lower-semicontinuity argument is reduced to
pointwise extraction into an admissible ground profile, and a uniform
rescaled mass bound is proved without a literature hypothesis. Extraction
itself, especially admissibility and strict limiting slack, remains
unproved; consequently this file does not derive the entire Chen–Sen
interface from Chen alone. The downstream `_reduced2` theorems retain
precisely the original minimizing-profile compactness hypothesis.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceLiteratureGroundStateFinal

open MeasureTheory ProbabilityTheory Set Filter CrisantiSommers
open SourceLiteratureGroundState SourceLiteratureGroundStateProof
open SourceLiteratureParisi SourceGroundProfileUniqueness
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem profile_continuous (u : GroundProfile) :
    ContinuousOn (profile u) (Icc 0 1) := by
  have h := intervalIntegral.continuousOn_primitive_interval'
    u.alpha_integrable (left_mem_uIcc)
  exact continuousOn_const.sub (by simpa only [uIcc_of_le zero_le_one] using h)

private theorem profile_lower (u : GroundProfile) {r : ℝ} (hr : r ∈ Icc 0 1) :
    u.L - (∫ s in (0 : ℝ)..1, u.alpha s) ≤ profile u r := by
  have htail : 0 ≤ ∫ s in r..1, u.alpha s := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hr.2
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      (volume.restrict (Icc r 1)).ae_ne (1 : ℝ)] with s hs hs1
    exact u.alpha_nonnegative s ⟨hr.1.trans hs.1, lt_of_le_of_ne hs.2 hs1⟩
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (u.alpha_integrable.mono_set (by
      rw [uIcc_of_le hr.1, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl hr.2))
    (u.alpha_integrable.mono_set (by
      rw [uIcc_of_le hr.2, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc hr.1 le_rfl))
  unfold profile
  linarith

private theorem profile_pos (u : GroundProfile) {r : ℝ} (hr : r ∈ Icc 0 1) :
    0 < profile u r :=
  (sub_pos.mpr u.height_gt_mass).trans_le (profile_lower u hr)

private theorem energy_kernel (μ : FiniteMixture) {s : ℝ} (hs : s ∈ Icc 0 1) :
    (∫ t in (0 : ℝ)..1, μ.xi2 t * (1 - max t s)) = μ.xi 1 - μ.xi s := by
  have hc : Continuous μ.xi2 := by unfold FiniteMixture.xi2; fun_prop
  have hleft : (∫ t in (0 : ℝ)..s, μ.xi2 t * (1 - max t s)) =
      (1 - s) * μ.xi1 s := by
    rw [intervalIntegral.integral_congr (g := fun t => μ.xi2 t * (1 - s))]
    · rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t _ => μ.hasDerivAt_xi1 t) (hc.intervalIntegrable _ _),
        CSTAPTelescope.xi1_zero, sub_zero]
      ring
    · intro t ht
      rw [uIcc_of_le hs.1] at ht
      dsimp only
      rw [max_eq_right ht.2]
  have hright : (∫ t in s..1, μ.xi2 t * (1 - max t s)) =
      μ.xi 1 - μ.xi s - (1 - s) * μ.xi1 s := by
    rw [intervalIntegral.integral_congr (g := fun t => μ.xi2 t * (1 - t))]
    · rw [CSTAPTelescope.integral_xi2_mul_one_sub]
      ring
    · intro t ht
      rw [uIcc_of_le hs.2] at ht
      dsimp only
      rw [max_eq_left ht.1]
  have hi : ∀ a b : ℝ,
      IntervalIntegrable (fun t => μ.xi2 t * (1 - max t s)) volume a b :=
    fun a b => (hc.mul (continuous_const.sub (continuous_id.max continuous_const)))
      |>.intervalIntegrable a b
  have h := intervalIntegral.integral_add_adjacent_intervals (hi 0 s) (hi s 1)
  rw [hleft, hright] at h
  linarith

private theorem cs_energy_eq (μ : FiniteMixture) (ζ : Admissible) :
    μ.xi 1 - (∫ s, μ.xi s ∂ζ.law) =
      ∫ t in (0 : ℝ)..1, μ.xi2 t * xHat ζ.law t := by
  let F : ℝ → ℝ → ℝ := fun t s => μ.xi2 t * (1 - max t s)
  have hc : Continuous μ.xi2 := by unfold FiniteMixture.xi2; fun_prop
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hc.continuousOn
  have hFm : Measurable (Function.uncurry F) := by dsimp [F]; fun_prop
  have hi : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod ζ.law) := by
    apply (integrable_const (max C 0)).mono' hFm.aestronglyMeasurable
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hFm.norm measurable_const)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    filter_upwards [ζ.hasCutoff.2.2] with s hs
    have hs1 : s ≤ 1 := hs.2.trans ζ.hasCutoff.2.1.le
    have hk0 : 0 ≤ 1 - max t s := sub_nonneg.mpr (max_le ht.2 hs1)
    have hk1 : 1 - max t s ≤ 1 := by linarith [le_max_left t s, ht.1]
    dsimp only [Function.uncurry_def, F]
    rw [norm_mul, Real.norm_eq_abs (1 - max t s), abs_of_nonneg hk0]
    exact (mul_le_of_le_one_right (norm_nonneg _) hk1).trans
      ((hC t ⟨ht.1.le, ht.2⟩).trans (le_max_left _ _))
  rw [← uIoc_of_le zero_le_one] at hi
  have hswap := intervalIntegral_integral_swap (f := F) (a := 0) (b := 1)
    (μ := ζ.law) hi
  have houter : (∫ s, (∫ t in (0 : ℝ)..1, F t s) ∂ζ.law) =
      μ.xi 1 - ∫ s, μ.xi s ∂ζ.law := by
    have hxi : Integrable μ.xi ζ.law := by
      have hcxi : ContinuousOn μ.xi (Icc 0 ζ.cutoff) :=
        fun r _ => (μ.hasDerivAt_xi r).continuousAt.continuousWithinAt
      have h := hcxi.integrableOn_compact isCompact_Icc (μ := ζ.law)
      simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem ζ.hasCutoff.2.2] using h
    calc
      _ = ∫ s, μ.xi 1 - μ.xi s ∂ζ.law := by
        apply integral_congr_ae
        filter_upwards [ζ.hasCutoff.2.2] with s hs
        exact energy_kernel μ ⟨hs.1, hs.2.trans ζ.hasCutoff.2.1.le⟩
      _ = _ := by rw [integral_sub (integrable_const _) hxi]; simp
  have hinner (t : ℝ) : (∫ s, F t s ∂ζ.law) = μ.xi2 t * xHat ζ.law t := by
    simp only [F, integral_const_mul, xHat]
  simp only [hinner] at hswap
  rw [houter] at hswap
  exact hswap.symm

private def inverseCutoff (ζ : Admissible) (β q t : ℝ) : ℝ :=
  if t ≤ q then (β * xHat ζ.law t)⁻¹ else 0

private theorem inverseCutoff_intervalIntegrable (ζ : Admissible) {β q : ℝ}
    (hq : HasCutoff ζ.law q) :
    IntervalIntegrable (inverseCutoff ζ β q) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have hf := ((inverse_xHat_intervalIntegrable ζ.law hq
    (a := 0) (b := q) (by norm_num) hq.2.1).div_const β).1
  have hf' : IntegrableOn (fun t => (xHat ζ.law t)⁻¹ / β) (Ioc 0 q) := hf
  have heq : inverseCutoff ζ β q = (Iic q).indicator
      (fun t => (xHat ζ.law t)⁻¹ / β) := by
    ext t
    simp only [inverseCutoff, indicator, mem_Iic]
    split_ifs <;> simp [mul_inv_rev, div_eq_mul_inv, mul_comm]
  rw [heq, integrableOn_indicator_iff measurableSet_Iic]
  simpa only [inter_comm (Iic q), Ioc_inter_Iic, min_eq_right hq.2.1.le] using hf'

private theorem inverseCutoff_integral (ζ : Admissible) {β q : ℝ}
    (_hβ : 0 < β) (hq : HasCutoff ζ.law q) :
    (∫ t in (0 : ℝ)..1, inverseCutoff ζ β q t) =
      (∫ t in (0 : ℝ)..q, (xHat ζ.law t)⁻¹) / β := by
  have hi := inverseCutoff_intervalIntegrable (β := β) ζ hq
  have hi0 := hi.mono_set (by
    rw [uIcc_of_le hq.1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hq.2.1.le)
  have hi1 := hi.mono_set (by
    rw [uIcc_of_le hq.2.1.le, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hq.1 le_rfl)
  have hzero : (∫ t in q..1, inverseCutoff ζ β q t) = 0 := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hq.2.1.le
      (g := fun _ => (0 : ℝ)) (fun t ht => by simp [inverseCutoff, not_le.mpr ht.1])]
    simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi0 hi1
  rw [hzero, add_zero] at hsplit
  rw [← hsplit, intervalIntegral.integral_congr (g := fun t => (xHat ζ.law t)⁻¹ / β)]
  · exact intervalIntegral.integral_div β _
  · intro t ht
    rw [uIcc_of_le hq.1] at ht
    simp [inverseCutoff, ht.2, mul_inv_rev, div_eq_mul_inv, mul_comm]

private theorem normalized_value_eq (μ : FiniteMixture) (ζ : Admissible)
    {β q : ℝ} (hβ : 0 < β) (hq : HasCutoff ζ.law q) :
    ζ.value β μ.xi / β =
      ((∫ t in (0 : ℝ)..1, μ.xi2 t * (β * xHat ζ.law t)) +
        (∫ t in (0 : ℝ)..1, inverseCutoff ζ β q t) + Real.log (1-q) / β) / 2 := by
  rw [ζ.value_eq β μ.xi hq, functional, cs_energy_eq,
    inverseCutoff_integral ζ hβ hq]
  have he : (∫ t in (0 : ℝ)..1, μ.xi2 t * (β * xHat ζ.law t)) =
      β * ∫ t in (0 : ℝ)..1, μ.xi2 t * xHat ζ.law t := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext t
    ring
  rw [he]
  field_simp

private def recoveryBeta (n : ℕ) : ℝ := (n + 1 : ℕ)

private theorem recoveryBeta_pos (n : ℕ) : 0 < recoveryBeta n := by
  unfold recoveryBeta
  positivity

private theorem recoveryBeta_ge_one (n : ℕ) : 1 ≤ recoveryBeta n := by
  unfold recoveryBeta
  exact_mod_cast (Nat.le_add_left 1 n)

private theorem recoveryBeta_tendsto : Tendsto recoveryBeta atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)

private def slack (u : GroundProfile) : ℝ := u.L - ∫ s in (0 : ℝ)..1, u.alpha s

private theorem slack_pos (u : GroundProfile) : 0 < slack u :=
  sub_pos.mpr u.height_gt_mass

private def recoveryCutoff (u : GroundProfile) (n : ℕ) : ℝ :=
  1 - slack u / (recoveryBeta n + slack u)

private theorem recoveryCutoff_mem (u : GroundProfile) (n : ℕ) :
    recoveryCutoff u n ∈ Ioo (0 : ℝ) 1 := by
  have hb := recoveryBeta_pos n
  have hd := slack_pos u
  unfold recoveryCutoff
  constructor
  · have := (div_lt_one (by positivity : 0 < recoveryBeta n + slack u)).mpr
      (by linarith : slack u < recoveryBeta n + slack u)
    linarith
  · have := div_pos hd (add_pos hb hd)
    linarith

private theorem recoveryCutoff_tendsto (u : GroundProfile) :
    Tendsto (recoveryCutoff u) atTop (𝓝 1) := by
  have hh : Tendsto (fun n => slack u / (recoveryBeta n + slack u)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop (slack u) recoveryBeta_tendsto)
  change Tendsto (fun n => 1 - slack u / (recoveryBeta n + slack u)) atTop (𝓝 1)
  simpa only [sub_zero] using
    (tendsto_const_nhds.sub hh : Tendsto
      (fun n => 1 - slack u / (recoveryBeta n + slack u)) atTop (𝓝 (1 - 0)))

private def recoveryCDF (u : GroundProfile) (β q s : ℝ) : ℝ :=
  if s < 0 then 0 else if s < q then min (u.alpha s / β) 1 else 1

private theorem recoveryCDF_mono (u : GroundProfile) {β q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Ico (0 : ℝ) 1) :
    Monotone (recoveryCDF u β q) := by
  intro s t hst
  by_cases hs : s < 0
  · by_cases ht : t < 0
    · simp [recoveryCDF, hs, ht]
    · by_cases htq : t < q
      · simp only [recoveryCDF, ite_eq_left hs, ite_eq_right ht, ite_eq_left htq]
        exact le_min (div_nonneg
          (u.alpha_nonnegative t ⟨le_of_not_gt ht, htq.trans hq.2⟩) hβ.le) zero_le_one
      · simp [recoveryCDF, hs, ht, htq]
  · have ht : ¬t < 0 := not_lt.mpr ((le_of_not_gt hs).trans hst)
    by_cases hsq : s < q
    · by_cases htq : t < q
      · simp only [recoveryCDF, ite_eq_right hs, ite_eq_right ht, ite_eq_left hsq, ite_eq_left htq]
        exact min_le_min_right 1 ((div_le_div_iff_of_pos_right hβ).mpr
          (u.alpha_monotone ⟨le_of_not_gt hs, hsq.trans hq.2⟩
            ⟨le_of_not_gt ht, htq.trans hq.2⟩ hst))
      · simp only [recoveryCDF, ite_eq_right hs, ite_eq_right ht, ite_eq_left hsq, ite_eq_right htq]
        exact min_le_right _ _
    · have htq : ¬t < q := not_lt.mpr ((le_of_not_gt hsq).trans hst)
      simp [recoveryCDF, hs, ht, hsq, htq]

private theorem recoveryCDF_rightContinuous (u : GroundProfile) {β q : ℝ}
    (hq : q ∈ Ico (0 : ℝ) 1) (s : ℝ) :
    ContinuousWithinAt (recoveryCDF u β q) (Ici s) s := by
  by_cases hs : s < 0
  · apply continuousWithinAt_const.congr_of_eventuallyEq
      (f := fun _ => (0 : ℝ))
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hs)] with t ht
      simp [recoveryCDF, (show t < 0 from ht)]
    · simp [recoveryCDF, hs]
  · by_cases hsq : s < q
    · have hs0 := le_of_not_gt hs
      have hc : ContinuousWithinAt (fun t => min (u.alpha t / β) 1) (Ici s) s :=
        ContinuousWithinAt.inf
          ((u.alpha_rightContinuous s ⟨hs0, hsq.trans hq.2⟩).div_const β)
          continuousWithinAt_const
      apply hc.congr_of_eventuallyEq
      · filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (Iio_mem_nhds hsq)] with t ht htq
        simp [recoveryCDF, not_lt.mpr (hs0.trans ht), (show t < q from htq)]
      · simp [recoveryCDF, hs, hsq]
    · apply continuousWithinAt_const.congr_of_eventuallyEq
        (f := fun _ => (1 : ℝ))
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simp [recoveryCDF, not_lt.mpr (hq.1.trans ((le_of_not_gt hsq).trans ht)),
          not_lt.mpr ((le_of_not_gt hsq).trans ht)]
      · simp [recoveryCDF, hs, hsq]

private def recoveryStieltjes (u : GroundProfile) {β q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Ico (0 : ℝ) 1) : StieltjesFunction ℝ where
  toFun := recoveryCDF u β q
  mono' := recoveryCDF_mono u hβ hq
  right_continuous' := recoveryCDF_rightContinuous u hq

private theorem recoveryStieltjes_bot (u : GroundProfile) {β q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Ico (0 : ℝ) 1) :
    Tendsto (recoveryStieltjes u hβ hq) atBot (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with s hs
  simp [recoveryStieltjes, recoveryCDF, hs]

private theorem recoveryStieltjes_top (u : GroundProfile) {β q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Ico (0 : ℝ) 1) :
    Tendsto (recoveryStieltjes u hβ hq) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop q] with s hs
  simp [recoveryStieltjes, recoveryCDF, not_lt.mpr (hq.1.trans hs), not_lt.mpr hs]

private theorem recoveryLaw_cutoff (u : GroundProfile) {β q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Ico (0 : ℝ) 1) :
    HasCutoff (recoveryStieltjes u hβ hq).measure q := by
  let f := recoveryStieltjes u hβ hq
  have hbot := recoveryStieltjes_bot u hβ hq
  have htop := recoveryStieltjes_top u hβ hq
  let : IsProbabilityMeasure f.measure := f.isProbabilityMeasure hbot htop
  refine ⟨hq.1, hq.2, ?_⟩
  have hleft : Function.leftLim f 0 = 0 := by
    apply leftLim_eq_of_tendsto
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp [f, recoveryStieltjes, recoveryCDF, (show s < 0 from hs)]
  have hneg : f.measure (Iio 0) = 0 := by
    rw [f.measure_Iio hbot, hleft]
    simp
  have hpos : f.measure (Ioi q) = 0 := by
    rw [f.measure_Ioi htop]
    simp [f, recoveryStieltjes, recoveryCDF, not_lt.mpr hq.1]
  rw [ae_iff]
  have hset : {s : ℝ | ¬s ∈ Icc 0 q} = Iio 0 ∪ Ioi q := by
    ext s
    simp only [mem_ofPred_eq, mem_Icc, not_and_or, not_le, mem_union, mem_Iio, mem_Ioi]
  rw [hset]
  exact measure_union_null hneg hpos

private def recoveryAdmissible (u : GroundProfile) {β q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Ico (0 : ℝ) 1) : Admissible where
  law := (recoveryStieltjes u hβ hq).measure
  probability := (recoveryStieltjes u hβ hq).isProbabilityMeasure
    (recoveryStieltjes_bot u hβ hq) (recoveryStieltjes_top u hβ hq)
  cutoff_exists := ⟨q, recoveryLaw_cutoff u hβ hq⟩

private theorem recoveryAdmissible_cutoff (u : GroundProfile) {β q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Ico (0 : ℝ) 1) :
    HasCutoff (recoveryAdmissible u hβ hq).law q := recoveryLaw_cutoff u hβ hq

private theorem recoveryAdmissible_cdf (u : GroundProfile) {β q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Ico (0 : ℝ) 1) (s : ℝ) :
    cdf (recoveryAdmissible u hβ hq).law s = recoveryCDF u β q s := by
  exact congrArg (fun f : StieltjesFunction ℝ => f s)
    (cdf_measure_stieltjesFunction _ (recoveryStieltjes_bot u hβ hq)
      (recoveryStieltjes_top u hβ hq))

private theorem scaled_xHat_nonneg (ζ : Admissible) {β t : ℝ}
    (hβ : 0 ≤ β) (ht : t ≤ 1) : 0 ≤ β * xHat ζ.law t := by
  have hh := xHat_lower_bound ζ.law ζ.hasCutoff t
  have hk : 0 ≤ 1 - max t ζ.cutoff :=
    sub_nonneg.mpr (max_le ht ζ.hasCutoff.2.1.le)
  exact mul_nonneg hβ (hk.trans hh)

private theorem scaled_energy_tendsto (μ : FiniteMixture) (u : GroundProfile)
    (ζ : ℕ → Admissible) (β q : ℕ → ℝ)
    (hβ : ∀ n, 0 < β n) (hq : ∀ n, HasCutoff (ζ n).law (q n))
    {C : ℝ} (hupper : ∀ᶠ n in atTop,
      ∀ t ∈ Icc (0 : ℝ) 1, β n * xHat (ζ n).law t ≤ C)
    (hlim : ∀ t ∈ Ico (0 : ℝ) 1,
      Tendsto (fun n => β n * xHat (ζ n).law t) atTop (𝓝 (profile u t))) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..1, μ.xi2 t * (β n * xHat (ζ n).law t)) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, μ.xi2 t * profile u t)) := by
  have hcxi : Continuous μ.xi2 := by unfold FiniteMixture.xi2; fun_prop
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun t => ‖μ.xi2 t‖ * C)
  · exact .of_forall fun n =>
      (hcxi.mul ((xHat_continuous (ζ n).law (hq n)).const_mul (β n))).aestronglyMeasurable
  · filter_upwards [hupper] with n hn
    apply Eventually.of_forall
    intro t ht
    rw [uIoc_of_le zero_le_one] at ht
    rw [norm_mul, Real.norm_eq_abs (β n * xHat (ζ n).law t),
      abs_of_nonneg (scaled_xHat_nonneg (ζ n) (hβ n).le ht.2)]
    exact mul_le_mul_of_nonneg_left (hn t ⟨ht.1.le, ht.2⟩) (norm_nonneg _)
  · exact (hcxi.norm.mul continuous_const).intervalIntegrable _ _
  · filter_upwards [volume.ae_ne (1 : ℝ)] with t ht1 ht
    rw [uIoc_of_le zero_le_one] at ht
    exact tendsto_const_nhds.mul (hlim t ⟨ht.1.le, lt_of_le_of_ne ht.2 ht1⟩)

private theorem normalized_values_tendsto (μ : FiniteMixture) (u : GroundProfile)
    (ζ : ℕ → Admissible) (β q : ℕ → ℝ)
    (hβ : ∀ n, 0 < β n) (hq : ∀ n, HasCutoff (ζ n).law (q n))
    (hqLim : Tendsto q atTop (𝓝 1))
    (hlog : Tendsto (fun n => Real.log (1 - q n) / β n) atTop (𝓝 0))
    {C c : ℝ} (hc : 0 < c)
    (hupper : ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) 1, β n * xHat (ζ n).law t ≤ C)
    (hlower : ∀ᶠ n in atTop, c ≤ β n * (1 - q n))
    (hlim : ∀ t ∈ Ico (0 : ℝ) 1,
      Tendsto (fun n => β n * xHat (ζ n).law t) atTop (𝓝 (profile u t))) :
    Tendsto (fun n => (ζ n).value (β n) μ.xi / β n) atTop
      (𝓝 (groundFunctional μ u)) := by
  have henergy := scaled_energy_tendsto μ u ζ β q hβ hq hupper hlim
  have hentropy : Tendsto (fun n => ∫ t in (0 : ℝ)..1,
      inverseCutoff (ζ n) (β n) (q n) t) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, (profile u t)⁻¹)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => c⁻¹)
    · exact .of_forall fun n =>
        ((((xHat_continuous (ζ n).law (hq n)).const_mul (β n)).measurable.inv).ite
          measurableSet_Iic measurable_const).aestronglyMeasurable
    · filter_upwards [hlower] with n hn
      apply Eventually.of_forall
      intro t ht
      dsimp only [inverseCutoff]
      split_ifs with htq
      · have hlo := mul_le_mul_of_nonneg_left
          (xHat_ge_one_sub_cutoff (ζ n).law (hq n) htq) (hβ n).le
        have hp : 0 < β n * xHat (ζ n).law t := hc.trans_le (hn.trans hlo)
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
        exact inv_anti₀ hc (hn.trans hlo)
      · simpa only [norm_zero] using (inv_pos.mpr hc).le
    · exact intervalIntegrable_const
    · filter_upwards [volume.ae_ne (1 : ℝ)] with t ht1 ht
      rw [uIoc_of_le zero_le_one] at ht
      have ht' : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1.le, lt_of_le_of_ne ht.2 ht1⟩
      apply ((hlim t ht').inv₀ (profile_pos u ⟨ht'.1, ht'.2.le⟩).ne').congr'
      filter_upwards [(tendsto_order.mp hqLim).1 t ht'.2] with n hn
      simp [inverseCutoff, hn.le]
  have h := ((henergy.add hentropy).add hlog).div_const 2
  rw [add_zero, ← groundFunctional_eq_integral] at h
  apply h.congr'
  exact .of_forall fun n => (normalized_value_eq μ (ζ n) (hβ n) (hq n)).symm

private def recoverySequence (u : GroundProfile) (n : ℕ) : Admissible :=
  recoveryAdmissible u (recoveryBeta_pos n)
    ⟨(recoveryCutoff_mem u n).1.le, (recoveryCutoff_mem u n).2⟩

private theorem recoverySequence_cutoff (u : GroundProfile) (n : ℕ) :
    HasCutoff (recoverySequence u n).law (recoveryCutoff u n) :=
  recoveryAdmissible_cutoff u _ _

private def truncatedSlope (u : GroundProfile) (n : ℕ) (s : ℝ) : ℝ :=
  if s < recoveryCutoff u n then min (u.alpha s) (recoveryBeta n) else 0

private theorem truncatedSlope_norm (u : GroundProfile) (n : ℕ) (s : ℝ) :
    ‖truncatedSlope u n s‖ ≤ ‖u.alpha s‖ := by
  unfold truncatedSlope
  split_ifs
  · by_cases hs : u.alpha s ≤ recoveryBeta n
    · rw [min_eq_left hs]
    · rw [min_eq_right (le_of_not_ge hs), Real.norm_eq_abs,
        abs_of_pos (recoveryBeta_pos n)]
      exact (le_of_not_ge hs).trans (le_abs_self _)
  · simpa only [norm_zero] using (norm_nonneg (u.alpha s))

private theorem alpha_integrable_tail (u : GroundProfile) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) : IntervalIntegrable u.alpha volume r 1 :=
  u.alpha_integrable.mono_set (by
    rw [uIcc_of_le hr.2, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hr.1 le_rfl)

private theorem truncatedSlope_measurable (u : GroundProfile) (n : ℕ) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) :
    AEStronglyMeasurable (truncatedSlope u n) (volume.restrict (uIoc r 1)) := by
  rw [uIoc_of_le hr.2]
  have hm : AEStronglyMeasurable (fun s => min (u.alpha s) (recoveryBeta n))
      (volume.restrict (Ioc r 1)) :=
    ((alpha_integrable_tail u hr).1.aestronglyMeasurable.aemeasurable.min
      aemeasurable_const).aestronglyMeasurable
  exact hm.indicator measurableSet_Iio

private theorem truncatedSlope_integrable (u : GroundProfile) (n : ℕ) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (truncatedSlope u n) volume r 1 := by
  rw [intervalIntegrable_iff, uIoc_of_le hr.2]
  exact ((alpha_integrable_tail u hr).1.norm).mono'
    (by simpa only [uIoc_of_le hr.2] using truncatedSlope_measurable u n hr) (.of_forall (truncatedSlope_norm u n))

private theorem truncatedSlope_integral_tendsto (u : GroundProfile) {r : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) :
    Tendsto (fun n => ∫ s in r..1, truncatedSlope u n s) atTop
      (𝓝 (∫ s in r..1, u.alpha s)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun s => ‖u.alpha s‖)
  · exact .of_forall fun n => truncatedSlope_measurable u n ⟨hr.1, hr.2.le⟩
  · exact .of_forall fun n => .of_forall fun s _ => truncatedSlope_norm u n s
  · exact (alpha_integrable_tail u ⟨hr.1, hr.2.le⟩).norm
  · filter_upwards [volume.ae_ne (1 : ℝ)] with s hs1 hs
    rw [uIoc_of_le hr.2.le] at hs
    have hs' : s < 1 := lt_of_le_of_ne hs.2 hs1
    apply tendsto_const_nhds.congr'
    filter_upwards [(tendsto_order.mp (recoveryCutoff_tendsto u)).1 s hs',
      recoveryBeta_tendsto.eventually (eventually_ge_atTop (u.alpha s))] with n hq hn
    simp [truncatedSlope, hq, min_eq_left hn]

private theorem recovery_scaled_xHat (u : GroundProfile) (n : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (hrq : r ≤ recoveryCutoff u n) :
    recoveryBeta n * xHat (recoverySequence u n).law r =
      recoveryBeta n * (1 - recoveryCutoff u n) +
        ∫ s in r..1, truncatedSlope u n s := by
  let ζ := recoverySequence u n
  let β := recoveryBeta n
  let q := recoveryCutoff u n
  have hβ : 0 < β := recoveryBeta_pos n
  have hq := recoveryCutoff_mem u n
  have hcut : HasCutoff ζ.law q := recoverySequence_cutoff u n
  have hcdf (s : ℝ) : cdf ζ.law s = recoveryCDF u β q s :=
    recoveryAdmissible_cdf u _ _ s
  have hi0 : IntervalIntegrable (cdf ζ.law) volume r q :=
    (monotone_cdf ζ.law).intervalIntegrable
  have hi1 : IntervalIntegrable (cdf ζ.law) volume q 1 :=
    (monotone_cdf ζ.law).intervalIntegrable
  have htail : (∫ s in q..1, cdf ζ.law s) = 1 - q := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))]
    · simp
    · intro s hs
      rw [uIcc_of_le hq.2.le] at hs
      rw [hcdf]
      have hsq : q ≤ s := hs.1
      simp [recoveryCDF, not_lt.mpr (hq.1.le.trans hs.1), not_lt.mpr hsq]
  have hfirst : β * (∫ s in r..q, cdf ζ.law s) =
      ∫ s in r..q, truncatedSlope u n s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le hrq
    intro s hs
    change β * cdf ζ.law s = truncatedSlope u n s
    rw [hcdf]
    change β * recoveryCDF u β q s = if s < q then min (u.alpha s) β else 0
    have hs0 : ¬s < 0 := not_lt.mpr (hr.trans hs.1.le)
    have hsq : s < q := hs.2
    simp only [recoveryCDF, ite_eq_right hs0, ite_eq_left hsq]
    rw [← div_self hβ.ne', min_div_div_right hβ.le,
      mul_div_cancel₀ _ hβ.ne']
  have hT := truncatedSlope_integrable u n ⟨hr, hrq.trans hq.2.le⟩
  have hT0 : IntervalIntegrable (truncatedSlope u n) volume r q :=
    hT.mono_set (by
      rw [uIcc_of_le hrq, uIcc_of_le (hrq.trans hq.2.le)]
      exact Icc_subset_Icc le_rfl hq.2.le)
  have hT1 := truncatedSlope_integrable u n ⟨hq.1.le, hq.2.le⟩
  have hTtail : (∫ s in q..1, truncatedSlope u n s) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro s hs
      rw [uIcc_of_le hq.2.le] at hs
      simp [truncatedSlope, not_lt.mpr hs.1]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hT0 hT1
  rw [hTtail, add_zero] at hsplit
  rw [xHat_integrated_cdf ζ.law hcut (hrq.trans hq.2.le),
    ← intervalIntegral.integral_add_adjacent_intervals hi0 hi1, htail, mul_add,
    hfirst, hsplit, add_comm]

private theorem recovery_gap_tendsto (u : GroundProfile) :
    Tendsto (fun n => recoveryBeta n * (1 - recoveryCutoff u n)) atTop
      (𝓝 (slack u)) := by
  have hsmall : Tendsto (fun n => slack u / (recoveryBeta n + slack u)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop (slack u) recoveryBeta_tendsto)
  have h : Tendsto (fun n => slack u * (1 - slack u / (recoveryBeta n + slack u)))
      atTop (𝓝 (slack u * (1 - 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub hsmall)
  have h' : Tendsto (fun n => slack u * (1 - slack u / (recoveryBeta n + slack u)))
      atTop (𝓝 (slack u)) := by simpa using h
  apply h'.congr'
  apply Eventually.of_forall
  intro n
  have hn : recoveryBeta n + slack u ≠ 0 := (add_pos (recoveryBeta_pos n) (slack_pos u)).ne'
  dsimp [recoveryCutoff]
  field_simp
  ring

private theorem recovery_kernel_tendsto (u : GroundProfile) {r : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) :
    Tendsto (fun n => recoveryBeta n * xHat (recoverySequence u n).law r) atTop
      (𝓝 (profile u r)) := by
  have h := (recovery_gap_tendsto u).add (truncatedSlope_integral_tendsto u hr)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (u.alpha_integrable.mono_set (by
      rw [uIcc_of_le hr.1, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl hr.2.le))
    (alpha_integrable_tail u ⟨hr.1, hr.2.le⟩)
  have heq : slack u + (∫ s in r..1, u.alpha s) = profile u r := by
    unfold slack profile
    linarith
  rw [heq] at h
  apply h.congr'
  filter_upwards [(tendsto_order.mp (recoveryCutoff_tendsto u)).1 r hr.2] with n hn
  exact (recovery_scaled_xHat u n hr.1 hn.le).symm

private theorem recovery_gap_lower (u : GroundProfile) (n : ℕ) :
    slack u / (1 + slack u) ≤ recoveryBeta n * (1 - recoveryCutoff u n) := by
  have hd := slack_pos u
  have hb := recoveryBeta_pos n
  have hb1 := recoveryBeta_ge_one n
  dsimp only [recoveryCutoff]
  rw [sub_sub_cancel, ← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity : 0 < 1 + slack u)
    (add_pos hb hd)).mpr
  nlinarith [mul_nonneg (sq_nonneg (slack u)) (sub_nonneg.mpr hb1)]

private theorem recovery_gap_upper (u : GroundProfile) (n : ℕ) :
    recoveryBeta n * (1 - recoveryCutoff u n) ≤ slack u := by
  have hd := slack_pos u
  have hb := recoveryBeta_pos n
  dsimp only [recoveryCutoff]
  rw [sub_sub_cancel, ← mul_div_assoc]
  apply (div_le_iff₀ (add_pos hb hd)).mpr
  nlinarith [sq_nonneg (slack u)]

private theorem recovery_kernel_upper (u : GroundProfile) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    recoveryBeta n * xHat (recoverySequence u n).law t ≤ u.L := by
  have hcut := recoverySequence_cutoff u n
  have hmono : xHat (recoverySequence u n).law t ≤
      xHat (recoverySequence u n).law 0 := by
    apply integral_mono (kernel_integrable _ hcut t) (kernel_integrable _ hcut 0)
    intro s
    exact sub_le_sub_left (max_le_max_right s ht.1) 1
  have hTle : (∫ s in (0 : ℝ)..1, truncatedSlope u n s) ≤
      ∫ s in (0 : ℝ)..1, u.alpha s := by
    apply intervalIntegral.integral_mono_ae_restrict zero_le_one
      (truncatedSlope_integrable u n ⟨le_rfl, zero_le_one⟩) u.alpha_integrable
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      (volume.restrict (Icc (0 : ℝ) 1)).ae_ne (1 : ℝ)] with s hs hs1
    dsimp only [truncatedSlope]
    split_ifs
    · exact min_le_left _ _
    · exact u.alpha_nonnegative s ⟨hs.1, lt_of_le_of_ne hs.2 hs1⟩
  have hzero := recovery_scaled_xHat u n (r := 0) le_rfl
    (recoveryCutoff_mem u n).1.le
  have hh := mul_le_mul_of_nonneg_left hmono (recoveryBeta_pos n).le
  have hgap := recovery_gap_upper u n
  unfold slack at hgap
  linarith

private theorem recovery_log_tendsto (u : GroundProfile) :
    Tendsto (fun n => Real.log (1 - recoveryCutoff u n) / recoveryBeta n)
      atTop (𝓝 0) := by
  have hconst : Tendsto (fun n => Real.log (slack u) / recoveryBeta n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop recoveryBeta_tendsto
  have hlog : Tendsto (fun n => Real.log (recoveryBeta n + slack u) / recoveryBeta n)
      atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-slack u) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_right atTop (slack u) recoveryBeta_tendsto)
    simpa only [Function.comp_def, pow_one, one_mul, add_neg_cancel_right] using h
  have h := hconst.sub hlog
  simp only [sub_zero] at h
  apply h.congr'
  apply Eventually.of_forall
  intro n
  have hd := slack_pos u
  have hb := add_pos (recoveryBeta_pos n) hd
  simp only [recoveryCutoff, sub_sub_cancel, Real.log_div hd.ne' hb.ne', sub_div]

/-- Chen–Sen's recovery step for every encoded ground profile, without
any finite-temperature Parisi hypothesis. The laws are actual admissible
probability measures obtained from truncated distribution functions. -/
theorem groundRecoverySequences : GroundRecoverySequences := by
  intro μ u
  refine ⟨recoverySequence u, ?_⟩
  exact normalized_values_tendsto μ u (recoverySequence u) recoveryBeta
    (recoveryCutoff u) recoveryBeta_pos (recoverySequence_cutoff u)
    (recoveryCutoff_tendsto u) (recovery_log_tendsto u)
    (div_pos (slack_pos u) (by linarith [slack_pos u]))
    (.of_forall fun n t ht => recovery_kernel_upper u n ht)
    (.of_forall (recovery_gap_lower u))
    (fun t ht => recovery_kernel_tendsto u ht)

private theorem inverseCutoff_nonneg (ζ : Admissible) {β q : ℝ}
    (hβ : 0 < β) (hq : HasCutoff ζ.law q) (t : ℝ) :
    0 ≤ inverseCutoff ζ β q t := by
  dsimp only [inverseCutoff]
  split_ifs with ht
  · exact (inv_pos.mpr (mul_pos hβ (xHat_pos ζ.law hq (ht.trans_lt hq.2.1)))).le
  · exact le_rfl

private theorem inverseCutoff_measurable (ζ : Admissible) {β q : ℝ}
    (hq : HasCutoff ζ.law q) : Measurable (inverseCutoff ζ β q) :=
  ((((xHat_continuous ζ.law hq).const_mul β).measurable.inv).ite
    measurableSet_Iic measurable_const)

private theorem normalized_liminf_of_kernel_limit
    (μ : FiniteMixture) (u : GroundProfile) (ζ : ℕ → Admissible) (β q : ℕ → ℝ)
    (hβ : ∀ n, 0 < β n) (hq : ∀ n, HasCutoff (ζ n).law (q n))
    (hqLim : Tendsto q atTop (𝓝 1))
    (hlog : Tendsto (fun n => Real.log (1 - q n) / β n) atTop (𝓝 0))
    (hlim : ∀ t ∈ Ico (0 : ℝ) 1,
      Tendsto (fun n => β n * xHat (ζ n).law t) atTop (𝓝 (profile u t))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      groundFunctional μ u ≤ (ζ n).value (β n) μ.xi / β n + ε := by
  let M := (slack u)⁻¹
  have hM : 0 < M := inv_pos.mpr (slack_pos u)
  let T : ℕ → ℝ → ℝ := fun n t => min (inverseCutoff (ζ n) (β n) (q n) t) M
  have hTm (n : ℕ) : Measurable (T n) :=
    (inverseCutoff_measurable (ζ n) (hq n)).min measurable_const
  have hTnorm (n : ℕ) (t : ℝ) : ‖T n t‖ ≤ M := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (le_min (inverseCutoff_nonneg (ζ n) (hβ n) (hq n) t) hM.le)]
    exact min_le_right _ _
  have hTint (n : ℕ) : IntervalIntegrable (T n) volume 0 1 := by
    rw [intervalIntegrable_iff, uIoc_of_le zero_le_one]
    exact (integrable_const M).mono' (hTm n).aestronglyMeasurable
      (.of_forall (hTnorm n))
  have hupper : ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      β n * xHat (ζ n).law t ≤ profile u 0 + 1 := by
    filter_upwards [(tendsto_order.mp (hlim 0 ⟨le_rfl, zero_lt_one⟩)).2
      (profile u 0 + 1) (by linarith)] with n hn t ht
    have hmono : xHat (ζ n).law t ≤ xHat (ζ n).law 0 := by
      apply integral_mono (kernel_integrable _ (hq n) t) (kernel_integrable _ (hq n) 0)
      intro s
      exact sub_le_sub_left (max_le_max_right s ht.1) 1
    exact (mul_le_mul_of_nonneg_left hmono (hβ n).le).trans hn.le
  have henergy := scaled_energy_tendsto μ u ζ β q hβ hq hupper hlim
  have hentropy : Tendsto (fun n => ∫ t in (0 : ℝ)..1, T n t) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, (profile u t)⁻¹)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
    · exact .of_forall fun n => (hTm n).aestronglyMeasurable
    · exact .of_forall fun n => .of_forall fun t _ => hTnorm n t
    · exact intervalIntegrable_const
    · filter_upwards [volume.ae_ne (1 : ℝ)] with t ht1 ht
      rw [uIoc_of_le zero_le_one] at ht
      have ht' : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1.le, lt_of_le_of_ne ht.2 ht1⟩
      have hinv : Tendsto (fun n => inverseCutoff (ζ n) (β n) (q n) t) atTop
          (𝓝 ((profile u t)⁻¹)) := by
        apply ((hlim t ht').inv₀ (profile_pos u ⟨ht'.1, ht'.2.le⟩).ne').congr'
        filter_upwards [(tendsto_order.mp hqLim).1 t ht'.2] with n hn
        simp [inverseCutoff, hn.le]
      have hbound : (profile u t)⁻¹ ≤ M :=
        inv_anti₀ (slack_pos u) (profile_lower u ⟨ht'.1, ht'.2.le⟩)
      have h : Tendsto (fun n => T n t) atTop (𝓝 (min ((profile u t)⁻¹) M)) :=
        hinv.min tendsto_const_nhds
      simpa only [min_eq_left hbound] using h
  have hlo := ((henergy.add hentropy).add hlog).div_const 2
  rw [add_zero, ← groundFunctional_eq_integral] at hlo
  have hbelow (n : ℕ) :
      ((∫ t in (0 : ℝ)..1, μ.xi2 t * (β n * xHat (ζ n).law t)) +
        (∫ t in (0 : ℝ)..1, T n t) + Real.log (1-q n) / β n) / 2 ≤
      (ζ n).value (β n) μ.xi / β n := by
    rw [normalized_value_eq μ (ζ n) (hβ n) (hq n)]
    have he := intervalIntegral.integral_mono_on zero_le_one (hTint n)
      (inverseCutoff_intervalIntegrable (β := β n) (ζ n) (hq n))
      (fun t _ => min_le_left (inverseCutoff (ζ n) (β n) (q n) t) M)
    linarith
  intro ε hε
  filter_upwards [(tendsto_order.mp hlo).1 (groundFunctional μ u - ε)
    (by linarith)] with n hn
  linarith [hbelow n]

private def compactnessCutoff (μ : FiniteMixture) (β : ℝ) : ℝ :=
  1 - (β^2 * ((CSCompactAttainment.mixtureLipschitzConstant μ : ℝ) + 1) + 2)⁻¹

private theorem compactnessCutoff_mem (μ : FiniteMixture) (β : ℝ) :
    compactnessCutoff μ β ∈ Ioo (0 : ℝ) 1 := by
  have hA : 0 ≤ β^2 * ((CSCompactAttainment.mixtureLipschitzConstant μ : ℝ) + 1) :=
    mul_nonneg (sq_nonneg β) (by positivity)
  have hD : 0 < β^2 * ((CSCompactAttainment.mixtureLipschitzConstant μ : ℝ) + 1) + 2 :=
    by linarith
  have hsmall := (inv_lt_one₀ hD).mpr (by linarith)
  have hpos := inv_pos.mpr hD
  unfold compactnessCutoff
  constructor <;> linarith

private theorem canonicalMinimizer_compactnessCutoff (μ : FiniteMixture) (β : ℝ) :
    HasCutoff (CSParisiMeasure.canonicalMinimizer μ β).law (compactnessCutoff μ β) := by
  have hm := compactnessCutoff_mem μ β
  apply CSStability.canonicalMinimizer_hasCutoff_of_lipschitz μ β
    (CSCompactAttainment.mixtureLipschitzConstant μ)
    (CSCompactAttainment.mixture_xi_lipschitzOn μ) hm.1.le hm.2
  have hD : β^2 * ((CSCompactAttainment.mixtureLipschitzConstant μ : ℝ) + 1) + 2 ≠ 0 :=
    ne_of_gt (by positivity)
  have heq : compactnessCutoff μ β / (1 - compactnessCutoff μ β) =
      β^2 * ((CSCompactAttainment.mixtureLipschitzConstant μ : ℝ) + 1) + 1 := by
    unfold compactnessCutoff
    field_simp [hD]
    ring
  rw [heq]
  nlinarith [sq_nonneg β]

private theorem compactnessCutoff_limits (μ : FiniteMixture) (β : ℕ → ℝ)
    (hβ : ∀ n, 1 ≤ β n) (hβLim : Tendsto β atTop atTop) :
    Tendsto (fun n => compactnessCutoff μ (β n)) atTop (𝓝 1) ∧
      Tendsto (fun n => Real.log (1 - compactnessCutoff μ (β n)) / β n)
        atTop (𝓝 0) := by
  let L : ℝ := CSCompactAttainment.mixtureLipschitzConstant μ
  let D : ℕ → ℝ := fun n => (β n)^2 * (L+1) + 2
  have hL : 0 ≤ L := (CSCompactAttainment.mixtureLipschitzConstant μ).property
  have hβpos (n : ℕ) : 0 < β n := by linarith [hβ n]
  have hDpos (n : ℕ) : 0 < D n := by dsimp [D]; positivity
  have hDbig (n : ℕ) : 1 ≤ D n := by dsimp [D]; nlinarith [sq_nonneg (β n)]
  have hDlim : Tendsto D atTop atTop := by
    apply tendsto_atTop_mono (fun n => ?_) hβLim
    dsimp [D]
    nlinarith [sq_nonneg (β n - 1), mul_nonneg (sq_nonneg (β n)) hL, hβ n]
  have hq : Tendsto (fun n => compactnessCutoff μ (β n)) atTop (𝓝 1) := by
    have h : Tendsto (fun n => 1 - (D n)⁻¹) atTop (𝓝 (1-0)) :=
      tendsto_const_nhds.sub (tendsto_inv_atTop_zero.comp hDlim)
    change Tendsto (fun n => 1 - (D n)⁻¹) atTop (𝓝 1)
    simpa only [sub_zero] using h
  refine ⟨hq, ?_⟩
  have hlogβ : Tendsto (fun n => Real.log (β n) / β n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hβLim
  have hc : Tendsto (fun n => Real.log (L+3) / β n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hβLim
  have hmajor : Tendsto (fun n => (2 * Real.log (β n) + Real.log (L+3)) / β n)
      atTop (𝓝 0) := by
    simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using
      (hlogβ.const_mul 2).add hc
  have hlogD : Tendsto (fun n => Real.log (D n) / β n) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => div_nonneg (Real.log_nonneg (hDbig n)) (hβpos n).le)
      (fun n => ?_) hmajor
    apply div_le_div_of_nonneg_right _ (hβpos n).le
    have hbound : D n ≤ (β n)^2 * (L+3) := by
      dsimp [D]
      nlinarith [sq_nonneg (β n - 1), hβ n]
    have h := Real.log_le_log (hDpos n) hbound
    rw [Real.log_mul (pow_ne_zero 2 (hβpos n).ne') (by linarith : L+3 ≠ 0),
      Real.log_pow] at h
    norm_num at h
    exact h
  have h := hlogD.neg
  simpa only [compactnessCutoff, sub_sub_cancel, Real.log_inv, neg_div, neg_zero] using h

/-- The remaining compactness problem: extract an admissible ground
profile as a pointwise limit of the rescaled actual minimizing kernels.
No functional inequality or convergence of variational values is assumed. -/
def RescaledMinimizerExtraction : Prop :=
  ∀ μ : FiniteMixture, ∃ u : GroundProfile, ∃ φ : ℕ → ℕ,
    StrictMono φ ∧ ∀ t ∈ Ico (0 : ℝ) 1,
      Tendsto (fun n => ((φ n + 1 : ℕ) : ℝ) *
        xHat (CSParisiMeasure.canonicalMinimizer μ ((φ n + 1 : ℕ) : ℝ)).law t)
        atTop (𝓝 (profile u t))

/-- Pointwise extraction into the exact admissible ground-profile class
implies the original compactness/liminf statement. Bounded truncation of
reciprocal entropy proves the lower-semicontinuity step, without assuming
nondegeneracy of the finite-temperature cutoffs. -/
theorem groundMinimizerLiminfCompactness_of_extraction
    (hExtraction : RescaledMinimizerExtraction) : GroundMinimizerLiminfCompactness := by
  intro μ
  obtain ⟨u, φ, hφ, hlim⟩ := hExtraction μ
  let β : ℕ → ℝ := fun n => ((φ n + 1 : ℕ) : ℝ)
  have hβpos (n : ℕ) : 0 < β n := recoveryBeta_pos (φ n)
  have hβone (n : ℕ) : 1 ≤ β n := recoveryBeta_ge_one (φ n)
  have hβLim : Tendsto β atTop atTop := recoveryBeta_tendsto.comp hφ.tendsto_atTop
  obtain ⟨hqLim, hlog⟩ := compactnessCutoff_limits μ β hβone hβLim
  have hval := normalized_liminf_of_kernel_limit μ u
    (fun n => CSParisiMeasure.canonicalMinimizer μ (β n)) β
    (fun n => compactnessCutoff μ (β n)) hβpos
    (fun n => canonicalMinimizer_compactnessCutoff μ (β n)) hqLim hlog hlim
  exact ⟨u, φ, hφ, hval⟩

/-- Recovery is discharged; only the exact original minimizing-profile
compactness statement remains in addition to Chen's Parisi formula. -/
theorem chenSenFiniteGround_of_minimizer_compactness
    (hChen : Chen2013FiniteParisi)
    (hCompactness : GroundMinimizerLiminfCompactness) : ChenSenFiniteGround :=
  chenSenFiniteGround_of_variational_steps hChen groundRecoverySequences hCompactness

/-- The same interface reduced to concrete rescaled-minimizer extraction.
No recovery, lower-semicontinuity, or thermodynamic limit is assumed here. -/
theorem chenSenFiniteGround_of_rescaled_minimizers
    (hChen : Chen2013FiniteParisi)
    (hExtraction : RescaledMinimizerExtraction) : ChenSenFiniteGround :=
  chenSenFiniteGround_of_minimizer_compactness hChen
    (groundMinimizerLiminfCompactness_of_extraction hExtraction)

private theorem admissible_entropy_nonneg (ζ : Admissible) :
    0 ≤ (∫ t in (0 : ℝ)..ζ.cutoff, (xHat ζ.law t)⁻¹) +
      Real.log (1 - ζ.cutoff) := by
  have hi : IntervalIntegrable (fun t : ℝ => (1-t)⁻¹) volume 0 ζ.cutoff := by
    apply ContinuousOn.intervalIntegrable
    apply (continuous_const.sub continuous_id).continuousOn.inv₀
    intro t ht
    rw [uIcc_of_le ζ.hasCutoff.1] at ht
    exact (sub_pos.mpr (ht.2.trans_lt ζ.hasCutoff.2.1)).ne'
  have h := intervalIntegral.integral_mono_on ζ.hasCutoff.1 hi
    (inverse_xHat_intervalIntegrable ζ.law ζ.hasCutoff (by norm_num) ζ.hasCutoff.2.1)
    (fun t ht => inv_anti₀ (xHat_pos ζ.law ζ.hasCutoff
      (ht.2.trans_lt ζ.hasCutoff.2.1)) (xHat_upper_bound ζ.law ζ.hasCutoff t))
  rw [integral_inverse_one_sub (by norm_num) ζ.hasCutoff.2.1] at h
  norm_num at h
  linarith

private theorem cs_value_le_linear (μ : FiniteMixture) {β : ℝ} (hβ : 1 ≤ β) :
    CSParisiMeasure.variationalValue μ β ≤
      β * ((CSCompactAttainment.mixtureLipschitzConstant μ : ℝ) + 1) / 2 := by
  have hβpos : 0 < β := by linarith
  have hβne := hβpos.ne'
  let q : ℝ := 1 - β⁻¹
  have hq0 : 0 ≤ q := sub_nonneg.mpr (inv_le_one_of_one_le₀ hβ)
  have hq1 : q < 1 := by dsimp only [q]; linarith [inv_pos.mpr hβpos]
  have hq : q ∈ Ico (0 : ℝ) 1 := ⟨hq0, hq1⟩
  let ζ : Admissible := ⟨Measure.dirac q, inferInstance, ⟨q, dirac_hasCutoff hq⟩⟩
  have h := CSParisiMeasure.canonicalMinimizer_isMinimizer μ β ζ
  rw [ζ.value_eq β μ.xi (dirac_hasCutoff hq), functional_dirac β μ.xi hq] at h
  have hLip := (CSCompactAttainment.mixture_xi_lipschitzOn μ).dist_le_mul
    1 ⟨by norm_num, le_rfl⟩ q ⟨hq0, hq1.le⟩
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hq1.le)] at hLip
  have hgap := (le_abs_self (μ.xi 1 - μ.xi q)).trans hLip
  have henergy := mul_le_mul_of_nonneg_left hgap (sq_nonneg β)
  have hprod : β^2 * ((CSCompactAttainment.mixtureLipschitzConstant μ : ℝ)*(1-q)) =
      β * (CSCompactAttainment.mixtureLipschitzConstant μ : ℝ) := by
    dsimp only [q]
    field_simp [hβne]
    ring
  rw [hprod] at henergy
  have hquot : q / (1-q) = β-1 := by
    dsimp only [q]
    field_simp [hβne]
    ring
  have hlog : Real.log (1-q) ≤ 0 :=
    Real.log_nonpos (sub_pos.mpr hq1).le (by linarith)
  rw [hquot] at h
  change CSParisiMeasure.variationalValue μ β ≤ _ at h
  linarith

/-- A uniform mass bound for the genuine rescaled minimizers (the
compactness estimates preceding Chen–Sen's extraction). This is a purely
variational consequence of a Dirac trial and entropy nonnegativity. -/
theorem canonicalMinimizer_rescaled_mass_le (μ : FiniteMixture) {β : ℝ} (hβ : 1 ≤ β) :
    β * xHat (CSParisiMeasure.canonicalMinimizer μ β).law 0 ≤
      ((CSCompactAttainment.mixtureLipschitzConstant μ : ℝ) + 1) / μ.xi 1 := by
  let ζ := CSParisiMeasure.canonicalMinimizer μ β
  have hβpos : 0 < β := by linarith
  have hv := cs_value_le_linear μ hβ
  change (β^2 * (μ.xi 1 - ∫ r, μ.xi r ∂ζ.law) +
    (∫ t in (0 : ℝ)..ζ.cutoff, (xHat ζ.law t)⁻¹) +
      Real.log (1-ζ.cutoff)) / 2 ≤ _ at hv
  have hS := admissible_entropy_nonneg ζ
  have hE : β * (μ.xi 1 - ∫ r, μ.xi r ∂ζ.law) ≤
      (CSCompactAttainment.mixtureLipschitzConstant μ : ℝ) + 1 := by
    have h : β * (β * (μ.xi 1 - ∫ r, μ.xi r ∂ζ.law) -
        ((CSCompactAttainment.mixtureLipschitzConstant μ : ℝ) + 1)) ≤ β * 0 := by
      nlinarith
    exact sub_nonpos.mp ((mul_le_mul_iff_right₀ hβpos).mp (by simpa only [mul_comm] using h))
  have hxi (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) : μ.xi r ≤ μ.xi 1 * r := by
    unfold FiniteMixture.xi
    simp only [one_pow, mul_one]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro p hp
    have hp2 := μ.degree_ge_two hp
    have heq : p = (p-1)+1 := by omega
    have hpw : r^p ≤ r := by
      rw [heq, pow_succ]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (pow_le_one₀ hr.1 hr.2 : r^(p-1) ≤ 1) hr.1
    exact mul_le_mul_of_nonneg_left hpw (μ.nonneg p)
  have hiξ := CSStability.integrable_of_cutoff ζ.law ζ.hasCutoff
    (fun r _ => (μ.hasDerivAt_xi r).continuousAt.continuousWithinAt)
  have hk := kernel_integrable ζ.law ζ.hasCutoff 0
  have hpoint : ∀ᵐ r ∂ζ.law,
      μ.xi 1 * (1-max 0 r) ≤ μ.xi 1 - μ.xi r := by
    filter_upwards [ζ.hasCutoff.2.2] with r hr
    rw [max_eq_right hr.1]
    linarith [hxi r ⟨hr.1, hr.2.trans ζ.hasCutoff.2.1.le⟩]
  have h := integral_mono_ae (hk.const_mul (μ.xi 1))
    ((integrable_const (μ.xi 1)).sub hiξ) hpoint
  change (∫ r, μ.xi 1 * (1 - max 0 r) ∂ζ.law) ≤
    ∫ r, μ.xi 1 - μ.xi r ∂ζ.law at h
  rw [integral_const_mul, integral_sub (integrable_const _) hiξ,
    integral_const, probReal_univ, one_smul] at h
  change μ.xi 1 * xHat ζ.law 0 ≤ μ.xi 1 - ∫ r, μ.xi r ∂ζ.law at h
  have hscaled := mul_le_mul_of_nonneg_left h hβpos.le
  apply (le_div_iff₀ (μ.xi_pos (by norm_num : 0 < (1 : ℝ)))).mpr
  nlinarith

end SlowEquilibration.SourceLiteratureGroundStateFinal

namespace SlowEquilibration.SourceLiteratureGroundStateFinal.Endpoints

open SlowEquilibration.LiteratureSubagProposition24Proof

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalTAPCertificate
open SourceLiteratureParisi SourceLiteratureGroundStateProof
open SourceLiteratureGroundStateFinal SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion
open SourceReductionConsumerAsymptotic SphericalOrthogonalHaar
open SphericalOverlapExponential SphericalAging.HardSphereDynamics
open scoped Topology NNReal

set_option autoImplicit false
universe u v

/-- The literal endpoint with both Proposition 24 and full ground-profile
recovery discharged. The remaining ground assumption is precisely the
original minimizing-profile compactness statement. -/
theorem finiteMixture_main_condensed_and_initial_literal_reduced2
    (μ : FiniteMixture) {β x Q : ℝ} (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hCompactness : GroundMinimizerLiminfCompactness)
    (h5 : Theorem5 (literatureThermodynamicData hChen
      (chenSenFiniteGround_of_minimizer_compactness hChen hCompactness) μ h.beta_pos.le))
    (h25 : Remark25Contrapositive μ β) :
    ∃ γ : ℝ, 0 < γ ∧
      VaryingConvergesInProbability
        (fun n => disorderLaw (n+2) μ.maxDegree)
        (fun n => originalUniformIntervalDistance μ β
          (exponentialGridHorizon γ (n+2)))
        (fun _ _ => 1) ∧
      uniformSeparationInProbability μ β (fun N => exponentialGridHorizon γ N) ∧
      (∀ ε : ℝ, 0 < ε →
        Tendsto (uniformPrescribedFailure μ β
          (fun N => exponentialGridHorizon γ N) ε) atTop (𝓝 0)) ∧
      (∀ (Ω : ℕ → Type) [∀ N, MeasurableSpace (Ω N)]
          (P : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]
          (J : ∀ N, Ω N → Disorder N μ.maxDegree)
          (ν : ∀ N, Ω N → ProbabilityMeasure (Vector N)),
          (∀ N, HasLaw (J N) (disorderLaw N μ.maxDegree) (P N)) →
          (∀ N, AEMeasurable (ν N) (P N)) →
          (∀ N, IndepFun
            (fun ω => fun x : {x : Vector N // OnSphere x} =>
              field (mixtureCoefficients μ) (J N ω) x) (ν N) (P N)) →
          (∀ N, 1 ≤ N → ∀ᵐ ω ∂P N, ∀ᵐ y ∂(ν N ω).toMeasure, OnSphere y) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => (P N).real
              {ω | intervalDistance μ β (exponentialGridHorizon γ N)
                (J N ω) (ν N ω) < 1-ε}) atTop (𝓝 0)) := by
  exact finiteMixture_main_condensed_and_initial_literal_reduced μ h hChen
    (chenSenFiniteGround_of_minimizer_compactness hChen hCompactness) h5 h25

/-- The universe-polymorphic all-initial conclusion with recovery and
Proposition 24 discharged and the exact compactness statement retained. -/
theorem finiteMixture_all_initial_spherical_of_literature_reduced2
    (μ : FiniteMixture) {β x Q : ℝ} (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hCompactness : GroundMinimizerLiminfCompactness)
    (h5 : Theorem5 (literatureThermodynamicData hChen
      (chenSenFiniteGround_of_minimizer_compactness hChen hCompactness) μ h.beta_pos.le))
    (h25 : Remark25Contrapositive μ β) :
    ∃ γ : ℝ, 0 < γ ∧ SourceMixedCountCapturePackage.SphericalInitialConclusions.{u,v} μ β γ := by
  exact finiteMixture_all_initial_spherical_of_literature_reduced.{u,v} μ h hChen
    (chenSenFiniteGround_of_minimizer_compactness hChen hCompactness) h5 h25

end SlowEquilibration.SourceLiteratureGroundStateFinal.Endpoints

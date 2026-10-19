-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceLiteratureGroundStateFinal
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.Sequences

/-!
# Compactness of the rescaled Crisanti–Sommers minimizing kernels

Chen–Sen, arXiv:1512.08492v2, Section 2.2, extracts rescaled minimizers
and proves strict limiting slack. Here the mass bound gives common local
Lipschitz bounds; Arzelà–Ascoli and a countable product extract one
subsequence on the whole half-open interval. Averaged CS support
stationarity gives a uniform positive terminal-gap bound. The negative
right derivative of the concave limit then constructs the full encoded
ground profile, with its integrability and strict slack proved by FTC.

Composition with the preceding recovery and lower-semicontinuity proofs
discharges the exact extraction hypothesis and derives the Chen–Sen
interface from Chen's finite-mixture Parisi formula alone.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceLiteratureGroundStateExtraction

open MeasureTheory ProbabilityTheory Set Filter CrisantiSommers
open SourceLiteratureGroundState SourceLiteratureGroundStateProof
open SourceLiteratureGroundStateFinal SourceGroundProfileUniqueness
open SourceLiteratureParisi
open scoped Topology NNReal BoundedContinuousFunction

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The uniform bound from the ordinary variational problem. -/
def kernelMassBound (μ : FiniteMixture) : ℝ :=
  ((CSCompactAttainment.mixtureLipschitzConstant μ : ℝ) + 1) / μ.xi 1

theorem kernelMassBound_pos (μ : FiniteMixture) : 0 < kernelMassBound μ := by
  exact div_pos (by positivity) (μ.xi_pos zero_lt_one)

/-- The actual minimizing kernels, at positive integer inverse temperatures. -/
def rescaledKernel (μ : FiniteMixture) (n : ℕ) (t : ℝ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) *
    xHat (CSParisiMeasure.canonicalMinimizer μ ((n + 1 : ℕ) : ℝ)).law t

private theorem xHat_antitone (ζ : Admissible) : Antitone (xHat ζ.law) := by
  intro s t hst
  exact integral_mono (kernel_integrable _ ζ.hasCutoff t)
    (kernel_integrable _ ζ.hasCutoff s)
    (fun a => sub_le_sub_left (max_le_max_right a hst) 1)

/-- The mass bound controls every point of the physical half-open interval. -/
theorem rescaledKernel_bounds (μ : FiniteMixture) (n : ℕ) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) :
    0 < rescaledKernel μ n t ∧ rescaledKernel μ n t ≤ kernelMassBound μ := by
  have hβ : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hβpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  let ζ := CSParisiMeasure.canonicalMinimizer μ ((n + 1 : ℕ) : ℝ)
  refine ⟨mul_pos hβpos (xHat_pos ζ.law ζ.hasCutoff ht.2), ?_⟩
  exact (mul_le_mul_of_nonneg_left (xHat_antitone ζ ht.1) hβpos.le).trans
    (canonicalMinimizer_rescaled_mass_le μ hβ)

private theorem kernel_increment_bound (ζ : Admissible) {s t r : ℝ}
    (_hs : 0 ≤ s) (hst : s ≤ t) (htr : t ≤ r) (hr : r < 1) :
    (xHat ζ.law s - xHat ζ.law t) * (1-r) ≤ (t-s) * xHat ζ.law 0 := by
  have hp : ∀ᵐ a ∂ζ.law,
      ((1-max s a) - (1-max t a)) * (1-r) ≤ (t-s) * (1-max 0 a) := by
    filter_upwards [ζ.hasCutoff.2.2] with a ha
    rw [max_eq_right ha.1]
    rcases le_total a s with has | hsa
    · rw [max_eq_left has, max_eq_left (has.trans hst)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hst)
        (sub_nonneg.mpr (has.trans (hst.trans htr)))]
    · rw [max_eq_right hsa]
      rcases le_total a t with hat | hta
      · rw [max_eq_left hat]
        nlinarith [mul_nonneg (sub_nonneg.mpr hst)
          (sub_nonneg.mpr (hat.trans htr)),
          mul_nonneg (sub_nonneg.mpr hsa) (sub_nonneg.mpr hr.le)]
      · rw [max_eq_right hta]
        have ha1 : a ≤ 1 := ha.2.trans ζ.hasCutoff.2.1.le
        exact by nlinarith [mul_nonneg (sub_nonneg.mpr hst) (sub_nonneg.mpr ha1)]
  have hi := integral_mono_ae
    (((kernel_integrable _ ζ.hasCutoff s).sub
      (kernel_integrable _ ζ.hasCutoff t)).mul_const (1-r))
    ((kernel_integrable _ ζ.hasCutoff 0).const_mul (t-s)) hp
  simp only [Pi.sub_apply] at hi
  rw [integral_mul_const, integral_sub (kernel_integrable _ ζ.hasCutoff s)
    (kernel_integrable _ ζ.hasCutoff t), integral_const_mul] at hi
  exact hi

/-- The bound is uniform in temperature on every compact subinterval.
It replaces the diagonal Helly step for the integrated kernels. -/
theorem rescaledKernel_lipschitzOn (μ : FiniteMixture) (n : ℕ) {r : ℝ}
    (hr : r < 1) :
    LipschitzOnWith ⟨kernelMassBound μ / (1-r),
      div_nonneg (kernelMassBound_pos μ).le (sub_pos.mpr hr).le⟩
      (rescaledKernel μ n) (Icc (0 : ℝ) r) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  wlog hst : s ≤ t generalizing s t
  · simpa only [dist_comm] using this t ht s hs (le_of_not_ge hst)
  let β : ℝ := ((n + 1 : ℕ) : ℝ)
  let ζ := CSParisiMeasure.canonicalMinimizer μ β
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hmono : rescaledKernel μ n t ≤ rescaledKernel μ n s :=
    mul_le_mul_of_nonneg_left (xHat_antitone ζ hst) hβ
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hmono), Real.dist_eq,
    abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
  change β * xHat ζ.law s - β * xHat ζ.law t ≤
    kernelMassBound μ / (1-r) * (t-s)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sub_pos.mpr hr)).mpr
  have hi := mul_le_mul_of_nonneg_left (kernel_increment_bound ζ hs.1 hst ht.2 hr) hβ
  have hm : β * xHat ζ.law 0 ≤ kernelMassBound μ :=
    (rescaledKernel_bounds μ n ⟨le_rfl, zero_lt_one⟩).2
  have hb := mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr hst)
  nlinarith [hi, hb]

private theorem local_lipschitz_subsequence
    (f : ℕ → ℝ → ℝ) (r : ℕ → ℝ) (C : ℝ) (K : ℕ → ℝ≥0)
    (hbound : ∀ n m t, t ∈ Icc (0 : ℝ) (r m) → f n t ∈ Icc 0 C)
    (hlip : ∀ n m, LipschitzOnWith (K m) (f n) (Icc (0 : ℝ) (r m)))
    (hcover : ∀ t ∈ Ico (0 : ℝ) 1, ∃ m, t ∈ Icc (0 : ℝ) (r m)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ t ∈ Ico (0 : ℝ) 1,
      ∃ l : ℝ, Tendsto (fun n => f (φ n) t) atTop (𝓝 l) := by
  let B (n m : ℕ) : Icc (0 : ℝ) (r m) →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨fun t => f n t, (hlip n m).to_restrict.continuous⟩
  let S (m : ℕ) : Set (Icc (0 : ℝ) (r m) →ᵇ ℝ) :=
    closure (range (fun n => B n m))
  have hS (m : ℕ) : IsCompact (S m) := by
    apply BoundedContinuousFunction.arzela_ascoli (Icc (0 : ℝ) C) isCompact_Icc
    · rintro g t ⟨n, rfl⟩
      exact hbound n m t t.property
    · apply Metric.equicontinuous_of_continuity_modulus (fun d => (K m : ℝ) * d)
      · simpa only [mul_zero] using (tendsto_const_nhds.mul tendsto_id :
          Tendsto (fun d : ℝ => (K m : ℝ) * d) (𝓝 0) (𝓝 ((K m : ℝ) * 0)))
      · rintro x y ⟨g, hg⟩
        obtain ⟨n, rfl⟩ := hg
        exact ((hlip n m).to_restrict).dist_le_mul x y
  let (m : ℕ) : CompactSpace (S m) := isCompact_iff_compactSpace.mp (hS m)
  let F (n : ℕ) : ∀ m, S m := fun m => ⟨B n m, subset_closure ⟨n, rfl⟩⟩
  obtain ⟨G, φ, hφ, hG⟩ := CompactSpace.tendsto_subseq F
  refine ⟨φ, hφ, ?_⟩
  intro t ht
  obtain ⟨m, hm⟩ := hcover t ht
  let z : Icc (0 : ℝ) (r m) := ⟨t, hm⟩
  refine ⟨(G m).val z, ?_⟩
  have hcoord := ((continuous_apply m).tendsto G).comp hG
  have heval := (((BoundedContinuousFunction.lipschitz_eval_const z).continuous.comp
    continuous_subtype_val).tendsto (G m)).comp hcoord
  exact heval

private def exhaustion (m : ℕ) : ℝ := 1 - ((m : ℝ) + 2)⁻¹

private theorem exhaustion_lt_one (m : ℕ) : exhaustion m < 1 := by
  dsimp [exhaustion]
  have h : 0 < (m : ℝ) + 2 := by positivity
  linarith [inv_pos.mpr h]

private theorem exhaustion_cover {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    ∃ m, t ∈ Icc (0 : ℝ) (exhaustion m) := by
  obtain ⟨m, hm⟩ := exists_nat_gt ((1-t)⁻¹)
  refine ⟨m, ht.1, ?_⟩
  have hd : 0 < (m : ℝ) + 2 := by positivity
  have hi : ((m : ℝ) + 2)⁻¹ ≤ 1-t := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hd).mpr
    have hprod : (1-t) * (1-t)⁻¹ = 1 := mul_inv_cancel₀ (sub_pos.mpr ht.2).ne'
    nlinarith [mul_lt_mul_of_pos_left hm (sub_pos.mpr ht.2)]
  dsimp [exhaustion]
  linarith

/-- A single subsequence converges at every real point below one.
This compactness assertion has no analytic or literature hypothesis. -/
theorem exists_rescaledKernel_pointwise_limit (μ : FiniteMixture) :
    ∃ f : ℝ → ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ t ∈ Ico (0 : ℝ) 1,
        Tendsto (fun n => rescaledKernel μ (φ n) t) atTop (𝓝 (f t)) := by
  let K (m : ℕ) : ℝ≥0 := ⟨kernelMassBound μ / (1-exhaustion m),
    div_nonneg (kernelMassBound_pos μ).le (sub_pos.mpr (exhaustion_lt_one m)).le⟩
  obtain ⟨φ, hφ, hlim⟩ := local_lipschitz_subsequence (rescaledKernel μ) exhaustion
    (kernelMassBound μ) K
    (fun n m t ht =>
      let h := rescaledKernel_bounds μ n ⟨ht.1, ht.2.trans_lt (exhaustion_lt_one m)⟩
      ⟨h.1.le, h.2⟩)
    (fun n m => rescaledKernel_lipschitzOn μ n (exhaustion_lt_one m))
    (fun _ ht => exhaustion_cover ht)
  classical
  let f : ℝ → ℝ := fun t => if ht : t ∈ Ico (0 : ℝ) 1 then
    Classical.choose (hlim t ht) else 0
  refine ⟨f, φ, hφ, ?_⟩
  intro t ht
  simpa only [f, dite_eq_left ht] using Classical.choose_spec (hlim t ht)

/-- Every pointwise cluster limit inherits the uniform mass bounds,
monotonicity, concavity, and local Lipschitz regularity. -/
theorem rescaledKernel_limit_properties (μ : FiniteMixture) (f : ℝ → ℝ)
    (φ : ℕ → ℕ)
    (hlim : ∀ t ∈ Ico (0 : ℝ) 1,
      Tendsto (fun n => rescaledKernel μ (φ n) t) atTop (𝓝 (f t))) :
    (∀ t ∈ Ico (0 : ℝ) 1, f t ∈ Icc 0 (kernelMassBound μ)) ∧
    AntitoneOn f (Ico (0 : ℝ) 1) ∧ ConcaveOn ℝ (Ico (0 : ℝ) 1) f ∧
    (∀ (r : ℝ) (hr : r < 1), LipschitzOnWith ⟨kernelMassBound μ / (1-r),
      div_nonneg (kernelMassBound_pos μ).le (sub_pos.mpr hr).le⟩ f (Icc 0 r)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨le_of_tendsto_of_tendsto' tendsto_const_nhds (hlim t ht)
        (fun n => (rescaledKernel_bounds μ (φ n) ht).1.le),
      le_of_tendsto' (hlim t ht) (fun n => (rescaledKernel_bounds μ (φ n) ht).2)⟩
  · intro s hs t ht hst
    apply le_of_tendsto_of_tendsto' (hlim t ht) (hlim s hs)
    intro n
    exact mul_le_mul_of_nonneg_left
      (xHat_antitone (CSParisiMeasure.canonicalMinimizer μ ((φ n + 1 : ℕ) : ℝ)) hst)
      (by positivity)
  · refine ⟨convex_Ico 0 1, ?_⟩
    intro s hs t ht a b ha hb hab
    have hx : a • s + b • t ∈ Ico (0 : ℝ) 1 := (convex_Ico 0 1) hs ht ha hb hab
    apply le_of_tendsto_of_tendsto'
      (((hlim s hs).const_mul a).add ((hlim t ht).const_mul b)) (hlim _ hx)
    intro n
    have hc := (xHat_concave
      (CSParisiMeasure.canonicalMinimizer μ ((φ n + 1 : ℕ) : ℝ)).law
      (CSParisiMeasure.canonicalMinimizer μ ((φ n + 1 : ℕ) : ℝ)).hasCutoff).2
        (mem_univ s) (mem_univ t) ha hb hab
    have hh := mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ ((φ n + 1 : ℕ) : ℝ))
    dsimp only [rescaledKernel, smul_eq_mul] at *
    nlinarith
  · intro r hr
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    exact le_of_tendsto' ((hlim s ⟨hs.1, hs.2.trans_lt hr⟩).dist
      (hlim t ⟨ht.1, ht.2.trans_lt hr⟩))
      (fun n => (rescaledKernel_lipschitzOn μ (φ n) hr).dist_le_mul s hs t ht)

/-- A genuine last support point can be used as the entropy cutoff. -/
theorem exists_max_support_cutoff (ζ : Admissible) :
    ∃ q ∈ ζ.law.support, HasCutoff ζ.law q ∧
      ∀ s ∈ ζ.law.support, s ≤ q := by
  have hsub := CSStructure.support_subset_cutoff ζ.law ζ.hasCutoff
  have hcompact : IsCompact ζ.law.support :=
    isCompact_Icc.of_isClosed_subset ζ.law.isClosed_support hsub
  have hnonempty : ζ.law.support.Nonempty :=
    ζ.law.nonempty_support (IsProbabilityMeasure.ne_zero ζ.law)
  obtain ⟨q, hq, hmax⟩ :=
    hcompact.exists_isMaxOn hnonempty continuous_id.continuousOn
  refine ⟨q, hq, ?_, hmax⟩
  have hqr := hsub hq
  refine ⟨hqr.1, hqr.2.trans_lt ζ.hasCutoff.2.1, ?_⟩
  filter_upwards [ζ.hasCutoff.2.2, ζ.law.support_mem_ae] with s hs hsupp
  exact ⟨hs.1, hmax hsupp⟩

/-- Stationarity at every support point, including the possible atom at
zero. This uses the ordinary CS minimizer criterion only. -/
theorem support_stationarity (μ : FiniteMixture) (β : ℝ) (ζ : Admissible)
    (hmin : ζ.IsMinimizer β μ.xi) {s : ℝ} (hs : s ∈ ζ.law.support) :
    β ^ 2 * μ.xi1 s = ∫ t in (0 : ℝ)..s, 1 / (xHat ζ.law t) ^ 2 := by
  have hsr := CSStructure.support_subset_cutoff ζ.law ζ.hasCutoff hs
  by_cases hs0 : s = 0
  · subst s
    rw [CSTAPTelescope.xi1_zero, intervalIntegral.integral_same]
    ring
  have hspos : 0 < s := lt_of_le_of_ne hsr.1 (Ne.symm hs0)
  have hs1 : s < 1 := hsr.2.trans_lt ζ.hasCutoff.2.1
  have hξcont : ContinuousOn μ.xi (Ico (0 : ℝ) 1) :=
    fun r _ => (μ.hasDerivAt_xi r).continuousAt.continuousWithinAt
  obtain ⟨m, hmax, hsupport⟩ :=
    (ζ.minimizer_iff_support_on_maximum β μ.xi hξcont).mp hmin
  have hfc : ContinuousOn (firstVariation β μ.xi ζ.law) (Icc 0 ζ.cutoff) := by
    intro r hr
    exact (firstVariation_hasDerivAt β μ.xi ζ.law ζ.hasCutoff
      (hr.2.trans_lt ζ.hasCutoff.2.1) (μ.hasDerivAt_xi r)).continuousAt.continuousWithinAt
  have hfs : firstVariation β μ.xi ζ.law s = m :=
    CSStructure.eq_on_support_of_ae_eq ζ.law ζ.hasCutoff hfc hsupport hs
  have hlocal : IsLocalMax (firstVariation β μ.xi ζ.law) s := by
    filter_upwards [Ioo_mem_nhds hspos hs1] with r hr
    rw [hfs]
    exact hmax r ⟨hr.1.le, hr.2⟩
  have hstationary := hlocal.deriv_eq_zero
  rw [firstVariation_deriv β μ.xi ζ.law ζ.hasCutoff hs1
    (μ.hasDerivAt_xi s).differentiableAt, (μ.hasDerivAt_xi s).deriv] at hstationary
  exact sub_eq_zero.mp hstationary

/-- Reciprocal FTC with the full distribution function, including atoms.
This is one of the two identities needed for strict terminal slack. -/
theorem integral_cdf_div_xHat_sq (ζ : Admissible) {q : ℝ}
    (hq : HasCutoff ζ.law q) :
    (∫ t in (0 : ℝ)..q, cdf ζ.law t / (xHat ζ.law t)^2) =
      (1-q)⁻¹ - (xHat ζ.law 0)⁻¹ := by
  have hci : ContinuousOn (fun t => ((xHat ζ.law t)^2)⁻¹) (Icc 0 q) :=
    ((xHat_continuous ζ.law hq).continuousOn.pow 2).inv₀
      (fun t ht => pow_ne_zero 2 (xHat_pos ζ.law hq (ht.2.trans_lt hq.2.1)).ne')
  have hint : IntervalIntegrable
      (fun t => cdf ζ.law t / (xHat ζ.law t)^2) volume 0 q := by
    simpa only [div_eq_mul_inv] using
      (monotone_cdf ζ.law).intervalIntegrable.mul_continuousOn
        (by simpa only [uIcc_of_le hq.1] using hci)
  have heq := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hq.1
    ((xHat_continuous ζ.law hq).continuousOn.inv₀
      (fun t ht => (xHat_pos ζ.law hq (ht.2.trans_lt hq.2.1)).ne'))
    (fun t ht => by
      simpa only [Pi.inv_apply, neg_neg, cdf_eq_real] using
        ((xHat_hasRightDerivative ζ.law hq t).inv
          (xHat_pos ζ.law hq (ht.2.trans hq.2.1)).ne').Ioi_of_Ici) hint
  simp only [Pi.inv_apply] at heq
  rwa [xHat_tail ζ.law hq le_rfl] at heq

private theorem averaged_support_stationarity
    (μ : FiniteMixture) (β : ℝ) (ζ : Admissible)
    (hmin : ζ.IsMinimizer β μ.xi) {q : ℝ}
    (hq : HasCutoff ζ.law q) (hqs : q ∈ ζ.law.support) :
    (∫ t in (0 : ℝ)..q, cdf ζ.law t / (xHat ζ.law t)^2) =
      β^2 * (μ.xi1 q - ∫ s, μ.xi1 s ∂ζ.law) := by
  let A : ℝ → ℝ := fun t => 1 / (xHat ζ.law t)^2
  let F : ℝ → ℝ → ℝ := fun t s => if s ≤ t then A t else 0
  have hAc : ContinuousOn A (Icc 0 q) :=
    continuousOn_const.div ((xHat_continuous ζ.law hq).continuousOn.pow 2)
      (fun t ht => pow_ne_zero 2 (xHat_pos ζ.law hq (ht.2.trans_lt hq.2.1)).ne')
  have hAi : IntervalIntegrable A volume 0 q := hAc.intervalIntegrable_of_Icc hq.1
  have hAm : Measurable A :=
    measurable_const.div ((xHat_continuous ζ.law hq).measurable.pow_const 2)
  have hFm : Measurable (Function.uncurry F) :=
    Measurable.ite (measurableSet_le measurable_snd measurable_fst)
      (hAm.comp measurable_fst) measurable_const
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hAc
  have hFi : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc (0 : ℝ) q)).prod ζ.law) := by
    apply (integrable_const (max C 0)).mono' hFm.aestronglyMeasurable
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hFm.norm measurable_const)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact .of_forall fun s => by
      dsimp only [Function.uncurry_def, F]
      split_ifs
      · exact (hC t ⟨ht.1.le, ht.2⟩).trans (le_max_left _ _)
      · simp only [norm_zero]
        exact le_max_right C (0 : ℝ)
  rw [← uIoc_of_le hq.1] at hFi
  have hprimitive (s : ℝ) (hs : s ∈ Icc (0 : ℝ) q) :
      (∫ t in (0 : ℝ)..q, F t s) =
        (∫ t in (0 : ℝ)..q, A t) - (∫ t in (0 : ℝ)..s, A t) := by
    have hBi : IntervalIntegrable ((Iic s).indicator A) volume 0 q :=
      ⟨hAi.1.indicator measurableSet_Iic, hAi.2.indicator measurableSet_Iic⟩
    calc
      _ = ∫ t in (0 : ℝ)..q, A t - (Iic s).indicator A t := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [volume.ae_ne s] with t hts _
        by_cases hst : s ≤ t
        · have hlt : s < t := lt_of_le_of_ne hst (Ne.symm hts)
          simp [F, hst, not_le.mpr hlt]
        · simp [F, hst, le_of_not_ge hst]
      _ = (∫ t in (0 : ℝ)..q, A t) -
          (∫ t in (0 : ℝ)..q, (Iic s).indicator A t) :=
        intervalIntegral.integral_sub hAi hBi
      _ = _ := congrArg (fun z => (∫ t in (0 : ℝ)..q, A t) - z)
        (intervalIntegral.integral_indicator (f := A) hs)
  have hinner (t : ℝ) : (∫ s, F t s ∂ζ.law) = ζ.law.real (Iic t) * A t := by
    change (∫ s, (Iic t).indicator (fun _ => A t) s ∂ζ.law) = _
    rw [integral_indicator measurableSet_Iic]
    simp [smul_eq_mul]
  have hξ : Integrable μ.xi1 ζ.law :=
    CSStability.integrable_of_cutoff ζ.law hq
      (fun s _ => (μ.hasDerivAt_xi1 s).continuousAt.continuousWithinAt)
  have hright : (∫ s, (∫ t in (0 : ℝ)..q, F t s) ∂ζ.law) =
      β^2 * (μ.xi1 q - ∫ s, μ.xi1 s ∂ζ.law) := by
    calc
      _ = ∫ s, β^2 * (μ.xi1 q - μ.xi1 s) ∂ζ.law := by
        apply integral_congr_ae
        filter_upwards [hq.2.2, ζ.law.support_mem_ae] with s hs hsupp
        rw [hprimitive s hs]
        change (∫ t in (0 : ℝ)..q, 1/(xHat ζ.law t)^2) -
          (∫ t in (0 : ℝ)..s, 1/(xHat ζ.law t)^2) = _
        rw [← support_stationarity μ β ζ hmin hqs,
          ← support_stationarity μ β ζ hmin hsupp]
        ring
      _ = _ := by
        rw [integral_const_mul, integral_sub (integrable_const _) hξ]
        simp
  have hswap := intervalIntegral_integral_swap (f := F) (a := 0) (b := q)
    (μ := ζ.law) hFi
  simp only [hinner] at hswap
  rw [hright] at hswap
  simpa only [A, cdf_eq_real, div_eq_mul_inv, mul_one, one_mul] using hswap

/-- Averaging CS support stationarity gives the reciprocal terminal-gap
identity used in the strict-slack argument, without an auxiliary Parisi
parameter or a second literature assumption. -/
theorem terminal_gap_identity (μ : FiniteMixture) (β : ℝ) (ζ : Admissible)
    (hmin : ζ.IsMinimizer β μ.xi) {q : ℝ}
    (hq : HasCutoff ζ.law q) (hqs : q ∈ ζ.law.support) :
    (1-q)⁻¹ = (xHat ζ.law 0)⁻¹ +
      β^2 * (μ.xi1 q - ∫ s, μ.xi1 s ∂ζ.law) := by
  have h := averaged_support_stationarity μ β ζ hmin hq hqs
  rw [integral_cdf_div_xHat_sq ζ hq] at h
  linarith

private theorem xi2_bounds (μ : FiniteMixture) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ μ.xi2 t ∧ μ.xi2 t ≤ μ.xi2 1 := by
  constructor
  · unfold FiniteMixture.xi2
    exact Finset.sum_nonneg fun p hp =>
      mul_nonneg (μ.curvatureCoeff_pos hp).le (pow_nonneg ht.1 _)
  · unfold FiniteMixture.xi2
    apply Finset.sum_le_sum
    intro p hp
    simpa only [one_pow, mul_one] using
      mul_le_mul_of_nonneg_left (pow_le_one₀ ht.1 ht.2 : t^(p-2) ≤ 1)
        (μ.curvatureCoeff_pos hp).le

private theorem xi1_increment_le (μ : FiniteMixture) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) :
    μ.xi1 t - μ.xi1 s ≤ μ.xi2 1 * (t-s) := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ Icc (0 : ℝ) 1) => (μ.hasDerivAt_xi1 x).hasDerivWithinAt)
    (fun x (hx : x ∈ Icc (0 : ℝ) 1) => by
      rw [Real.norm_eq_abs, abs_of_nonneg (xi2_bounds μ hx).1]
      exact (xi2_bounds μ hx).2)
    (convex_Icc (0 : ℝ) 1) hs ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hst)] at hh
  exact (le_abs_self _).trans hh

private theorem minimizer_inverse_mass_le_sqrt (μ : FiniteMixture) {β : ℝ}
    (hβ : 0 < β) (ζ : Admissible) (hmin : ζ.IsMinimizer β μ.xi)
    {q : ℝ} (hq : q ∈ ζ.law.support) (hqpos : 0 < q) :
    1 / (β * xHat ζ.law 0) ≤ Real.sqrt (μ.xi2 1) := by
  have hqr := CSStructure.support_subset_cutoff ζ.law ζ.hasCutoff hq
  have hq1 : q < 1 := hqr.2.trans_lt ζ.hasCutoff.2.1
  have hf0 : 0 < xHat ζ.law 0 := xHat_pos ζ.law ζ.hasCutoff zero_lt_one
  have hi : IntervalIntegrable (fun t => 1 / (xHat ζ.law t)^2) volume 0 q := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div ((xHat_continuous ζ.law ζ.hasCutoff).continuousOn.pow 2)
    intro t ht
    rw [uIcc_of_le hqpos.le] at ht
    exact pow_ne_zero 2 (xHat_pos ζ.law ζ.hasCutoff (ht.2.trans_lt hq1)).ne'
  have hI := intervalIntegral.integral_mono_on hqpos.le
    (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => 1 / (xHat ζ.law 0)^2) volume 0 q)
    hi (fun t ht =>
      one_div_le_one_div_of_le
        (sq_pos_of_pos (xHat_pos ζ.law ζ.hasCutoff (ht.2.trans_lt hq1)))
        (pow_le_pow_left₀ (xHat_pos ζ.law ζ.hasCutoff (ht.2.trans_lt hq1)).le
          (xHat_antitone ζ ht.1) 2))
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hI
  rw [← support_stationarity μ β ζ hmin hq] at hI
  have hxi : μ.xi1 q ≤ μ.xi2 1 * q := by
    simpa only [CSTAPTelescope.xi1_zero, sub_zero] using
      xi1_increment_le μ ⟨le_rfl, zero_le_one⟩ ⟨hqpos.le, hq1.le⟩ hqpos.le
  have hI' : q / (xHat ζ.law 0)^2 ≤ β^2 * μ.xi1 q := by
    simpa only [div_eq_mul_inv, one_mul] using hI
  have hbound : q / (xHat ζ.law 0)^2 ≤ β^2 * (μ.xi2 1 * q) :=
    hI'.trans (mul_le_mul_of_nonneg_left hxi (sq_nonneg β))
  have hscaled := (div_le_iff₀ (sq_pos_of_pos hf0)).mp hbound
  have hsq : 1 ≤ μ.xi2 1 * (β * xHat ζ.law 0)^2 := by
    apply (mul_le_mul_iff_right₀ hqpos).mp
    nlinarith only [hscaled]
  have hrootSq : 1 ≤ (Real.sqrt (μ.xi2 1) * (β * xHat ζ.law 0))^2 := by
    rw [mul_pow, Real.sq_sqrt (μ.xi2_pos zero_lt_one).le]
    exact hsq
  have hmpos := mul_pos hβ hf0
  have hrootM := (one_le_sq_iff₀
    (mul_nonneg (Real.sqrt_nonneg (μ.xi2 1)) hmpos.le)).mp hrootSq
  exact (div_le_iff₀ hmpos).mpr hrootM

/-- The strictly positive terminal-gap bound, uniform in inverse
temperature at least one. The last support point is essential here. -/
theorem canonicalMinimizer_terminal_gap_lower (μ : FiniteMixture) {β q : ℝ}
    (hβ : 1 ≤ β)
    (hq : HasCutoff (CSParisiMeasure.canonicalMinimizer μ β).law q)
    (hqs : q ∈ (CSParisiMeasure.canonicalMinimizer μ β).law.support) :
    1 / (1 + Real.sqrt (μ.xi2 1) + μ.xi2 1 * kernelMassBound μ) ≤ β * (1-q) := by
  let ζ := CSParisiMeasure.canonicalMinimizer μ β
  let D := 1 + Real.sqrt (μ.xi2 1) + μ.xi2 1 * kernelMassBound μ
  have hβpos : 0 < β := by linarith
  have hK : 0 < μ.xi2 1 := μ.xi2_pos zero_lt_one
  have hD1 : 1 ≤ D := by
    dsimp [D]
    linarith [Real.sqrt_nonneg (μ.xi2 1),
      mul_nonneg hK.le (kernelMassBound_pos μ).le]
  have hD : 0 < D := zero_lt_one.trans_le hD1
  change 1 / D ≤ β * (1-q)
  by_cases hq0 : q = 0
  · subst q
    simp only [sub_zero, mul_one]
    exact (one_div_le_one_div_of_le zero_lt_one hD1).trans (by simpa using hβ)
  have hqpos : 0 < q := lt_of_le_of_ne hq.1 (Ne.symm hq0)
  have hf0 : 0 < xHat ζ.law 0 := xHat_pos ζ.law hq zero_lt_one
  have hInv := minimizer_inverse_mass_le_sqrt μ hβpos ζ
    (CSParisiMeasure.canonicalMinimizer_isMinimizer μ β) hqs hqpos
  have hInv0 : (xHat ζ.law 0)⁻¹ ≤ β * Real.sqrt (μ.xi2 1) := by
    have hh := mul_le_mul_of_nonneg_left hInv hβpos.le
    convert hh using 1
    field_simp [hβpos.ne', hf0.ne']
  have hξ : Integrable μ.xi1 ζ.law :=
    CSStability.integrable_of_cutoff ζ.law hq
      (fun s _ => (μ.hasDerivAt_xi1 s).continuousAt.continuousWithinAt)
  have hdiff : μ.xi1 q - (∫ s, μ.xi1 s ∂ζ.law) ≤
      μ.xi2 1 * xHat ζ.law 0 := by
    have hi := integral_mono_ae ((integrable_const (μ.xi1 q)).sub hξ)
      ((kernel_integrable ζ.law hq 0).const_mul (μ.xi2 1))
      (hq.2.2.mono fun s hs => by
        dsimp only [Pi.sub_apply]
        rw [max_eq_right hs.1]
        exact (xi1_increment_le μ ⟨hs.1, hs.2.trans hq.2.1.le⟩
          ⟨hq.1, hq.2.1.le⟩ hs.2).trans
            (mul_le_mul_of_nonneg_left (sub_le_sub_right hq.2.1.le s) hK.le))
    simp only [Pi.sub_apply] at hi
    rw [integral_sub (integrable_const _) hξ, integral_const_mul] at hi
    simpa only [integral_const, probReal_univ, one_smul, xHat] using hi
  have hm : β * xHat ζ.law 0 ≤ kernelMassBound μ :=
    canonicalMinimizer_rescaled_mass_le μ hβ
  have hE : β^2 * (μ.xi1 q - ∫ s, μ.xi1 s ∂ζ.law) ≤
      β * μ.xi2 1 * kernelMassBound μ := by
    have hi := mul_le_mul_of_nonneg_left hdiff (sq_nonneg β)
    have hh := mul_le_mul_of_nonneg_left hm (mul_nonneg hβpos.le hK.le)
    nlinarith only [hi, hh]
  have hid := terminal_gap_identity μ β ζ
    (CSParisiMeasure.canonicalMinimizer_isMinimizer μ β) hq hqs
  have hupper : (1-q)⁻¹ ≤ β * D := by
    dsimp [D]
    nlinarith only [hid, hE, hInv0, hβpos]
  have hprod := mul_le_mul_of_nonneg_right hupper (sub_pos.mpr hq.2.1).le
  rw [inv_mul_cancel₀ (sub_pos.mpr hq.2.1).ne'] at hprod
  apply (div_le_iff₀ hD).mpr
  nlinarith only [hprod]

/-- Strict limiting slack: every pointwise cluster limit is bounded away
from zero by the same positive constant, all the way up to one. -/
theorem rescaledKernel_limit_uniform_lower (μ : FiniteMixture) (f : ℝ → ℝ)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : ∀ t ∈ Ico (0 : ℝ) 1,
      Tendsto (fun n => rescaledKernel μ (φ n) t) atTop (𝓝 (f t))) :
    ∀ t ∈ Ico (0 : ℝ) 1,
      1 / (1 + Real.sqrt (μ.xi2 1) + μ.xi2 1 * kernelMassBound μ) ≤ f t := by
  intro t ht
  let c : ℝ := 1 / (1 + Real.sqrt (μ.xi2 1) + μ.xi2 1 * kernelMassBound μ)
  change c ≤ f t
  have hβLim : Tendsto (fun n => ((φ n + 1 : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).comp hφ.tendsto_atTop
  have hlarge : ∀ᶠ n in atTop, c ≤ ((φ n + 1 : ℕ) : ℝ) * (1-t) :=
    (hβLim.atTop_mul_const (sub_pos.mpr ht.2)).eventually (eventually_ge_atTop c)
  apply ge_of_tendsto (hlim t ht)
  filter_upwards [hlarge] with n hn
  let β : ℝ := ((φ n + 1 : ℕ) : ℝ)
  let ζ := CSParisiMeasure.canonicalMinimizer μ β
  have hβone : 1 ≤ β := by
    dsimp [β]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (φ n))
  have hβnonneg : 0 ≤ β := by dsimp [β]; positivity
  obtain ⟨q, hqs, hq, _⟩ := exists_max_support_cutoff ζ
  change c ≤ β * xHat ζ.law t
  by_cases htq : t ≤ q
  · have hgap : c ≤ β * (1-q) :=
      canonicalMinimizer_terminal_gap_lower μ hβone hq hqs
    exact hgap.trans (mul_le_mul_of_nonneg_left
      (xHat_ge_one_sub_cutoff ζ.law hq htq) hβnonneg)
  · rw [xHat_tail ζ.law hq (le_of_not_ge htq)]
    exact hn

private theorem convex_rightDerivative_rightContinuous (g : ℝ → ℝ)
    (hg : ConvexOn ℝ (Iio 1) g) {x : ℝ} (hx : x < 1) :
    ContinuousWithinAt (fun z => derivWithin g (Ioi z) z) (Ici x) x := by
  let D : ℝ → ℝ := fun z => derivWithin g (Ioi z) z
  have hd (z : ℝ) (hz : z < 1) : HasDerivWithinAt g (D z) (Ioi z) z :=
    hg.hasDerivWithinAt_rightDeriv_of_mem_interior (by simpa using hz)
  have hm : MonotoneOn D (Iio 1) := by
    simpa only [interior_Iio] using hg.monotoneOn_rightDeriv
  have hc : ContinuousAt g x :=
    (hg.continuousOn isOpen_Iio x hx).continuousAt (Iio_mem_nhds hx)
  have hr : ContinuousWithinAt D (Ioi x) x := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      filter_upwards [Ioo_mem_nhdsGT hx] with z hz
      exact ha.trans_le (hm hx hz.2 hz.1.le)
    · intro b hb
      have hs : Tendsto (slope g x) (𝓝[>] x) (𝓝 (D x)) :=
        (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp (hd x hx)
      obtain ⟨y, hy, hsy⟩ :=
        ((show ∀ᶠ y in 𝓝[>] x, y ∈ Ioo x 1 from Ioo_mem_nhdsGT hx).and
          (hs (Iio_mem_nhds hb))).exists
      have hsc : ContinuousAt (fun z => slope g z y) x := by
        simp only [slope_def_field]
        exact (continuousAt_const.sub hc).div
          (continuousAt_const.sub continuousAt_id) (sub_ne_zero.mpr hy.1.ne')
      have hslope : ∀ᶠ z in 𝓝 x, slope g z y < b := hsc (Iio_mem_nhds hsy)
      filter_upwards [hslope.filter_mono nhdsWithin_le_nhds,
        Ioo_mem_nhdsGT hy.1] with z hz hzy
      exact (hg.rightDeriv_le_slope_of_mem_interior
        (by simpa using hzy.2.trans hy.2) hy.2 hzy.2).trans_lt hz
  have hset : Ici x = insert x (Ioi x) := by
    ext z
    simp only [mem_Ici, mem_insert_iff, mem_Ioi]
    grind
  rw [hset]
  exact hr.insert

private theorem groundProfile_of_concave_kernel (f : ℝ → ℝ) {d : ℝ}
    (hdpos : 0 < d) (hlower : ∀ t < 1, d ≤ f t)
    (hanti : AntitoneOn f (Iio 1)) (hconc : ConcaveOn ℝ (Iio 1) f) :
    ∃ u : GroundProfile, ∀ t ∈ Ico (0 : ℝ) 1, profile u t = f t := by
  classical
  let c : ℝ := sInf (f '' Iio (1 : ℝ))
  have hne : (f '' Iio (1 : ℝ)).Nonempty := ⟨f 0, 0, zero_lt_one, rfl⟩
  have hbb : BddBelow (f '' Iio (1 : ℝ)) := by
    refine ⟨d, ?_⟩
    rintro y ⟨t, ht, rfl⟩
    exact hlower t ht
  have hcpos : 0 < c := hdpos.trans_le (le_csInf hne (by
    rintro y ⟨t, ht, rfl⟩
    exact hlower t ht))
  have hlim : Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 c) := hanti.tendsto_nhdsLT hbb
  let G : ℝ → ℝ := fun t => if t < 1 then -f t else -c
  have hGeq (t : ℝ) (ht : t < 1) : G t = -f t := by simp [G, ht]
  have hG0 : G 0 = -f 0 := hGeq 0 zero_lt_one
  have hG1 : G 1 = -c := by simp [G]
  have hGc : ConvexOn ℝ (Iio 1) G := hconc.neg.congr (by
    intro t ht
    change -f t = G t
    exact (hGeq t ht).symm)
  have hGmono : MonotoneOn G (Iio 1) := by
    intro s hs t ht hst
    rw [hGeq s hs, hGeq t ht]
    exact neg_le_neg (hanti hs ht hst)
  have hGlim : Tendsto G (𝓝[<] (1 : ℝ)) (𝓝 (-c)) := by
    apply hlim.neg.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hGeq t ht).symm
  have hGcont1 : ContinuousWithinAt G (Iic 1) 1 := by
    have hleft : ContinuousWithinAt G (Iio 1) 1 := by
      change Tendsto G (𝓝[<] (1 : ℝ)) (𝓝 (G 1))
      simpa only [hG1] using hGlim
    have hset : Iic (1 : ℝ) = insert 1 (Iio 1) := by
      ext t
      simp only [mem_Iic, mem_insert_iff, mem_Iio]
      grind
    rw [hset]
    exact hleft.insert
  have hGcont : ContinuousOn G (Icc (0 : ℝ) 1) := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with ht1 | rfl
    · exact ((hGc.continuousOn isOpen_Iio t ht1).continuousAt
        (Iio_mem_nhds ht1)).continuousWithinAt
    · exact hGcont1.mono (fun _ hs => hs.2)
  let D : ℝ → ℝ := fun t => derivWithin G (Ioi t) t
  have hderiv (t : ℝ) (ht : t < 1) : HasDerivWithinAt G (D t) (Ioi t) t :=
    hGc.hasDerivWithinAt_rightDeriv_of_mem_interior (by simpa using ht)
  have hDmono : MonotoneOn D (Iio 1) := by
    simpa only [interior_Iio] using hGc.monotoneOn_rightDeriv
  have hDpos (t : ℝ) (ht : t < 1) : 0 ≤ D t := by
    apply ge_of_tendsto
      ((hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp (hderiv t ht))
    filter_upwards [Ioo_mem_nhdsGT ht] with y hy
    exact hGmono.slope_nonneg ht hy.2
  have hInt : IntervalIntegrable D volume (0 : ℝ) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
      (intervalIntegral.integrableOn_deriv_right_of_nonneg hGcont
        (fun t ht => hderiv t ht.2) (fun t ht => hDpos t ht.2))
  have hTotal := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    zero_le_one hGcont (fun t ht => hderiv t ht.2) hInt
  let u : GroundProfile := {
    L := f 0
    alpha := D
    alpha_nonnegative := fun t ht => hDpos t ht.2
    alpha_monotone := hDmono.mono (fun _ ht => ht.2)
    alpha_rightContinuous := fun t ht =>
      convex_rightDerivative_rightContinuous G hGc ht.2
    alpha_integrable := hInt
    height_gt_mass := by
      change (∫ t in (0 : ℝ)..1, D t) < f 0
      rw [hTotal, hG1, hG0]
      linarith }
  refine ⟨u, ?_⟩
  intro t ht
  change f 0 - (∫ s in (0 : ℝ)..t, D s) = f t
  have hIntt : IntervalIntegrable D volume (0 : ℝ) t := hInt.mono_set (by
    rw [uIcc_of_le ht.1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl ht.2.le)
  have hFt := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
    (hGcont.mono (Icc_subset_Icc le_rfl ht.2.le))
    (fun s hs => hderiv s (hs.2.trans ht.2)) hIntt
  rw [hFt, hGeq t ht.2, hG0]
  ring

private theorem rescaledKernel_max_zero (μ : FiniteMixture) (n : ℕ) (t : ℝ) :
    rescaledKernel μ n (max t 0) = rescaledKernel μ n t := by
  unfold rescaledKernel xHat
  congr 1
  apply integral_congr_ae
  filter_upwards [(CSParisiMeasure.canonicalMinimizer μ ((n+1 : ℕ) : ℝ)).hasCutoff.2.2]
    with s hs
  rw [max_assoc, max_eq_right hs.1]

/-- Every actual pointwise cluster limit has the full encoded admissible
profile representation. The terminal-gap estimate supplies strict slack. -/
theorem rescaledKernel_limit_admissible (μ : FiniteMixture) (f : ℝ → ℝ)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : ∀ t ∈ Ico (0 : ℝ) 1,
      Tendsto (fun n => rescaledKernel μ (φ n) t) atTop (𝓝 (f t))) :
    ∃ u : GroundProfile, ∀ t ∈ Ico (0 : ℝ) 1, profile u t = f t := by
  let F : ℝ → ℝ := fun t => f (max t 0)
  have hlimF (t : ℝ) (ht : t < 1) :
      Tendsto (fun n => rescaledKernel μ (φ n) t) atTop (𝓝 (F t)) := by
    simpa only [rescaledKernel_max_zero] using
      hlim (max t 0) ⟨le_max_right _ _, max_lt ht zero_lt_one⟩
  have hFanti : AntitoneOn F (Iio 1) := by
    intro s hs t ht hst
    apply le_of_tendsto_of_tendsto' (hlimF t ht) (hlimF s hs)
    intro n
    exact mul_le_mul_of_nonneg_left
      (xHat_antitone (CSParisiMeasure.canonicalMinimizer μ ((φ n + 1 : ℕ) : ℝ)) hst)
      (by positivity)
  have hFconc : ConcaveOn ℝ (Iio 1) F := by
    refine ⟨convex_Iio 1, ?_⟩
    intro s hs t ht a b ha hb hab
    have hx : a • s + b • t ∈ Iio (1 : ℝ) := (convex_Iio 1) hs ht ha hb hab
    apply le_of_tendsto_of_tendsto'
      (((hlimF s hs).const_mul a).add ((hlimF t ht).const_mul b)) (hlimF _ hx)
    intro n
    have hc := (xHat_concave
      (CSParisiMeasure.canonicalMinimizer μ ((φ n + 1 : ℕ) : ℝ)).law
      (CSParisiMeasure.canonicalMinimizer μ ((φ n + 1 : ℕ) : ℝ)).hasCutoff).2
        (mem_univ s) (mem_univ t) ha hb hab
    have hh := mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ ((φ n + 1 : ℕ) : ℝ))
    dsimp only [rescaledKernel, smul_eq_mul] at *
    nlinarith
  let d := 1 / (1 + Real.sqrt (μ.xi2 1) + μ.xi2 1 * kernelMassBound μ)
  have hd : 0 < d := by
    apply one_div_pos.mpr
    have hK := μ.xi2_pos zero_lt_one
    have hM := kernelMassBound_pos μ
    positivity
  have hlower : ∀ t < 1, d ≤ F t := fun t ht =>
    rescaledKernel_limit_uniform_lower μ f φ hφ hlim (max t 0)
      ⟨le_max_right _ _, max_lt ht zero_lt_one⟩
  obtain ⟨u, hu⟩ := groundProfile_of_concave_kernel F hd hlower hFanti hFconc
  refine ⟨u, ?_⟩
  intro t ht
  simpa only [F, max_eq_left ht.1] using hu t ht

/-- The exact original extraction hypothesis, including every
admissibility field and the strict height-versus-mass inequality. -/
theorem rescaledMinimizerExtraction : RescaledMinimizerExtraction := by
  intro μ
  obtain ⟨f, φ, hφ, hlim⟩ := exists_rescaledKernel_pointwise_limit μ
  obtain ⟨u, hu⟩ := rescaledKernel_limit_admissible μ f φ hφ hlim
  refine ⟨u, φ, hφ, ?_⟩
  intro t ht
  simpa only [← hu t ht, rescaledKernel] using hlim t ht

/-- Actual minimizing profiles satisfy the previously isolated liminf
inequality, with no remaining compactness hypothesis. -/
theorem groundMinimizerLiminfCompactness : GroundMinimizerLiminfCompactness :=
  groundMinimizerLiminfCompactness_of_extraction rescaledMinimizerExtraction

/-- Chen–Sen's full finite-mixture ground interface from Chen alone. -/
theorem chenSenFiniteGround (hChen : Chen2013FiniteParisi) : ChenSenFiniteGround :=
  chenSenFiniteGround_of_rescaled_minimizers hChen rescaledMinimizerExtraction

end SlowEquilibration.SourceLiteratureGroundStateExtraction

namespace SlowEquilibration.SourceLiteratureGroundStateExtraction.Endpoints

open SlowEquilibration.LiteratureSubagProposition24Proof

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalTAPCertificate
open SourceLiteratureParisi SourceLiteratureGroundStateExtraction SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion
open SourceReductionConsumerAsymptotic SphericalOrthogonalHaar
open SphericalOverlapExponential SphericalAging.HardSphereDynamics
open scoped Topology NNReal

set_option autoImplicit false
universe u v

/-- The literal endpoint with the ground-state literature hypothesis and
all intermediate recovery, compactness, and extraction hypotheses removed. -/
theorem finiteMixture_main_condensed_and_initial_literal_reduced3
    (μ : FiniteMixture) {β x Q : ℝ} (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (h5 : Theorem5 (literatureThermodynamicData hChen
      (chenSenFiniteGround hChen) μ h.beta_pos.le))
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
    (chenSenFiniteGround hChen) h5 h25

/-- The universe-polymorphic all-initial conclusion, using Chen alone
for all ground-state and zero-temperature variational input. -/
theorem finiteMixture_all_initial_spherical_of_literature_reduced3
    (μ : FiniteMixture) {β x Q : ℝ} (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (h5 : Theorem5 (literatureThermodynamicData hChen
      (chenSenFiniteGround hChen) μ h.beta_pos.le))
    (h25 : Remark25Contrapositive μ β) :
    ∃ γ : ℝ, 0 < γ ∧ SourceMixedCountCapturePackage.SphericalInitialConclusions.{u,v} μ β γ := by
  exact finiteMixture_all_initial_spherical_of_literature_reduced.{u,v} μ h hChen
    (chenSenFiniteGround hChen) h5 h25

end SlowEquilibration.SourceLiteratureGroundStateExtraction.Endpoints

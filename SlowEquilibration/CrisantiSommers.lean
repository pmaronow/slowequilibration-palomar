-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic

@[expose] public section

namespace SlowEquilibration.CrisantiSommers

open MeasureTheory Set Filter
open scoped Topology

/-- A support cutoff in the manuscript's class of variational measures. -/
def HasCutoff (ζ : Measure ℝ) (q : ℝ) : Prop :=
  0 ≤ q ∧ q < 1 ∧ ∀ᵐ s ∂ζ, s ∈ Icc (0:ℝ) q

/-- The actual integrated distribution function, expressed using the
Fubini kernel from the manuscript. -/
noncomputable def xHat (ζ : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ s, 1-max t s ∂ζ

/-- The ordinary Crisanti--Sommers functional at a valid cutoff q.
Independence of that cutoff is proved separately. -/
noncomputable def functional (β : ℝ) (η : ℝ → ℝ) (ζ : Measure ℝ) (q : ℝ) : ℝ :=
  (β^2*(η 1-∫ s, η s ∂ζ)+(∫ t in (0:ℝ)..q, (xHat ζ t)⁻¹)+Real.log (1-q))/2

/-- The actual first-variation potential. -/
noncomputable def firstVariation (β : ℝ) (η : ℝ → ℝ) (ζ : Measure ℝ) (s : ℝ) : ℝ :=
  β^2*η s-(∫ t in (0:ℝ)..s, (s-t)/(xHat ζ t)^2)

lemma kernel_integrable (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q : ℝ} (hq : HasCutoff ζ q) (t : ℝ) :
    Integrable (fun s => 1-max t s) ζ := by
  apply (integrable_const (1+|t|+q)).mono' (by fun_prop)
  filter_upwards [hq.2.2] with s hs
  rw [Real.norm_eq_abs]
  have hb : |max t s| ≤ |t|+q := by
    apply abs_le.mpr
    constructor
    · have htl : -|t| ≤ t := neg_abs_le t
      have htmax : t ≤ max t s := le_max_left t s
      linarith [hq.1]
    · apply max_le
      · linarith [le_abs_self t,hq.1]
      · linarith [hs.2,abs_nonneg t]
  have h := abs_sub_le (1:ℝ) (0:ℝ) (max t s)
  norm_num at h
  linarith

/-- The integrated kernel is globally 1-Lipschitz, even though its density
representation is supported only on the fixed compact interval. -/
theorem xHat_lipschitz (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q : ℝ} (hq : HasCutoff ζ q) : LipschitzWith 1 (xHat ζ) := by
  apply LipschitzWith.of_dist_le_mul
  intro t u
  change |xHat ζ t-xHat ζ u| ≤ (1:ℝ)*|t-u|
  rw [one_mul]
  unfold xHat
  rw [← integral_sub (kernel_integrable ζ hq t) (kernel_integrable ζ hq u)]
  have hb : ∀ᵐ s ∂ζ, ‖(1-max t s)-(1-max u s)‖ ≤ |t-u| := by
    filter_upwards [] with s
    rw [Real.norm_eq_abs]
    have heq : (1-max t s)-(1-max u s)=-(max t s-max u s) := by ring
    rw [heq,abs_neg]
    exact abs_max_sub_max_le_abs t u s
  have h := norm_integral_le_of_norm_le_const (μ:=ζ) hb
  simpa [Real.norm_eq_abs] using h

theorem xHat_continuous (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q : ℝ} (hq : HasCutoff ζ q) : Continuous (xHat ζ) :=
  (xHat_lipschitz ζ hq).continuous

/-- The pointwise lower bound used to justify all denominators. -/
theorem xHat_lower_bound (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q : ℝ} (hq : HasCutoff ζ q) (t : ℝ) :
    1-max t q ≤ xHat ζ t := by
  have h := integral_mono_ae (integrable_const (1-max t q)) (kernel_integrable ζ hq t)
    (hq.2.2.mono (fun s hs => sub_le_sub_left (max_le_max_left t hs.2) 1))
  simpa [xHat] using h

/-- The ordinary upper bound, obtained from max(t,s)≥t. -/
theorem xHat_upper_bound (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q : ℝ} (hq : HasCutoff ζ q) (t : ℝ) :
    xHat ζ t ≤ 1-t := by
  have h := integral_mono_ae (kernel_integrable ζ hq t) (integrable_const (1-t))
    (Eventually.of_forall (fun s => sub_le_sub_left (le_max_left t s) 1))
  simpa [xHat] using h

/-- Uniform positive lower bound on the entire cutoff interval. -/
theorem xHat_ge_one_sub_cutoff (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q : ℝ} (hq : HasCutoff ζ q) {t : ℝ} (ht : t ≤ q) :
    1-q ≤ xHat ζ t := by
  simpa only [max_eq_right ht] using xHat_lower_bound ζ hq t

/-- Positivity at every point below one. -/
theorem xHat_pos (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q t : ℝ} (hq : HasCutoff ζ q) (ht : t < 1) : 0 < xHat ζ t := by
  have hmax : max t q < 1 := max_lt ht hq.2.1
  exact (sub_pos.mpr hmax).trans_le (xHat_lower_bound ζ hq t)

/-- Above the support cutoff the hatted function is exactly 1-t. -/
theorem xHat_tail (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q t : ℝ} (hq : HasCutoff ζ q) (ht : q ≤ t) : xHat ζ t=1-t := by
  unfold xHat
  have heq : (fun s => 1-max t s) =ᵐ[ζ] fun _ => 1-t :=
    hq.2.2.mono (fun s hs => by dsimp only; rw [max_eq_left (hs.2.trans ht)])
  rw [integral_congr_ae heq]
  simp

/-- The actual inverse hatted function is interval-integrable throughout
any compact interval strictly below one. -/
theorem inverse_xHat_intervalIntegrable (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q a b : ℝ} (hq : HasCutoff ζ q) (ha : a < 1) (hb : b < 1) :
    IntervalIntegrable (fun t => (xHat ζ t)⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply (xHat_continuous ζ hq).continuousOn.inv₀
  intro t ht
  have ht1 : t < 1 := lt_of_le_of_lt ht.2 (max_lt ha hb)
  exact (xHat_pos ζ hq ht1).ne'

/-- Raising a valid cutoff preserves admissibility. -/
theorem HasCutoff.mono {ζ : Measure ℝ} {q q' : ℝ} (hq : HasCutoff ζ q)
    (hqq' : q ≤ q') (hq' : q' < 1) : HasCutoff ζ q' :=
  ⟨hq.1.trans hqq',hq',hq.2.2.mono (fun _ hs => ⟨hs.1,hs.2.trans hqq'⟩)⟩

/-- The logarithmic primitive that cancels the support-cutoff entropy tail. -/
theorem integral_inverse_one_sub {a b : ℝ} (ha : a < 1) (hb : b < 1) :
    (∫ t in a..b, (1-t)⁻¹)=Real.log (1-a)-Real.log (1-b) := by
  have hcont : ContinuousOn (fun t : ℝ => (1-t)⁻¹) (uIcc a b) := by
    apply (continuous_const.sub continuous_id).continuousOn.inv₀
    intro t ht
    exact (sub_pos.mpr (lt_of_le_of_lt ht.2 (max_lt ha hb))).ne'
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f:=fun t : ℝ => -Real.log (1-t))
    (f':=fun t : ℝ => (1-t)⁻¹)
    (fun t ht => by
      have hne : 1-t ≠ 0 :=
        (sub_pos.mpr (lt_of_le_of_lt ht.2 (max_lt ha hb))).ne'
      have hd := (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).log hne).neg
      convert hd using 1 <;> try { funext u; rfl } <;> simp [div_eq_mul_inv])
    hcont.intervalIntegrable
  simpa only [neg_sub_neg] using hh

/-- Exact integral of the hatted-function tail above the support. -/
theorem integral_inverse_xHat_tail (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q q' : ℝ} (hq : HasCutoff ζ q) (hqq' : q ≤ q') (hq' : q' < 1) :
    (∫ t in q..q', (xHat ζ t)⁻¹)=Real.log (1-q)-Real.log (1-q') := by
  rw [intervalIntegral.integral_congr]
  · exact integral_inverse_one_sub hq.2.1 hq'
  · intro t ht
    have htq : q ≤ t := by
      have hh := ht.1
      rw [min_eq_left hqq'] at hh
      exact hh
    dsimp only
    rw [xHat_tail ζ hq htq]

/-- The Crisanti--Sommers value is independent of the valid cutoff witness. -/
theorem functional_cutoff_independent (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    (β : ℝ) (η : ℝ → ℝ) {q q' : ℝ}
    (hq : HasCutoff ζ q) (hq' : HasCutoff ζ q') :
    functional β η ζ q=functional β η ζ q' := by
  wlog hqq' : q ≤ q' generalizing q q'
  · exact (this hq' hq (le_of_not_ge hqq')).symm
  have hi0 : IntervalIntegrable (fun t => (xHat ζ t)⁻¹) volume (0:ℝ) q :=
    inverse_xHat_intervalIntegrable ζ hq (by norm_num) hq.2.1
  have hi1 : IntervalIntegrable (fun t => (xHat ζ t)⁻¹) volume q q' :=
    inverse_xHat_intervalIntegrable ζ hq hq.2.1 hq'.2.1
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi0 hi1
  rw [integral_inverse_xHat_tail ζ hq hqq' hq'.2.1] at hsplit
  unfold functional
  linarith

/-- Concavity of the actual hatted function, derived directly from its
integral kernel instead of postulating distribution-function slopes. -/
theorem xHat_concave (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q : ℝ} (hq : HasCutoff ζ q) : ConcaveOn ℝ univ (xHat ζ) := by
  refine ⟨convex_univ,?_⟩
  intro t _ u _ a b ha hb hab
  have hi := integral_mono_ae
    (((kernel_integrable ζ hq t).const_mul a).add ((kernel_integrable ζ hq u).const_mul b))
    (kernel_integrable ζ hq (a*t+b*u))
    (Eventually.of_forall (fun s => by
      have hmax : max (a*t+b*u) s ≤ a*max t s+b*max u s := by
        apply max_le
        · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left t s) ha)
            (mul_le_mul_of_nonneg_left (le_max_left u s) hb)
        · have hh := add_le_add (mul_le_mul_of_nonneg_left (le_max_right t s) ha)
            (mul_le_mul_of_nonneg_left (le_max_right u s) hb)
          have hss : a*s+b*s=s := by rw [← add_mul,hab,one_mul]
          rw [hss] at hh
          exact hh
      change a*(1-max t s)+b*(1-max u s) ≤ 1-max (a*t+b*u) s
      nlinarith))
  change (∫ s, a*(1-max t s)+b*(1-max u s) ∂ζ) ≤ _ at hi
  rw [integral_add ((kernel_integrable ζ hq t).const_mul a)
    ((kernel_integrable ζ hq u).const_mul b),integral_const_mul,integral_const_mul] at hi
  simpa only [smul_eq_mul,xHat] using hi

end SlowEquilibration.CrisantiSommers

-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntropyTransfer
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Stationary displacement tests for genuine Markov kernels

The set of acceptable starting points is defined from the actual transition
kernel. Its measurability and probability bound follow from two applications
of Chebyshev's inequality. An endpoint image ball then tests both total
variation and relative entropy at every earlier time.
-/

@[expose] public section

noncomputable section
namespace SlowEquilibration.StationaryTrap

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V H : Type*} [MeasurableSpace V]
variable [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H]
variable [SecondCountableTopology H]

/-- The literal displacement event in the two-time space. -/
def farEvent (B : V → H) (ρ : ℝ) : Set (V × V) :=
  {z | ρ < ‖B z.2 - B z.1‖}

/-- The literal image ball centered at the initial image. -/
def imageBall (B : V → H) (ρ : ℝ) (x : V) : Set V :=
  {y | ‖B y - B x‖ ≤ ρ}

lemma farEvent_measurable {B : V → H} (hB : Measurable B) (ρ : ℝ) :
    MeasurableSet (farEvent B ρ) :=
  measurableSet_lt measurable_const ((hB.comp measurable_snd).sub
    (hB.comp measurable_fst)).norm

lemma imageBall_measurable {B : V → H} (hB : Measurable B) (ρ : ℝ) (x : V) :
    MeasurableSet (imageBall B ρ x) :=
  measurableSet_le (hB.sub measurable_const).norm measurable_const

/-- Actual transition probability of displacement beyond the prescribed radius. -/
def farProbability (K : Kernel V V) (B : V → H) (ρ : ℝ) (x : V) : ℝ :=
  (K x).real {y | ρ < ‖B y - B x‖}

lemma farProbability_measurable (K : Kernel V V) [IsMarkovKernel K]
    {B : V → H} (hB : Measurable B) (ρ : ℝ) :
    Measurable (farProbability K B ρ) := by
  exact (Kernel.measurable_kernel_prodMk_left (κ := K)
    (farEvent_measurable hB ρ)).ennreal_toReal

lemma farProbability_integrable (π : Measure V) [IsProbabilityMeasure π]
    (K : Kernel V V) [IsMarkovKernel K] {B : V → H}
    (hB : Measurable B) (ρ : ℝ) : Integrable (farProbability K B ρ) π := by
  apply (integrable_const (μ := π) (1 : ℝ)).mono'
    (farProbability_measurable K hB ρ).aestronglyMeasurable
  filter_upwards [] with x
  simpa [farProbability, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using
    (measureReal_le_one (μ := K x) (s := {y | ρ < ‖B y - B x‖}))

lemma integral_farProbability (π : Measure V) [IsProbabilityMeasure π]
    (K : Kernel V V) [IsMarkovKernel K] {B : V → H}
    (hB : Measurable B) (ρ : ℝ) :
    (∫ x, farProbability K B ρ x ∂π) = (π ⊗ₘ K).real (farEvent B ρ) := by
  rw [Measure.real, Measure.compProd_apply (farEvent_measurable hB ρ)]
  exact integral_toReal (Kernel.measurable_kernel_prodMk_left
    (farEvent_measurable hB ρ)).aemeasurable
    (Eventually.of_forall (fun x => measure_lt_top (K x) _))

/-- Starting points whose endpoint displacement probability is at most η. -/
def goodStartingSet (K : Kernel V V) (B : V → H) (ρ η : ℝ) : Set V :=
  {x | farProbability K B ρ x ≤ η}

lemma goodStartingSet_measurable (K : Kernel V V) [IsMarkovKernel K]
    {B : V → H} (hB : Measurable B) (ρ η : ℝ) :
    MeasurableSet (goodStartingSet K B ρ η) :=
  measurableSet_le (farProbability_measurable K hB ρ) measurable_const

/-- The first Chebyshev bound uses the actual two-time displacement moment. -/
theorem farEvent_probability_le (π : Measure V) [IsProbabilityMeasure π]
    (K : Kernel V V) [IsMarkovKernel K] (B : V → H) {ρ : ℝ} (hρ : 0 < ρ)
    (hI : Integrable (fun z : V × V => ‖B z.2 - B z.1‖ ^ 2) (π ⊗ₘ K)) :
    ρ ^ 2 * (π ⊗ₘ K).real (farEvent B ρ) ≤
      ∫ z, ‖B z.2 - B z.1‖ ^ 2 ∂(π ⊗ₘ K) := by
  have hsub : farEvent B ρ ⊆ {z : V × V | ρ ^ 2 ≤ ‖B z.2 - B z.1‖ ^ 2} := by
    intro z hz
    exact (sq_le_sq₀ hρ.le (norm_nonneg _)).mpr hz.le
  exact (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (sq_nonneg ρ)).trans
    (mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall (fun z => sq_nonneg _))
      hI (ρ ^ 2))

/-- The exact bad-starting-mass estimate in `lem:sp-trap`. Its moment
hypothesis is the preceding genuine stationary energy estimate. -/
theorem goodStartingSet_compl_mass_le (π : Measure V) [IsProbabilityMeasure π]
    (K : Kernel V V) [IsMarkovKernel K] {B : V → H} (hB : Measurable B)
    {ρ η C : ℝ} (hρ : 0 < ρ) (hη : 0 < η)
    (hI : Integrable (fun z : V × V => ‖B z.2 - B z.1‖ ^ 2) (π ⊗ₘ K))
    (hMoment : (∫ z, ‖B z.2 - B z.1‖ ^ 2 ∂(π ⊗ₘ K)) ≤ C) :
    π.real (goodStartingSet K B ρ η)ᶜ ≤ C / (ρ ^ 2 * η) := by
  have hsub : (goodStartingSet K B ρ η)ᶜ ⊆
      {x | η ≤ farProbability K B ρ x} := by
    intro x hx
    change ¬farProbability K B ρ x ≤ η at hx
    exact le_of_lt (lt_of_not_ge hx)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun x => measureReal_nonneg (μ := K x)))
    (farProbability_integrable π K hB ρ) η
  change η * π.real {x | η ≤ farProbability K B ρ x} ≤
    ∫ x, farProbability K B ρ x ∂π at hmarkov
  have hfirst := farEvent_probability_le π K B hρ hI
  rw [integral_farProbability π K hB ρ] at hmarkov
  have hsecond : η * π.real (goodStartingSet K B ρ η)ᶜ ≤
      (π ⊗ₘ K).real (farEvent B ρ) :=
    (mul_le_mul_of_nonneg_left (measureReal_mono hsub) hη.le).trans hmarkov
  rw [le_div_iff₀ (mul_pos (sq_pos_of_pos hρ) hη)]
  nlinarith [mul_le_mul_of_nonneg_left hsecond (sq_nonneg ρ)]

/-- An acceptable starting point puts at least 1−η endpoint mass in its
literal image ball. -/
theorem imageBall_transition_mass (K : Kernel V V) [IsMarkovKernel K]
    {B : V → H} (hB : Measurable B) (ρ η : ℝ) {x : V}
    (hx : x ∈ goodStartingSet K B ρ η) :
    1 - η ≤ (K x).real (imageBall B ρ x) := by
  have hc := probReal_add_probReal_compl (μ := K x) (imageBall_measurable hB ρ x)
  have hfar : (imageBall B ρ x)ᶜ = {y | ρ < ‖B y - B x‖} := by
    ext y
    simp [imageBall]
  rw [hfar] at hc
  change (K x).real {y | ρ < ‖B y - B x‖} ≤ η at hx
  linarith

/-- Pointwise total-variation contraction along a genuine kernel semigroup. -/
theorem transition_totalVariation_antitone (P : ℝ≥0 → Kernel V V)
    [∀ t, IsMarkovKernel (P t)] (π : Measure V) [IsProbabilityMeasure π]
    (hcomp : ∀ s t, P (s + t) = P s ∘ₖ P t)
    (hinv : ∀ t, P t ∘ₘ π = π) (x : V) :
    Antitone (fun t => totalVariation (P t x) π) := by
  intro s t hst
  have htime : (t - s) + s = t := tsub_add_cancel_of_le hst
  have heq : P t x = P (t - s) ∘ₘ P s x := by
    calc
      P t x = P ((t - s) + s) x := congrArg (fun v => P v x) htime.symm
      _ = P (t - s) ∘ₘ P s x := by rw [hcomp, Kernel.comp_apply]
  change totalVariation (P t x) π ≤ totalVariation (P s x) π
  rw [heq]
  have hc := totalVariation_kernel_contraction (P s x) π (P (t - s))
  rw [hinv] at hc
  exact hc

/-- Pointwise relative-entropy contraction, including infinite values. -/
theorem transition_relativeEntropy_antitone (P : ℝ≥0 → Kernel V V)
    [∀ t, IsMarkovKernel (P t)] (π : Measure V) [IsProbabilityMeasure π]
    (hcomp : ∀ s t, P (s + t) = P s ∘ₖ P t)
    (hinv : ∀ t, P t ∘ₘ π = π) (x : V) :
    Antitone (fun t => InformationTheory.klDiv (P t x) π) := by
  intro s t hst
  have htime : (t - s) + s = t := tsub_add_cancel_of_le hst
  have heq : P t x = P (t - s) ∘ₘ P s x := by
    calc
      P t x = P ((t - s) + s) x := congrArg (fun v => P v x) htime.symm
      _ = P (t - s) ∘ₘ P s x := by rw [hcomp, Kernel.comp_apply]
  change InformationTheory.klDiv (P t x) π ≤ InformationTheory.klDiv (P s x) π
  rw [heq]
  have hc := relativeEntropy_kernel_contraction (P s x) π (P (t - s))
  rw [hinv] at hc
  exact hc

/-- The numerical binary test with an upper bound w for the reference
event. No positive reference-event-mass or finite entropy premise is used. -/
theorem event_relativeEntropy_lower (ν π : Measure V)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure π] {D : Set V}
    (hD : MeasurableSet D) {η w : ℝ} (hη : η ≤ 1) (hw : 0 < w)
    (hν : 1 - η ≤ ν.real D) (hπ : π.real D ≤ w) :
    ENNReal.ofReal ((1 - η) * Real.log (1 / w) - Real.log 2) ≤
      InformationTheory.klDiv ν π := by
  by_cases hw1 : w < 1
  · by_cases ha : π.real D = 0
    · by_cases hp : ν.real D = 0
      · have hη1 : η = 1 := by linarith
        rw [hη1]
        simp only [sub_self, zero_mul, zero_sub]
        rw [ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr (Real.log_nonneg (by norm_num)))]
        exact bot_le
      · have ha' : eventProbability π D = 0 := Subtype.ext ha
        have hp' : eventProbability ν D ≠ 0 := fun h => hp (congrArg Subtype.val h)
        have ht := relativeEntropy_binary_event_test ν π hD
        simp only [binaryLogTest, if_pos ha', if_neg hp'] at ht
        exact le_top.trans ht
    · have hap : 0 < π.real D := lt_of_le_of_ne measureReal_nonneg (Ne.symm ha)
      have ha' : eventProbability π D ≠ 0 := fun h => ha (congrArg Subtype.val h)
      have hlog0 : 0 ≤ Real.log (1 / w) :=
        Real.log_nonneg ((one_le_div hw).mpr hw1.le)
      have hlog : Real.log (1 / w) ≤ Real.log (1 / π.real D) := by
        apply Real.log_le_log (div_pos zero_lt_one hw)
        exact one_div_le_one_div_of_le hap hπ
      have hnum : (1 - η) * Real.log (1 / w) - Real.log 2 ≤
          ν.real D * Real.log (1 / π.real D) - Real.log 2 := by
        have hmul := mul_le_mul hν hlog hlog0 (measureReal_nonneg (μ := ν))
        linarith
      have ht := relativeEntropy_binary_event_test ν π hD
      simp only [binaryLogTest, if_neg ha'] at ht
      exact (ENNReal.ofReal_le_ofReal hnum).trans ht
  · have hlog : Real.log (1 / w) ≤ 0 :=
      Real.log_nonpos (div_nonneg zero_le_one hw.le) ((div_le_one hw).mpr (le_of_not_gt hw1))
    have hnonpos : (1 - η) * Real.log (1 / w) - Real.log 2 ≤ 0 := by
      have := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hη) hlog
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
      linarith
    rw [ENNReal.ofReal_eq_zero.mpr hnonpos]
    exact bot_le

/-- A single actual endpoint event yields both source trapping bounds at
every earlier time. The entropy conclusion is an extended-real inequality. -/
theorem endpoint_separation_all_times (P : ℝ≥0 → Kernel V V)
    [∀ t, IsMarkovKernel (P t)] (π : Measure V) [IsProbabilityMeasure π]
    (hcomp : ∀ s t, P (s + t) = P s ∘ₖ P t)
    (hinv : ∀ t, P t ∘ₘ π = π) (T : ℝ≥0) (x : V)
    {D : Set V} (hD : MeasurableSet D) {η w : ℝ} (hη : η ≤ 1) (hw : 0 < w)
    (hν : 1 - η ≤ (P T x).real D) (hπ : π.real D ≤ w) :
    ∀ t ≤ T, 1 - η - w ≤ totalVariation (P t x) π ∧
      ENNReal.ofReal ((1 - η) * Real.log (1 / w) - Real.log 2) ≤
        InformationTheory.klDiv (P t x) π := by
  intro t ht
  constructor
  · have htest := event_difference_le_totalVariation (P T x) π hD
    have habs := le_abs_self ((P T x).real D - π.real D)
    have hmono := transition_totalVariation_antitone P π hcomp hinv x ht
    linarith
  · exact (event_relativeEntropy_lower (P T x) π hD hη hw hν hπ).trans
      (transition_relativeEntropy_antitone P π hcomp hinv x ht)

/-- The source logarithmic lower bound with its genuine infinite value
when the equilibrium test event has zero mass. -/
def entropyBound (η w : ℝ) : ℝ≥0∞ :=
  if w = 0 then ∞ else ENNReal.ofReal ((1 - η) * Real.log (1 / w) - Real.log 2)

theorem endpoint_separation_all_times_of_nonneg (P : ℝ≥0 → Kernel V V)
    [∀ t, IsMarkovKernel (P t)] (π : Measure V) [IsProbabilityMeasure π]
    (hcomp : ∀ s t, P (s + t) = P s ∘ₖ P t)
    (hinv : ∀ t, P t ∘ₘ π = π) (T : ℝ≥0) (x : V)
    {D : Set V} (hD : MeasurableSet D) {η w : ℝ} (hη : η < 1) (hw : 0 ≤ w)
    (hν : 1 - η ≤ (P T x).real D) (hπ : π.real D ≤ w) :
    ∀ t ≤ T, 1 - η - w ≤ totalVariation (P t x) π ∧
      entropyBound η w ≤ InformationTheory.klDiv (P t x) π := by
  by_cases hw0 : w = 0
  · have ha : π.real D = 0 := le_antisymm (by simpa [hw0] using hπ) measureReal_nonneg
    have hp : (P T x).real D ≠ 0 := ne_of_gt (lt_of_lt_of_le (sub_pos.mpr hη) hν)
    have ha' : eventProbability π D = 0 := Subtype.ext ha
    have hp' : eventProbability (P T x) D ≠ 0 := fun h => hp (congrArg Subtype.val h)
    have hkl := relativeEntropy_binary_event_test (P T x) π hD
    simp only [binaryLogTest, if_pos ha', if_neg hp'] at hkl
    intro t ht
    constructor
    · have htest := event_difference_le_totalVariation (P T x) π hD
      have habs := le_abs_self ((P T x).real D - π.real D)
      have hmono := transition_totalVariation_antitone P π hcomp hinv x ht
      linarith
    · simp only [entropyBound, if_pos hw0]
      exact hkl.trans (transition_relativeEntropy_antitone P π hcomp hinv x ht)
  · have hpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
    simpa only [entropyBound, if_neg hw0] using
      endpoint_separation_all_times P π hcomp hinv T x hD hη.le hpos hν hπ

end SlowEquilibration.StationaryTrap

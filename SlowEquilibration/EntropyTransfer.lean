module

public import SlowEquilibration.Separation
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
public import Mathlib.Probability.Kernel.Composition.RadonNikodym
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Binary relative entropy and endpoint transfer

The binary laws below are actual Mathlib Bernoulli measures. They are
obtained by pushing a probability measure forward along the measurable
indicator of an event.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace SlowEquilibration

variable {α : Type*} [MeasurableSpace α]

/-- The probability of an event, regarded as a point of the unit interval. -/
noncomputable def eventProbability (μ : Measure α) [IsProbabilityMeasure μ]
    (B : Set α) : unitInterval :=
  ⟨μ.real B, measureReal_nonneg, measureReal_le_one⟩

omit [MeasurableSpace α] in
private lemma eventIndicator_preimage_false (B : Set α) :
    eventIndicator B ⁻¹' {false} = Bᶜ := by
  classical
  ext x
  simp [eventIndicator, Set.piecewise]

/-- The pushforward along an event indicator is exactly its Bernoulli law. -/
theorem eventIndicator_law (μ : Measure α) [IsProbabilityMeasure μ]
    {B : Set α} (hB : MeasurableSet B) :
    μ.map (eventIndicator B) = bernoulliMeasure true false (eventProbability μ B) := by
  apply ext_iff_measureReal_singleton.mpr
  intro b
  cases b
  · have hcomp := probReal_add_probReal_compl (μ := μ) hB
    simp only [Measure.real, Measure.map_apply (measurable_eventIndicator hB)
      (measurableSet_singleton false), eventIndicator_preimage_false]
    rw [← measureReal_def]
    have h : (bernoulliMeasure true false (eventProbability μ B)).real {false} =
        1 - μ.real B := by
      simp [eventProbability]
    change μ.real Bᶜ = (bernoulliMeasure true false (eventProbability μ B)).real {false}
    rw [h]
    linarith
  · rw [Measure.real, eventIndicator_law_true μ hB]
    change μ.real B = _
    simp [eventProbability]

/-- The standard binary KL divergence as the relative entropy between
actual Bernoulli probability measures. -/
noncomputable def binaryRelativeEntropy (p a : unitInterval) : ℝ≥0∞ :=
  InformationTheory.klDiv (bernoulliMeasure true false p) (bernoulliMeasure true false a)

/-- First inequality of `lem:pre-binary`, with its Bernoulli-law identity
proved explicitly. -/
theorem binary_data_processing (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : Set α} (hB : MeasurableSet B) :
    binaryRelativeEntropy (eventProbability μ B) (eventProbability ν B) ≤
      InformationTheory.klDiv μ ν := by
  unfold binaryRelativeEntropy
  rw [← eventIndicator_law μ hB, ← eventIndicator_law ν hB]
  exact binary_relativeEntropy_data_processing μ ν hB

private noncomputable def bernoulliDensity (p a : unitInterval) (b : Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (if b then (p : ℝ) / (a : ℝ) else (1 - (p : ℝ)) / (1 - (a : ℝ)))

private lemma bernoulli_withDensity (p a : unitInterval)
    (ha0 : 0 < (a : ℝ)) (ha1 : (a : ℝ) < 1) :
    (bernoulliMeasure true false a).withDensity (bernoulliDensity p a) =
      bernoulliMeasure true false p := by
  have hp0 : 0 ≤ (p : ℝ) := p.property.1
  have hp1 : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.property.2
  have ha1' : 0 < 1 - (a : ℝ) := sub_pos.mpr ha1
  simp only [bernoulliMeasure_def, ENNReal.smul_def, withDensity_add_measure,
    withDensity_smul_measure, dirac_withDensity, smul_smul,
    bernoulliDensity, Bool.false_eq_true, ↓reduceIte]
  have ht : (unitInterval.toNNReal a : ℝ≥0∞) * ENNReal.ofReal ((p : ℝ) / (a : ℝ)) =
      (unitInterval.toNNReal p : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal,
      ← ENNReal.ofReal_mul ha0.le, mul_div_cancel₀ _ ha0.ne']
    rw [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal]
  have hf : (unitInterval.toNNReal (unitInterval.symm a) : ℝ≥0∞) *
      ENNReal.ofReal ((1 - (p : ℝ)) / (1 - (a : ℝ))) =
      (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal,
      unitInterval.coe_symm_eq, ← ENNReal.ofReal_mul ha1'.le,
      mul_div_cancel₀ _ ha1'.ne']
    rw [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
  rw [ht, hf]

private lemma bernoulli_ac (p a : unitInterval)
    (ha0 : 0 < (a : ℝ)) (ha1 : (a : ℝ) < 1) :
    bernoulliMeasure true false p ≪ bernoulliMeasure true false a := by
  rw [← bernoulli_withDensity p a ha0 ha1]
  exact withDensity_absolutelyContinuous _ _

/-- The finite positive-reference-mass formula for genuine Bernoulli KL. -/
theorem binaryRelativeEntropy_formula (p a : unitInterval)
    (ha0 : 0 < (a : ℝ)) (ha1 : (a : ℝ) < 1) :
    (binaryRelativeEntropy p a).toReal =
      (p : ℝ) * Real.log ((p : ℝ) / (a : ℝ)) +
        (1 - (p : ℝ)) * Real.log ((1 - (p : ℝ)) / (1 - (a : ℝ))) := by
  have hAC := bernoulli_ac p a ha0 ha1
  have hDensity : Measurable (bernoulliDensity p a) := measurable_of_finite _
  have hDeriv := Measure.rnDeriv_withDensity (bernoulliMeasure true false a) hDensity
  rw [bernoulli_withDensity p a ha0 ha1] at hDeriv
  have hDerivμ := hAC.ae_le hDeriv
  have hIntegral : (∫ b, llr (bernoulliMeasure true false p)
      (bernoulliMeasure true false a) b ∂bernoulliMeasure true false p) =
      ∫ b, Real.log (bernoulliDensity p a b).toReal ∂bernoulliMeasure true false p := by
    apply integral_congr_ae
    filter_upwards [hDerivμ] with b hb
    simp [llr, hb]
  unfold binaryRelativeEntropy
  rw [InformationTheory.toReal_klDiv_of_measure_eq hAC (by simp), hIntegral,
    integral_bernoulliMeasure]
  have hp0 : 0 ≤ (p : ℝ) := p.property.1
  have hp1 : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.property.2
  have ha1' : 0 < 1 - (a : ℝ) := sub_pos.mpr ha1
  simp [bernoulliDensity, ENNReal.toReal_ofReal, div_nonneg hp0 ha0.le,
    div_nonneg hp1 ha1'.le, smul_eq_mul]

/-- The reference law has two positive atoms, so its Bernoulli KL is finite. -/
theorem binaryRelativeEntropy_ne_top (p a : unitInterval)
    (ha0 : 0 < (a : ℝ)) (ha1 : (a : ℝ) < 1) :
    binaryRelativeEntropy p a ≠ ∞ :=
  InformationTheory.klDiv_ne_top (bernoulli_ac p a ha0 ha1)
    (integrable_bernoulliMeasure _ _ _ _)

private lemma mul_log_div (x y : ℝ) (hy : y ≠ 0) :
    x * Real.log (x / y) = x * Real.log x - x * Real.log y := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.log_div hx hy]
    ring

/-- The elementary numerical bound in `lem:pre-binary`, including p = 0
and p = 1, for reference probability strictly between zero and one. -/
theorem binaryRelativeEntropy_log_lower (p a : unitInterval)
    (ha0 : 0 < (a : ℝ)) (ha1 : (a : ℝ) < 1) :
    (p : ℝ) * Real.log (1 / (a : ℝ)) - Real.log 2 ≤
      (binaryRelativeEntropy p a).toReal := by
  rw [binaryRelativeEntropy_formula p a ha0 ha1,
    mul_log_div _ _ ha0.ne', mul_log_div _ _ (sub_pos.mpr ha1).ne']
  have hentropy := Real.binEntropy_le_log_two (p := (p : ℝ))
  have hlog : Real.log (1 - (a : ℝ)) ≤ 0 :=
    Real.log_nonpos (by linarith) (by linarith)
  have hterm : 0 ≤ -(1 - (p : ℝ)) * Real.log (1 - (a : ℝ)) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith [p.property.2]) hlog
  simp only [one_div, Real.log_inv] at *
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog,
    Real.negMulLog] at hentropy
  nlinarith

/-- The a = 0 boundary case uses absolute continuity, so positive success
probability has infinite binary divergence. -/
theorem binaryRelativeEntropy_zero_reference (p : unitInterval) :
    binaryRelativeEntropy p 0 = if p = 0 then 0 else ∞ := by
  classical
  by_cases hp : p = 0
  · simp [hp, binaryRelativeEntropy]
  · simp only [hp, ↓reduceIte]
    unfold binaryRelativeEntropy
    apply InformationTheory.klDiv_of_not_ac
    intro hAC
    have hnull := hAC (s := {true}) (by simp)
    have hp0 : (p : ℝ) ≠ 0 := by
      intro h
      apply hp
      exact Subtype.ext h
    have hpPos : 0 < (p : ℝ) := lt_of_le_of_ne p.property.1 (Ne.symm hp0)
    have hreal := congrArg ENNReal.toReal hnull
    simpa using ne_of_gt hpPos (by simpa using hreal)

/-- The nonnegative extended-real form of the manuscript's logarithmic
binary test. At a = 0, its clauses encode 0 * infinity = 0; finite negative
values are truncated to zero because KL itself is nonnegative. -/
noncomputable def binaryLogTest (p a : unitInterval) : ℝ≥0∞ :=
  if a = 0 then if p = 0 then 0 else ∞
  else ENNReal.ofReal ((p : ℝ) * Real.log (1 / (a : ℝ)) - Real.log 2)

/-- Second inequality of `lem:pre-binary`, including all boundary cases
with the manuscript's convention for zero times infinity. -/
theorem binaryLogTest_le_binaryRelativeEntropy (p a : unitInterval) :
    binaryLogTest p a ≤ binaryRelativeEntropy p a := by
  classical
  by_cases ha : a = 0
  · simp [binaryLogTest, ha, binaryRelativeEntropy_zero_reference]
  · by_cases ha1 : a = 1
    · have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      simp [binaryLogTest, ha1, ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr hlog2)]
    · have ha0 : 0 < (a : ℝ) := by
        have hzero : (a : ℝ) ≠ 0 := fun h => ha (Subtype.ext h)
        exact lt_of_le_of_ne a.property.1 (Ne.symm hzero)
      have haLt : (a : ℝ) < 1 := by
        have hone : (a : ℝ) ≠ 1 := fun h => ha1 (Subtype.ext h)
        exact lt_of_le_of_ne a.property.2 hone
      simp only [binaryLogTest, ha, ↓reduceIte]
      exact ENNReal.ofReal_le_of_le_toReal (binaryRelativeEntropy_log_lower p a ha0 haLt)

/-- The full binary test on arbitrary measurable events of actual
probability measures. No finiteness assumption on their relative entropy
is needed here. -/
theorem relativeEntropy_binary_event_test (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : Set α} (hB : MeasurableSet B) :
    binaryLogTest (eventProbability μ B) (eventProbability ν B) ≤
      InformationTheory.klDiv μ ν :=
  (binaryLogTest_le_binaryRelativeEntropy _ _).trans (binary_data_processing μ ν hB)

/-- Rearranged finite-entropy conclusion of `lem:pre-binary`. -/
theorem relativeEntropy_event_probability_bound (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hKL : InformationTheory.klDiv μ ν ≠ ∞)
    {B : Set α} (hB : MeasurableSet B)
    (ha0 : 0 < ν.real B) (ha1 : ν.real B < 1) :
    μ.real B ≤ ((InformationTheory.klDiv μ ν).toReal + Real.log 2) /
      Real.log (1 / ν.real B) := by
  have hnum := binaryRelativeEntropy_log_lower (eventProbability μ B)
    (eventProbability ν B) ha0 ha1
  have hdata := ENNReal.toReal_mono hKL (binary_data_processing μ ν hB)
  have hlog : 0 < Real.log (1 / ν.real B) :=
    Real.log_pos ((one_lt_div ha0).mpr ha1)
  rw [le_div_iff₀ hlog]
  change μ.real B * Real.log (1 / ν.real B) - Real.log 2 ≤ _ at hnum
  linarith

/-- The positive-reference-mass entropy-transfer conclusion of
`prop:pre-endpoint`, for every time up to the endpoint. -/
theorem markov_endpoint_entropy_separation (P : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (P t)]
    (μ ν π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure π]
    (hcomp : ∀ s t, P (s + t) = P s ∘ₖ P t)
    (hinv : ∀ t, P t ∘ₘ π = π)
    (hKL : InformationTheory.klDiv μ ν ≠ ∞)
    (T : ℝ≥0) {B : Set α} (hB : MeasurableSet B)
    (ha0 : 0 < (P T ∘ₘ ν).real B) (ha1 : (P T ∘ₘ ν).real B < 1) :
    ∀ t ≤ T, 1 - π.real Bᶜ -
      min 1 (((InformationTheory.klDiv μ ν).toReal + Real.log 2) /
        Real.log (1 / (P T ∘ₘ ν).real B)) ≤ totalVariation (P t ∘ₘ μ) π := by
  have hcontract := relativeEntropy_kernel_contraction μ ν (P T)
  have hKLfinal : InformationTheory.klDiv (P T ∘ₘ μ) (P T ∘ₘ ν) ≠ ∞ :=
    ne_of_lt (hcontract.trans_lt (lt_top_iff_ne_top.mpr hKL))
  have hprob := relativeEntropy_event_probability_bound (P T ∘ₘ μ) (P T ∘ₘ ν)
    hKLfinal hB ha0 ha1
  have hreal := ENNReal.toReal_mono hKL hcontract
  have hlog : 0 < Real.log (1 / (P T ∘ₘ ν).real B) :=
    Real.log_pos ((one_lt_div ha0).mpr ha1)
  have hsum : (InformationTheory.klDiv (P T ∘ₘ μ) (P T ∘ₘ ν)).toReal + Real.log 2 ≤
      (InformationTheory.klDiv μ ν).toReal + Real.log 2 := by linarith
  have hfrac := div_le_div_of_nonneg_right hsum hlog.le
  have hp := le_min (measureReal_le_one (μ := P T ∘ₘ μ) (s := B)) (hprob.trans hfrac)
  intro t ht
  have htv := markov_endpoint_separation P μ π hcomp hinv T hB t ht
  linarith

/-- The exact infimum form of the positive-reference-mass formula in
`eq:pre-endpoint-entropy`. -/
theorem markov_endpoint_entropy_infimum (P : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (P t)]
    (μ ν π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure π]
    (hcomp : ∀ s t, P (s + t) = P s ∘ₖ P t)
    (hinv : ∀ t, P t ∘ₘ π = π)
    (hKL : InformationTheory.klDiv μ ν ≠ ∞)
    (T : ℝ≥0) {B : Set α} (hB : MeasurableSet B)
    (ha0 : 0 < (P T ∘ₘ ν).real B) (ha1 : (P T ∘ₘ ν).real B < 1) :
    1 - π.real Bᶜ -
      min 1 (((InformationTheory.klDiv μ ν).toReal + Real.log 2) /
        Real.log (1 / (P T ∘ₘ ν).real B)) ≤
      sInf ((fun t => totalVariation (P t ∘ₘ μ) π) '' Icc 0 T) := by
  apply le_csInf
  · exact ⟨totalVariation (P T ∘ₘ μ) π, T, ⟨zero_le, le_rfl⟩, rfl⟩
  · rintro r ⟨t, ht, rfl⟩
    exact markov_endpoint_entropy_separation P μ ν π hcomp hinv hKL T hB ha0 ha1 t ht.2

/-- The zero-reference-endpoint-mass infimum form of
`prop:pre-endpoint`, complementary to the positive-mass formula. -/
theorem markov_endpoint_entropy_zero_infimum (P : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (P t)]
    (μ ν π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure π]
    (hcomp : ∀ s t, P (s + t) = P s ∘ₖ P t)
    (hinv : ∀ t, P t ∘ₘ π = π)
    (hKL : InformationTheory.klDiv μ ν ≠ ∞)
    (T : ℝ≥0) {B : Set α} (hB : MeasurableSet B)
    (ha : (P T ∘ₘ ν) B = 0) :
    1 - π.real Bᶜ ≤ sInf ((fun t => totalVariation (P t ∘ₘ μ) π) '' Icc 0 T) := by
  apply le_csInf
  · exact ⟨totalVariation (P T ∘ₘ μ) π, T, ⟨zero_le, le_rfl⟩, rfl⟩
  · rintro r ⟨t, ht, rfl⟩
    exact markov_endpoint_separation_zero P μ ν π hcomp hinv hKL T hB ha t ht.2

open scoped Classical in
private lemma kernel_relativeEntropy_formula {β : Type*} [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (K L : Kernel α β) [IsFiniteKernel K] [IsFiniteKernel L] (x : α) :
    InformationTheory.klDiv (K x) (L x) =
      if K x ≪ L x then
        ∫⁻ y, ENNReal.ofReal (InformationTheory.klFun (K.rnDeriv L x y).toReal) ∂L x
      else ∞ := by
  classical
  rw [InformationTheory.klDiv_eq_lintegral_klFun]
  by_cases hAC : K x ≪ L x
  · simp only [hAC, ↓reduceIte]
    apply lintegral_congr_ae
    filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := K) (η := L) (a := x)] with y hy
    rw [hy]
  · simp [hAC]

/-- Pointwise KL between finite kernels is measurable when the output
sigma-algebra is countably generated (or the input is countable). -/
theorem measurable_kernel_relativeEntropy {β : Type*} [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (K L : Kernel α β) [IsFiniteKernel K] [IsFiniteKernel L] :
    Measurable (fun x => InformationTheory.klDiv (K x) (L x)) := by
  classical
  simp_rw [kernel_relativeEntropy_formula]
  have hf : Measurable (fun p : α × β =>
      ENNReal.ofReal (InformationTheory.klFun (K.rnDeriv L p.1 p.2).toReal)) := by
    fun_prop
  exact Measurable.ite (Kernel.measurableSet_absolutelyContinuous K L)
    hf.lintegral_kernel_prod_right' measurable_const

/-- The conditional KL integral identity `eq:pre-chain`, in its more general
form comparing two actual Markov kernels under the same initial measure. -/
theorem relativeEntropy_compProd_right_integral {β : Type*} [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (K L : Kernel α β) [IsMarkovKernel K] [IsMarkovKernel L] :
    InformationTheory.klDiv (μ ⊗ₘ K) (μ ⊗ₘ L) =
      ∫⁻ x, InformationTheory.klDiv (K x) (L x) ∂μ := by
  classical
  by_cases hAC : μ ⊗ₘ K ≪ μ ⊗ₘ L
  · have hACpoint := Measure.absolutelyContinuous_compProd_right_iff.mp hAC
    rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac hAC]
    have hf : Measurable (fun p : α × β =>
        ENNReal.ofReal (InformationTheory.klFun (K.rnDeriv L p.1 p.2).toReal)) := by
      fun_prop
    calc
      (∫⁻ p, ENNReal.ofReal (InformationTheory.klFun
          ((μ ⊗ₘ K).rnDeriv (μ ⊗ₘ L) p).toReal) ∂μ ⊗ₘ L) =
          ∫⁻ p, ENNReal.ofReal (InformationTheory.klFun
            (K.rnDeriv L p.1 p.2).toReal) ∂μ ⊗ₘ L := by
        apply lintegral_congr_ae
        filter_upwards [rnDeriv_measure_compProd_right μ K L] with p hp
        rw [hp]
      _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (InformationTheory.klFun
          (K.rnDeriv L x y).toReal) ∂L x ∂μ := Measure.lintegral_compProd hf
      _ = ∫⁻ x, InformationTheory.klDiv (K x) (L x) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hACpoint] with x hx
        rw [kernel_relativeEntropy_formula K L x, ite_eq_left hx]
  · rw [InformationTheory.klDiv_of_not_ac hAC]
    symm
    by_contra hfin
    have hpoint := ae_lt_top (measurable_kernel_relativeEntropy K L) hfin
    have hACpoint : ∀ᵐ x ∂μ, K x ≪ L x := by
      filter_upwards [hpoint] with x hx
      exact (InformationTheory.klDiv_ne_top_iff.mp hx.ne).1
    exact hAC (Measure.absolutelyContinuous_compProd_right_iff.mpr hACpoint)

/-- Relative entropy is unchanged by swapping the coordinates of a joint
law and its comparison law. -/
theorem relativeEntropy_swap {β : Type*} [MeasurableSpace β]
    (ρ σ : Measure (α × β)) [IsFiniteMeasure ρ] [IsFiniteMeasure σ] :
    InformationTheory.klDiv (ρ.map Prod.swap) (σ.map Prod.swap) =
      InformationTheory.klDiv ρ σ := by
  apply le_antisymm
  · exact InformationTheory.klDiv_map_le ρ σ measurable_swap
  · have h := InformationTheory.klDiv_map_le (ρ.map Prod.swap) (σ.map Prod.swap) measurable_swap
    simpa [Measure.map_map measurable_swap measurable_swap, Function.comp_def] using h

/-- Mutual information of the endpoints, defined by their actual joint law
and the product of its two marginal laws. -/
noncomputable def endpointMutualInformation {β : Type*} [MeasurableSpace β]
    (μ : Measure α) (K : Kernel α β) : ℝ≥0∞ :=
  InformationTheory.klDiv (μ ⊗ₘ K) (μ.prod (K ∘ₘ μ))

/-- The measure-theoretic chain identity `eq:pre-chain-2`. Disintegration
of the reversed joint law proves it with no entropy-finiteness assumptions. -/
theorem endpoint_relativeEntropy_chain {β : Type*} [MeasurableSpace β]
    [StandardBorelSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Kernel α β) [IsMarkovKernel K]
    (π : Measure β) [IsProbabilityMeasure π] :
    InformationTheory.klDiv (μ ⊗ₘ K) (μ.prod π) =
      endpointMutualInformation μ K + InformationTheory.klDiv (K ∘ₘ μ) π := by
  have : Nonempty α := nonempty_of_isProbabilityMeasure μ
  let Γ : Measure (α × β) := μ ⊗ₘ K
  let Γs : Measure (β × α) := Γ.map Prod.swap
  let R : Kernel β α := Γs.condKernel
  have hdis : (K ∘ₘ μ) ⊗ₘ R = Γs := by
    have h := Measure.disintegrate Γs Γs.condKernel
    simpa [Γs, Γ, Measure.fst_map_swap, Measure.snd_compProd, R] using h
  have hchain := InformationTheory.klDiv_compProd_eq_add (K ∘ₘ μ) π R (Kernel.const β μ)
  rw [Measure.compProd_const, Measure.compProd_const, hdis] at hchain
  have hswap1 := relativeEntropy_swap Γ (μ.prod π)
  have hswap2 := relativeEntropy_swap Γ (μ.prod (K ∘ₘ μ))
  rw [Measure.prod_swap] at hswap1 hswap2
  unfold endpointMutualInformation
  change InformationTheory.klDiv Γ (μ.prod π) =
    InformationTheory.klDiv Γ (μ.prod (K ∘ₘ μ)) + InformationTheory.klDiv (K ∘ₘ μ) π
  rw [← hswap1, ← hswap2]
  simpa [Γs, add_comm] using hchain

/-- The golden formula `eq:pre-golden` for actual endpoint mutual
information, with arbitrary (including infinite) relative entropies. -/
theorem endpoint_mutualInformation_golden {β : Type*} [MeasurableSpace β]
    [StandardBorelSpace α] [MeasurableSpace.CountablyGenerated β]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Kernel α β) [IsMarkovKernel K]
    (π : Measure β) [IsProbabilityMeasure π] :
    (∫⁻ x, InformationTheory.klDiv (K x) π ∂μ) =
      endpointMutualInformation μ K + InformationTheory.klDiv (K ∘ₘ μ) π := by
  have h := relativeEntropy_compProd_right_integral μ K (Kernel.const α π)
  simp only [Measure.compProd_const, Kernel.const_apply] at h
  rw [← h]
  exact endpoint_relativeEntropy_chain μ K π

/-- The subtraction form of `lem:pre-MI` when the output-law entropy is
finite. The conditional integral and the mutual information may be infinite. -/
theorem endpoint_mutualInformation_subtraction {β : Type*} [MeasurableSpace β]
    [StandardBorelSpace α] [MeasurableSpace.CountablyGenerated β]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Kernel α β) [IsMarkovKernel K]
    (π : Measure β) [IsProbabilityMeasure π]
    (hKL : InformationTheory.klDiv (K ∘ₘ μ) π ≠ ∞) :
    endpointMutualInformation μ K =
      (∫⁻ x, InformationTheory.klDiv (K x) π ∂μ) - InformationTheory.klDiv (K ∘ₘ μ) π := by
  rw [endpoint_mutualInformation_golden μ K π, ENNReal.add_sub_cancel_right hKL]

/-- Stationary endpoint mutual information, `eq:pre-golden-stationary`. -/
theorem stationary_endpoint_mutualInformation [StandardBorelSpace α]
    (π : Measure α) [IsProbabilityMeasure π]
    (K : Kernel α α) [IsMarkovKernel K] (hinv : K ∘ₘ π = π) :
    endpointMutualInformation π K = ∫⁻ x, InformationTheory.klDiv (K x) π ∂π := by
  have h := endpoint_mutualInformation_golden π K π
  simpa [hinv] using h.symm

end SlowEquilibration

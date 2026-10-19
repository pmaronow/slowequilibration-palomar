-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Hahn
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.Linarith

/-!
# Event testing and the two-parameter separation reduction

This file uses genuine `MeasureTheory.Measure` and `TendstoInMeasure`.
`totalVariation` is the manuscript's normalization: the supremum, over
measurable events, of the absolute difference of their probabilities.

Hahn decomposition proves total-variation contraction for arbitrary Markov
kernels. For actual kernel semigroups, both total variation and relative
entropy are antitone, and event testing gives separation on the entire
time interval. The construction of the Langevin process is not asserted
here. The KL contraction result uses Mathlib's standard divergence.

`testing_band_union` formalizes Lemma `lem:red-test`. Its capture hypothesis
is the epsilon/eventual formulation of the manuscript's two-parameter
expected-complement-mass limit. In particular, its window is selected
before the dimension tends to infinity.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace SlowEquilibration

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]

/-- Total variation in the event-supremum normalization, on actual measures. -/
noncomputable def totalVariation (μ ν : Measure α) : ℝ :=
  sSup {r : ℝ | ∃ B : Set α, MeasurableSet B ∧ r = |μ.real B - ν.real B|}

private theorem eventDifferences_bddAbove (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    BddAbove {r : ℝ | ∃ B : Set α, MeasurableSet B ∧ r = |μ.real B - ν.real B|} := by
  refine ⟨1, ?_⟩
  rintro r ⟨B, _, rfl⟩
  have hμ := measureReal_nonneg (μ := μ) (s := B)
  have hν := measureReal_nonneg (μ := ν) (s := B)
  have hμ' := measureReal_le_one (μ := μ) (s := B)
  have hν' := measureReal_le_one (μ := ν) (s := B)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Each measurable event tests total variation. -/
theorem event_difference_le_totalVariation (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : Set α} (hB : MeasurableSet B) :
    |μ.real B - ν.real B| ≤ totalVariation μ ν := by
  exact le_csSup (eventDifferences_bddAbove μ ν) ⟨B, hB, rfl⟩

theorem totalVariation_nonneg (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ totalVariation μ ν := by
  simpa using event_difference_le_totalVariation μ ν MeasurableSet.empty

theorem totalVariation_le_one (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    totalVariation μ ν ≤ 1 := by
  apply csSup_le
  · exact ⟨0, ∅, MeasurableSet.empty, by simp⟩
  · rintro r ⟨B, _, rfl⟩
    have hμ := measureReal_nonneg (μ := μ) (s := B)
    have hν := measureReal_nonneg (μ := ν) (s := B)
    have hμ' := measureReal_le_one (μ := μ) (s := B)
    have hν' := measureReal_le_one (μ := ν) (s := B)
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem totalVariation_symm (μ ν : Measure α) :
    totalVariation μ ν = totalVariation ν μ := by
  unfold totalVariation
  simp_rw [abs_sub_comm]

/-- Deterministic data processing for event-supremum total variation. -/
theorem totalVariation_map_le {β : Type*} [MeasurableSpace β]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {g : α → β} (hg : Measurable g) :
    totalVariation (μ.map g) (ν.map g) ≤ totalVariation μ ν := by
  apply csSup_le
  · exact ⟨0, ∅, MeasurableSet.empty, by simp⟩
  · rintro r ⟨B, hB, rfl⟩
    have hμ : (μ.map g).real B = μ.real (g ⁻¹' B) := by
      simp [Measure.real, Measure.map_apply hg hB]
    have hν : (ν.map g).real B = ν.real (g ⁻¹' B) := by
      simp [Measure.real, Measure.map_apply hg hB]
    rw [hμ, hν]
    exact event_difference_le_totalVariation μ ν (hg hB)

/-- Invariance of total variation under a measurable equivalence. This is
the deterministic coordinate-change step used in the rotation reductions. -/
theorem totalVariation_map_measurableEquiv {β : Type*} [MeasurableSpace β]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (g : α ≃ᵐ β) :
    totalVariation (μ.map g) (ν.map g) = totalVariation μ ν := by
  apply le_antisymm
  · exact totalVariation_map_le μ ν g.measurable
  · have h := totalVariation_map_le (μ.map g) (ν.map g) g.symm.measurable
    simpa [Measure.map_map g.symm.measurable g.measurable, Function.comp_def] using h

private lemma integrable_unit_bounded (μ : Measure α) [IsFiniteMeasure μ]
    {u : α → ℝ} (hu : Measurable u) (hu0 : ∀ x, 0 ≤ u x) (hu1 : ∀ x, u x ≤ 1) :
    Integrable u μ := by
  apply (integrable_const (μ := μ) (1 : ℝ)).mono' hu.aestronglyMeasurable
  filter_upwards [] with x
  simpa [Real.norm_eq_abs, abs_of_nonneg (hu0 x)] using hu1 x

private lemma bounded_test_upper (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {u : α → ℝ} (hu : Measurable u) (hu0 : ∀ x, 0 ≤ u x) (hu1 : ∀ x, u x ≤ 1) :
    (∫ x, u x ∂μ) - (∫ x, u x ∂ν) ≤ totalVariation μ ν := by
  obtain ⟨A, hA, hpos, hneg⟩ :=
    SignedMeasure.exists_compl_positive_negative (μ.toSignedMeasure - ν.toSignedMeasure)
  have hpos' : ν.restrict A ≤ μ.restrict A := by
    apply (Measure.toSignedMeasure_le_toSignedMeasure_iff _ _).mp
    have hp : (0 : SignedMeasure α) ≤
        (μ.toSignedMeasure - ν.toSignedMeasure).restrict A := by
      simpa using hpos
    rw [VectorMeasure.restrict_sub, VectorMeasure.restrict_toSignedMeasure hA,
      VectorMeasure.restrict_toSignedMeasure hA] at hp
    exact sub_nonneg.mp hp
  have hneg' : μ.restrict Aᶜ ≤ ν.restrict Aᶜ := by
    apply (Measure.toSignedMeasure_le_toSignedMeasure_iff _ _).mp
    have hn : (μ.toSignedMeasure - ν.toSignedMeasure).restrict Aᶜ ≤
        (0 : SignedMeasure α) := by
      simpa using hneg
    rw [VectorMeasure.restrict_sub, VectorMeasure.restrict_toSignedMeasure hA.compl,
      VectorMeasure.restrict_toSignedMeasure hA.compl] at hn
    exact sub_nonpos.mp hn
  have huintμ := integrable_unit_bounded μ hu hu0 hu1
  have huintν := integrable_unit_bounded ν hu hu0 hu1
  have hiμ : Integrable u (μ.restrict A) := huintμ.mono_measure (Measure.restrict_le_self)
  have hiν : Integrable u (ν.restrict A) := huintν.mono_measure (Measure.restrict_le_self)
  have hu' : Measurable (fun x => 1 - u x) := measurable_const.sub hu
  have hcomp0 : ∀ x, 0 ≤ 1 - u x := fun x => sub_nonneg.mpr (hu1 x)
  have hcomp1 : ∀ x, 1 - u x ≤ 1 := fun x => by linarith [hu0 x]
  have hcomp := integral_mono_measure hpos'
    (Eventually.of_forall hcomp0)
    (integrable_unit_bounded (μ.restrict A) hu' hcomp0 hcomp1)
  rw [integral_sub (integrable_const _) hiν,
    integral_sub (integrable_const _) hiμ] at hcomp
  simp only [integral_const, smul_eq_mul, mul_one,
    measureReal_restrict_apply_univ] at hcomp
  have hnegative := integral_mono_measure hneg' (Eventually.of_forall hu0)
    (huintν.mono_measure Measure.restrict_le_self)
  have hsplitμ := integral_add_compl hA huintμ
  have hsplitν := integral_add_compl hA huintν
  have htest := event_difference_le_totalVariation μ ν hA
  have habs := le_abs_self (μ.real A - ν.real A)
  linarith

lemma bounded_test_difference (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {u : α → ℝ} (hu : Measurable u) (hu0 : ∀ x, 0 ≤ u x) (hu1 : ∀ x, u x ≤ 1) :
    |(∫ x, u x ∂μ) - (∫ x, u x ∂ν)| ≤ totalVariation μ ν := by
  apply abs_le.mpr
  constructor
  · have h := bounded_test_upper ν μ hu hu0 hu1
    rw [totalVariation_symm ν μ] at h
    linarith
  · exact bounded_test_upper μ ν hu hu0 hu1

lemma totalVariation_kernel_contraction {β : Type*} [MeasurableSpace β]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : Kernel α β) [IsMarkovKernel K] :
    totalVariation (K ∘ₘ μ) (K ∘ₘ ν) ≤ totalVariation μ ν := by
  apply csSup_le
  · exact ⟨0, ∅, MeasurableSet.empty, by simp⟩
  · rintro r ⟨B, hB, rfl⟩
    have hu : Measurable (fun x => (K x).real B) :=
      (K.measurable_coe hB).ennreal_toReal
    have hμ : (K ∘ₘ μ).real B = ∫ x, (K x).real B ∂μ := by
      rw [Measure.real, Measure.bind_apply hB K.aemeasurable]
      exact (integral_toReal (K.measurable_coe hB).aemeasurable
        (Eventually.of_forall (fun x => measure_lt_top (K x) B))).symm
    have hν : (K ∘ₘ ν).real B = ∫ x, (K x).real B ∂ν := by
      rw [Measure.real, Measure.bind_apply hB K.aemeasurable]
      exact (integral_toReal (K.measurable_coe hB).aemeasurable
        (Eventually.of_forall (fun x => measure_lt_top (K x) B))).symm
    rw [hμ, hν]
    exact bounded_test_difference μ ν hu (fun x => measureReal_nonneg)
      (fun x => measureReal_le_one)


/-- The fixed-time event-testing inequality in `eq:pre-endpoint-test`. -/
theorem separation_from_event (ρ π : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure π]
    {B : Set α} (hB : MeasurableSet B) :
    1 - π.real Bᶜ - ρ.real B ≤ totalVariation ρ π := by
  have hcomp := probReal_add_probReal_compl (μ := π) hB
  have htest := event_difference_le_totalVariation ρ π hB
  have habs := neg_le_abs (ρ.real B - π.real B)
  linarith

/-- A common-tolerance version: a nearly full equilibrium event with small
endpoint mass forces nearly maximal total variation. -/
theorem separation_from_event_bounds (ρ π : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure π]
    {B : Set α} (hB : MeasurableSet B) {η a : ℝ}
    (hπ : π.real Bᶜ ≤ η) (hρ : ρ.real B ≤ a) :
    1 - η - a ≤ totalVariation ρ π := by
  have := separation_from_event ρ π hB
  linarith

/-- Deterministic endpoint part of `prop:pre-endpoint`: the antitonicity
premise is precisely the consequence of kernel contraction used in the paper. -/
theorem endpoint_separation (ρ : ℝ → Measure α) (π : Measure α)
    [∀ t, IsProbabilityMeasure (ρ t)] [IsProbabilityMeasure π]
    {T : ℝ} (hT : 0 ≤ T)
    (hanti : AntitoneOn (fun t => totalVariation (ρ t) π) (Ici 0))
    {B : Set α} (hB : MeasurableSet B) :
    ∀ t ∈ Icc 0 T,
      1 - π.real Bᶜ - (ρ T).real B ≤ totalVariation (ρ t) π := by
  intro t ht
  exact (separation_from_event (ρ T) π hB).trans
    (hanti ht.1 hT ht.2)

/-- The infimum over the entire time interval is its endpoint value whenever
contraction has supplied antitonicity. -/
theorem endpoint_infimum (ρ : ℝ → Measure α) (π : Measure α)
    [∀ t, IsProbabilityMeasure (ρ t)] [IsProbabilityMeasure π]
    {T : ℝ} (hT : 0 ≤ T)
    (hanti : AntitoneOn (fun t => totalVariation (ρ t) π) (Ici 0)) :
    sInf ((fun t => totalVariation (ρ t) π) '' Icc 0 T) =
      totalVariation (ρ T) π := by
  apply le_antisymm
  · apply csInf_le
    · refine ⟨0, ?_⟩
      rintro r ⟨t, _, rfl⟩
      exact totalVariation_nonneg (ρ t) π
    · exact ⟨T, ⟨hT, le_rfl⟩, rfl⟩
  · apply le_csInf
    · exact ⟨totalVariation (ρ T) π, T, ⟨hT, le_rfl⟩, rfl⟩
    · rintro r ⟨t, ht, rfl⟩
      exact hanti ht.1 hT ht.2

/-- Relative-entropy kernel contraction in `lem:pre-contraction`, with the
standard Mathlib KL divergence (valued in `ENNReal`). -/
theorem relativeEntropy_kernel_contraction {β : Type*} [MeasurableSpace β]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : Kernel α β) [IsMarkovKernel K] :
    InformationTheory.klDiv (K ∘ₘ μ) (K ∘ₘ ν) ≤ InformationTheory.klDiv μ ν :=
  InformationTheory.klDiv_comp_right_le μ ν K

noncomputable def eventIndicator (B : Set α) : α → Bool := by
  classical
  exact B.piecewise (fun _ => true) (fun _ => false)

lemma measurable_eventIndicator {B : Set α} (hB : MeasurableSet B) :
    Measurable (eventIndicator B) := by
  classical
  exact Measurable.piecewise hB measurable_const measurable_const

omit [MeasurableSpace α] in
lemma eventIndicator_preimage_true (B : Set α) :
    eventIndicator B ⁻¹' {true} = B := by
  classical
  ext x
  simp [eventIndicator, Set.piecewise]

lemma eventIndicator_law_true (μ : Measure α) {B : Set α} (hB : MeasurableSet B) :
    (μ.map (eventIndicator B)) {true} = μ B := by
  rw [Measure.map_apply (measurable_eventIndicator hB) (measurableSet_singleton _)]
  rw [eventIndicator_preimage_true]

/-- The first inequality in `lem:pre-binary`: mapping to the event indicator
cannot increase the standard measure-theoretic relative entropy. -/
theorem binary_relativeEntropy_data_processing (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : Set α} (hB : MeasurableSet B) :
    InformationTheory.klDiv (μ.map (eventIndicator B)) (ν.map (eventIndicator B)) ≤
      InformationTheory.klDiv μ ν :=
  InformationTheory.klDiv_map_le μ ν (measurable_eventIndicator hB)

/-- The zero-reference-mass conclusion of `lem:pre-binary`. -/
theorem event_null_of_finite_relativeEntropy (μ ν : Measure α)
    (hKL : InformationTheory.klDiv μ ν ≠ ∞) {B : Set α} (hν : ν B = 0) : μ B = 0 :=
  (InformationTheory.klDiv_ne_top_iff.mp hKL).1 hν

/-- The zero-endpoint-mass part of `prop:pre-endpoint` is preserved under a
Markov kernel when the initial relative entropy is finite. -/
theorem endpoint_null_of_finite_relativeEntropy {β : Type*} [MeasurableSpace β]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : Kernel α β) [IsMarkovKernel K]
    (hKL : InformationTheory.klDiv μ ν ≠ ∞)
    {B : Set β} (hν : (K ∘ₘ ν) B = 0) : (K ∘ₘ μ) B = 0 := by
  apply event_null_of_finite_relativeEntropy (K ∘ₘ μ) (K ∘ₘ ν) _ hν
  exact ne_of_lt ((relativeEntropy_kernel_contraction μ ν K).trans_lt
    (lt_top_iff_ne_top.mpr hKL))

/-- Relative entropy is antitone along an actual Markov kernel semigroup
with invariant probability measure, the entropy part of `lem:pre-contraction`. -/
theorem relativeEntropy_semigroup_antitone (P : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (P t)]
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hcomp : ∀ s t, P (s + t) = P s ∘ₖ P t)
    (hinv : ∀ t, P t ∘ₘ π = π) :
    Antitone (fun t => InformationTheory.klDiv (P t ∘ₘ μ) π) := by
  intro s t hst
  have htime : (t - s) + s = t := tsub_add_cancel_of_le hst
  calc
    InformationTheory.klDiv (P t ∘ₘ μ) π =
        InformationTheory.klDiv (P (t - s) ∘ₘ (P s ∘ₘ μ)) (P (t - s) ∘ₘ π) := by
      rw [Measure.comp_assoc, ← hcomp, htime, hinv]
    _ ≤ InformationTheory.klDiv (P s ∘ₘ μ) π :=
      relativeEntropy_kernel_contraction (P s ∘ₘ μ) π (P (t - s))


/-- Total variation is antitone along an actual Markov kernel semigroup
with invariant probability measure, the TV part of `lem:pre-contraction`. -/
theorem totalVariation_semigroup_antitone (P : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (P t)]
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hcomp : ∀ s t, P (s + t) = P s ∘ₖ P t)
    (hinv : ∀ t, P t ∘ₘ π = π) :
    Antitone (fun t => totalVariation (P t ∘ₘ μ) π) := by
  intro s t hst
  have htime : (t - s) + s = t := tsub_add_cancel_of_le hst
  calc
    totalVariation (P t ∘ₘ μ) π =
        totalVariation (P (t - s) ∘ₘ (P s ∘ₘ μ)) (P (t - s) ∘ₘ π) := by
      rw [Measure.comp_assoc, ← hcomp, htime, hinv]
    _ ≤ totalVariation (P s ∘ₘ μ) π :=
      totalVariation_kernel_contraction (P s ∘ₘ μ) π (P (t - s))

/-- The TV conclusion of `prop:pre-endpoint`, for an actual Markov kernel
semigroup, using the complement mass under its invariant measure. -/
theorem markov_endpoint_separation (P : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (P t)]
    (μ π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hcomp : ∀ s t, P (s + t) = P s ∘ₖ P t)
    (hinv : ∀ t, P t ∘ₘ π = π)
    (T : ℝ≥0) {B : Set α} (hB : MeasurableSet B) :
    ∀ t ≤ T, 1 - π.real Bᶜ - (P T ∘ₘ μ).real B ≤
      totalVariation (P t ∘ₘ μ) π := by
  intro t ht
  exact (separation_from_event (P T ∘ₘ μ) π hB).trans
    (totalVariation_semigroup_antitone P μ π hcomp hinv ht)

/-- The zero-reference-endpoint-mass conclusion of `prop:pre-endpoint`,
including separation for every earlier time under finite initial entropy. -/
theorem markov_endpoint_separation_zero (P : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (P t)]
    (μ ν π : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure π]
    (hcomp : ∀ s t, P (s + t) = P s ∘ₖ P t)
    (hinv : ∀ t, P t ∘ₘ π = π)
    (hKL : InformationTheory.klDiv μ ν ≠ ∞)
    (T : ℝ≥0) {B : Set α} (hB : MeasurableSet B)
    (hν : (P T ∘ₘ ν) B = 0) :
    ∀ t ≤ T, 1 - π.real Bᶜ ≤ totalVariation (P t ∘ₘ μ) π := by
  have hμ := endpoint_null_of_finite_relativeEntropy μ ν (P T) hKL hν
  simpa [Measure.real, hμ] using markov_endpoint_separation P μ π hcomp hinv T hB

/-- Lemma `lem:red-test`, with the capture limit expressed by eventual
smallness of the expected complement mass after selecting a fixed window.
The variables live on the original probability space; no finite model is
substituted for the disorder law. -/
theorem testing_band_union (P : Measure Ω) [IsProbabilityMeasure P]
    (Δ : ℕ → Ω → ℝ) (C E : ℕ → ℝ → Ω → ℝ)
    (hΔ : ∀ N ω, Δ N ω ≤ 1)
    (hC : ∀ N M, 0 < M → ∀ ω, 0 ≤ C N M ω)
    (hE : ∀ N M, 0 < M → ∀ ω, 0 ≤ E N M ω)
    (hCint : ∀ N M, 0 < M → Integrable (C N M) P)
    (hcapture : ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ N in atTop, (∫ ω, C N M ω ∂P) < η)
    (herror : ∀ M : ℝ, 0 < M → TendstoInMeasure P (fun N => E N M) atTop (fun _ => 0))
    (hbound : ∀ N M, 0 < M → ∀ ω, 1 - C N M ω - E N M ω ≤ Δ N ω) :
    TendstoInMeasure P Δ atTop (fun _ => 1) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun _ => ha.trans_le measureReal_nonneg)
  · intro δ hδ
    obtain ⟨M, hM, hcap⟩ := hcapture (ε * δ / 4) (by positivity)
    have herr := (tendstoInMeasure_iff_measureReal_norm.mp (herror M hM))
      (ε / 2) (by positivity)
    have herr' : ∀ᶠ N in atTop, P.real {ω | ε / 2 ≤ ‖E N M ω - 0‖} < δ / 2 :=
      (tendsto_order.mp herr).2 (δ / 2) (by positivity)
    filter_upwards [hcap, herr'] with N hcapN herrN
    have hmarkov := mul_meas_ge_le_integral_of_nonneg
      (μ := P) (Filter.Eventually.of_forall (hC N M hM)) (hCint N M hM) (ε / 2)
    have hcaptail : P.real {ω | ε / 2 ≤ C N M ω} < δ / 2 := by
      nlinarith
    have hsub : {ω | ε ≤ ‖Δ N ω - 1‖} ⊆
        {ω | ε / 2 ≤ C N M ω} ∪ {ω | ε / 2 ≤ ‖E N M ω - 0‖} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, Set.mem_union] at *
      have hnorm : ‖Δ N ω - 1‖ = 1 - Δ N ω := by
        rw [Real.norm_eq_abs, abs_of_nonpos (by linarith [hΔ N ω])]
        ring
      have hEnorm : ‖E N M ω - 0‖ = E N M ω := by
        simp [Real.norm_eq_abs, abs_of_nonneg (hE N M hM ω)]
      rw [hnorm] at hω
      rw [hEnorm]
      by_contra h
      push Not at h
      linarith [hbound N M hM ω]
    have hprob := (measureReal_mono (μ := P) hsub).trans
      (measureReal_union_le (μ := P) _ _)
    linarith

end SlowEquilibration

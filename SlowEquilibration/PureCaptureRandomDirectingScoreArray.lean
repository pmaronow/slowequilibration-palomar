-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalScoreTightness
public import SlowEquilibration.DirectingPhysicalRandomCompanions

/-! A random directing measure gives a coherent family of finite overlap
score laws. Its score-failure probabilities vanish when the directing
measure is supported on the squared-norm-Q sphere. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCaptureRandomDirectingScoreArray

open Set Filter MeasureTheory ProbabilityTheory
open PureCaptureOverlapScoreCoordinates
open PureCapturePhysicalScoreTightness
open SlowEquilibration.DirectingPhysical
open SphericalModel SphericalForm
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- Scores of the actual query-plus-block directing ensemble after
averaging over the random directing kernel. -/
def randomDirectingScoreLaw (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω H) [IsMarkovKernel G] (k T : ℕ) :
    ProbabilityMeasure (ScoreCoordinates k T) :=
  ((SlowEquilibration.DirectingPhysical.companionEnsembleLaw d G k T).toProbabilityMeasure).map
    directingScoreCoordinates

theorem randomDirectingScoreLaw_failure_mass (d : Measure Ω)
    [IsProbabilityMeasure d] (G : Kernel Ω H) [IsMarkovKernel G]
    (k T : ℕ) (Q θ : ℝ) :
    (randomDirectingScoreLaw d G k T : Measure (ScoreCoordinates k T))
        (scoreFailure Q θ) =
      (SlowEquilibration.DirectingPhysical.companionEnsembleLaw d G k T)
        (SlowEquilibration.DirectingPhysical.companionFailureEvent k Q θ T) := by
  unfold randomDirectingScoreLaw
  rw [ProbabilityMeasure.map_apply' _
    (directingScoreCoordinates_continuous.measurable.aemeasurable)
    (scoreFailure_closed Q θ).measurableSet]
  exact congrArg _ (directingFailure_eq_scoreFailure_preimage Q θ).symm

/-- The original random-directing companion extraction theorem becomes
pointwise vanishing of the same finite score-failure witness used by
the physical weak-limit argument. -/
theorem randomDirectingScoreLaw_failure_tendsto_zero (d : Measure Ω)
    [IsProbabilityMeasure d] (G : Kernel Ω H) [IsMarkovKernel G]
    (k : ℕ) {Q θ : ℝ} (hθ : 0 < θ)
    (hG : ∀ᵐ ω ∂d, ∀ᵐ v ∂G ω, ‖v‖ ^ 2 = Q) :
    Tendsto (fun T =>
      ((randomDirectingScoreLaw d G k T : Measure (ScoreCoordinates k T))
        (scoreFailure Q θ)).toReal) atTop (𝓝 0) := by
  simp_rw [randomDirectingScoreLaw_failure_mass]
  exact SlowEquilibration.DirectingPhysical.annealed_companionFailure_tendsto_zero
    d G k hθ hG

/-- At a fixed directing measure, increasing the number of independent
blocks can only decrease the probability of finding no successful block. -/
theorem directingFailure_mass_antitone (ν : Measure H) [IsProbabilityMeasure ν]
    (k : ℕ) (Q θ : ℝ) {s t : ℕ} (hst : s ≤ t) :
    (ν.prod (Measure.pi (fun _ : Fin t => Measure.pi (fun _ : Fin k => ν)))).real
      (companionFailureEvent k Q θ t) ≤
    (ν.prod (Measure.pi (fun _ : Fin s => Measure.pi (fun _ : Fin k => ν)))).real
      (companionFailureEvent k Q θ s) := by
  simp_rw [companionFailure_mass_eq_integral]
  have hmeas : Measurable (companionBlockMass ν k Q θ) :=
    companionBlockMass_measurable ν k Q θ
  have hint (T : ℕ) : Integrable (fun v : H =>
      (1 - companionBlockMass ν k Q θ v) ^ T) ν := by
    apply Integrable.of_bound ((measurable_const.sub hmeas).pow_const T).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun v => by
      have h0 : 0 ≤ companionBlockMass ν k Q θ v := measureReal_nonneg
      have h1 : companionBlockMass ν k Q θ v ≤ 1 := measureReal_le_one
      change ‖(1 - companionBlockMass ν k Q θ v) ^ T‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sub_nonneg.mpr h1) T)]
      exact pow_le_one₀ (sub_nonneg.mpr h1) (by linarith)
  apply integral_mono (hint t) (hint s)
  intro v
  have h0 : 0 ≤ companionBlockMass ν k Q θ v := measureReal_nonneg
  have h1 : companionBlockMass ν k Q θ v ≤ 1 := measureReal_le_one
  change (1 - companionBlockMass ν k Q θ v) ^ t ≤
    (1 - companionBlockMass ν k Q θ v) ^ s
  exact pow_le_pow_of_le_one (by linarith)
    (by linarith : 1 - companionBlockMass ν k Q θ v ≤ 1) hst

/-- The antitone failure law survives averaging over the random
directing kernel. -/
theorem randomDirectingFailure_mass_antitone (d : Measure Ω)
    [IsProbabilityMeasure d] (G : Kernel Ω H) [IsMarkovKernel G]
    (k : ℕ) (Q θ : ℝ) {s t : ℕ} (hst : s ≤ t) :
    (companionEnsembleLaw d G k t).real (companionFailureEvent k Q θ t) ≤
    (companionEnsembleLaw d G k s).real (companionFailureEvent k Q θ s) := by
  rw [companionEnsemble_failure_real_eq_integral,
    companionEnsemble_failure_real_eq_integral]
  have hint (T : ℕ) : Integrable (fun ω =>
      (companionEnsembleKernel G k T ω).real (companionFailureEvent k Q θ T)) d := by
    have hm : Measurable (fun ω =>
        (companionEnsembleKernel G k T ω).real (companionFailureEvent k Q θ T)) :=
      ((companionEnsembleKernel G k T).measurable_coe
        (companionFailureEvent_closed k Q θ T).measurableSet).ennreal_toReal
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
  apply integral_mono (hint t) (hint s)
  intro ω
  change (companionEnsembleKernel G k t ω).real (companionFailureEvent k Q θ t) ≤
    (companionEnsembleKernel G k s ω).real (companionFailureEvent k Q θ s)
  rw [companionEnsembleKernel_apply, companionEnsembleKernel_apply]
  exact directingFailure_mass_antitone (G ω) k Q θ hst

theorem randomDirectingScoreLaw_failure_antitone (d : Measure Ω)
    [IsProbabilityMeasure d] (G : Kernel Ω H) [IsMarkovKernel G]
    (k : ℕ) (Q θ : ℝ) {s t : ℕ} (hst : s ≤ t) :
    ((randomDirectingScoreLaw d G k t : Measure (ScoreCoordinates k t))
      (scoreFailure Q θ)).toReal ≤
    ((randomDirectingScoreLaw d G k s : Measure (ScoreCoordinates k s))
      (scoreFailure Q θ)).toReal := by
  rw [randomDirectingScoreLaw_failure_mass,
    randomDirectingScoreLaw_failure_mass]
  exact randomDirectingFailure_mass_antitone d G k Q θ hst

/-- A random directing kernel together with its probability and Markov
properties. This packages the measure-theoretic data that a
Dovbysh–Sudakov representation theorem would provide. -/
structure RandomDirectingData (Ω H : Type*) [MeasurableSpace Ω]
    [MeasurableSpace H] where
  disorderLaw : Measure Ω
  directingKernel : Kernel Ω H
  disorderProbability : IsProbabilityMeasure disorderLaw
  directingMarkov : IsMarkovKernel directingKernel

def RandomDirectingData.scoreLaw (R : RandomDirectingData Ω H)
    (k T : ℕ) : ProbabilityMeasure (ScoreCoordinates k T) := by
  let : IsProbabilityMeasure R.disorderLaw := R.disorderProbability
  let : IsMarkovKernel R.directingKernel := R.directingMarkov
  exact randomDirectingScoreLaw R.disorderLaw R.directingKernel k T

theorem RandomDirectingData.scoreLaw_failure_antitone
    (R : RandomDirectingData Ω H) (k : ℕ) (Q θ : ℝ)
    {s t : ℕ} (hst : s ≤ t) :
    ((R.scoreLaw k t : Measure (ScoreCoordinates k t)) (scoreFailure Q θ)).toReal ≤
    ((R.scoreLaw k s : Measure (ScoreCoordinates k s)) (scoreFailure Q θ)).toReal := by
  let : IsProbabilityMeasure R.disorderLaw := R.disorderProbability
  let : IsMarkovKernel R.directingKernel := R.directingMarkov
  exact randomDirectingScoreLaw_failure_antitone
    R.disorderLaw R.directingKernel k Q θ hst

theorem RandomDirectingData.scoreLaw_failure_tendsto_zero
    (R : RandomDirectingData Ω H) (k : ℕ) {Q θ : ℝ} (hθ : 0 < θ)
    (hQ : ∀ᵐ ω ∂(R.disorderLaw), ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ^ 2 = Q) :
    Tendsto (fun T =>
      ((R.scoreLaw k T : Measure (ScoreCoordinates k T)) (scoreFailure Q θ)).toReal)
        atTop (𝓝 0) := by
  let : IsProbabilityMeasure R.disorderLaw := R.disorderProbability
  let : IsMarkovKernel R.directingKernel := R.directingMarkov
  exact randomDirectingScoreLaw_failure_tendsto_zero
    R.disorderLaw R.directingKernel k hθ hQ

/-- The finite physical failure part of source Proposition 9.16, with
all compactness and weak-subsequence extraction proved. The one
remaining bridge hypothesis says each actual physical overlap-array
cluster family is the score law of a random norm-Q directing kernel. -/
theorem expectedFiniteFailure_eventually_small_of_directing_representation
    {k : ℕ} (μ : FiniteMixture) (β Q θ : ℝ) (hθ : 0 < θ)
    (hDS : ∀ x ∈ physicalScoreLawArrayLimitSet k μ β,
      ∃ R : RandomDirectingData Ω H,
        (∀ᵐ ω ∂(R.disorderLaw), ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ^ 2 = Q) ∧
        ∀ T, x T = R.scoreLaw k T)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T, ∀ᶠ n : ℕ in atTop,
      PureCapturePhysicalCoarseLimit.expectedFiniteFailure
        (n := n) (k := k) (T := T) μ β Q θ < ε := by
  apply expectedFiniteFailure_eventually_small_of_physical_array_limits μ β Q θ
    ?_ ?_ ε hε
  · intro x hx s t hst
    obtain ⟨R, _, hrepr⟩ := hDS x hx
    rw [hrepr s, hrepr t]
    exact R.scoreLaw_failure_antitone k Q θ hst
  · intro x hx
    obtain ⟨R, hQ, hrepr⟩ := hDS x hx
    simp_rw [hrepr]
    exact R.scoreLaw_failure_tendsto_zero k hθ hQ

end SlowEquilibration.PureCaptureRandomDirectingScoreArray

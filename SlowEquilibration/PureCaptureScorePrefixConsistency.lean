-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCaptureRandomDirectingScoreArray

/-! Projective consistency of the actual physical finite overlap-score
laws. The identity follows from the existing genuine IID replica-kernel
prefix theorem, and survives disorder averaging and weak closure. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCaptureScorePrefixConsistency

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCaptureOverlapScoreCoordinates
open PureCaptureScorePortmanteauTransfer
open PureCapturePhysicalScoreTightness
open PureCapturePhysicalFiniteMeasurability
open PureCapturePhysicalFiniteEnsembleTransfer
open PureCaptureRandomDirectingScoreArray
open GaussianReplicaKernel
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Forget the last companion block in a finite score record. -/
def scorePrefixStep {k T : ℕ} (c : ScoreCoordinates k (T+1)) :
    ScoreCoordinates k T :=
  ((fun b i => c.1 b.castSucc i),
    (fun b i j => c.2 b.castSucc i j))

theorem scorePrefixStep_continuous {k T : ℕ} :
    Continuous (scorePrefixStep (k := k) (T := T)) := by
  unfold scorePrefixStep
  apply Continuous.prodMk
  · apply continuous_pi
    intro b
    apply continuous_pi
    intro i
    exact (continuous_apply i).comp
      ((continuous_apply b.castSucc).comp continuous_fst)
  · apply continuous_pi
    intro b
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (continuous_apply j).comp ((continuous_apply i).comp
      ((continuous_apply b.castSucc).comp continuous_snd))

def physicalPrefixStep {N k T : ℕ} (p : PhysicalEnsemble N k (T+1)) :
    PhysicalEnsemble N k T :=
  (p.1, initial p.2)

theorem physicalPrefixStep_measurable {N k T : ℕ} :
    Measurable (physicalPrefixStep (N := N) (k := k) (T := T)) := by
  exact measurable_fst.prodMk ((initial_measurable T).comp measurable_snd)

theorem scorePrefixStep_physicalScoreCoordinates {N k T : ℕ}
    (p : PhysicalEnsemble N k (T+1)) :
    scorePrefixStep (physicalScoreCoordinates p) =
      physicalScoreCoordinates (physicalPrefixStep p) := rfl

/-- The genuine original Gibbs kernel is projectively consistent in
the companion-block count, even after retaining the distinguished query. -/
theorem physicalEnsembleKernel_map_prefixStep {n k T : ℕ}
    (μ : FiniteMixture) (β : ℝ) :
    (physicalEnsembleKernel (n := n) (k := k) (T := T+1) μ β).map
      physicalPrefixStep =
      physicalEnsembleKernel (n := n) (k := k) (T := T) μ β := by
  unfold physicalEnsembleKernel physicalPrefixStep
  let G := allDimensionGibbsKernel (N := n+2) (mixtureCoefficients μ) β
  change (G ×ₖ iid (iid G k) (T+1)).map (Prod.map id initial) =
    G ×ₖ iid (iid G k) T
  rw [← Kernel.map_prod_map G (iid (iid G k) (T+1)) measurable_id (initial_measurable T)]
  rw [Kernel.map_id, iid_map_initial]

theorem annealedPhysicalEnsembleLaw_map_prefixStep {n k T : ℕ}
    (μ : FiniteMixture) (β : ℝ) :
    (annealedPhysicalEnsembleLaw (n := n) (k := k) (T := T+1) μ β).map
      physicalPrefixStep =
      annealedPhysicalEnsembleLaw (n := n) (k := k) (T := T) μ β := by
  unfold annealedPhysicalEnsembleLaw
  rw [Measure.map_comp _ _ physicalPrefixStep_measurable]
  rw [physicalEnsembleKernel_map_prefixStep]

theorem annealedPhysicalScoreLaw_map_prefixStep {n k T : ℕ}
    (μ : FiniteMixture) (β : ℝ) :
    (annealedPhysicalScoreLaw (n := n) (k := k) (T := T+1) μ β).map
      scorePrefixStep =
      annealedPhysicalScoreLaw (n := n) (k := k) (T := T) μ β := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((annealedPhysicalEnsembleLaw (n := n) (k := k) (T := T+1) μ β).map
    physicalScoreCoordinates).map scorePrefixStep =
    (annealedPhysicalEnsembleLaw (n := n) (k := k) (T := T) μ β).map
      physicalScoreCoordinates
  rw [Measure.map_map scorePrefixStep_continuous.measurable
    physicalScoreCoordinates_continuous.measurable]
  have hcomp : (scorePrefixStep (k := k) (T := T)) ∘
      (physicalScoreCoordinates (N := n+2) (k := k) (T := T+1)) =
      (physicalScoreCoordinates (N := n+2) (k := k) (T := T)) ∘
        physicalPrefixStep := by
    funext p
    exact scorePrefixStep_physicalScoreCoordinates p
  rw [hcomp, ← Measure.map_map physicalScoreCoordinates_continuous.measurable
    physicalPrefixStep_measurable]
  rw [annealedPhysicalEnsembleLaw_map_prefixStep]

def consistentScoreLawArrays (k : ℕ) : Set (ScoreLawArray k) :=
  {x | ∀ T, (x (T+1)).map scorePrefixStep = x T}

theorem consistentScoreLawArrays_closed (k : ℕ) :
    IsClosed (consistentScoreLawArrays k) := by
  unfold consistentScoreLawArrays
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro T
  exact isClosed_eq
    ((ProbabilityMeasure.continuous_map scorePrefixStep_continuous).comp
      (continuous_apply (T+1)))
    (continuous_apply T)

theorem physicalScoreLawArray_consistent (k : ℕ)
    (μ : FiniteMixture) (β : ℝ) (n : ℕ) :
    annealedPhysicalScoreLawArray k μ β n ∈ consistentScoreLawArrays k := by
  intro T
  exact annealedPhysicalScoreLaw_map_prefixStep μ β

/-- All simultaneous physical weak-limit families remain projectively
consistent. This is a closed condition on the product of finite-law
spaces, so it survives passage to the compact weak closure. -/
theorem physicalScoreLawArrayLimitSet_consistent (k : ℕ)
    (μ : FiniteMixture) (β : ℝ)
    {x : ScoreLawArray k} (hx : x ∈ physicalScoreLawArrayLimitSet k μ β) :
    x ∈ consistentScoreLawArrays k := by
  apply closure_minimal _ (consistentScoreLawArrays_closed k) hx
  rintro x ⟨n, rfl⟩
  exact physicalScoreLawArray_consistent k μ β n

theorem scoreFailure_step_subset {k T : ℕ} (Q θ : ℝ) :
    scoreFailure (k := k) (T := T+1) Q θ ⊆
      scorePrefixStep ⁻¹' scoreFailure (k := k) (T := T) Q θ := by
  intro c hc
  change ∀ b : Fin T, ¬scoreBlockSuccess Q θ (scorePrefixStep c) b
  intro b
  exact hc b.castSucc

theorem consistentScoreLaw_failure_step_le {k : ℕ} (Q θ : ℝ)
    {x : ScoreLawArray k} (hx : x ∈ consistentScoreLawArrays k) (T : ℕ) :
    ((x (T+1) : Measure (ScoreCoordinates k (T+1)))
      (scoreFailure Q θ)).toReal ≤
    ((x T : Measure (ScoreCoordinates k T)) (scoreFailure Q θ)).toReal := by
  have hmass : (x (T+1) : Measure (ScoreCoordinates k (T+1)))
      (scorePrefixStep ⁻¹' scoreFailure (k := k) (T := T) Q θ) =
      (x T : Measure (ScoreCoordinates k T)) (scoreFailure Q θ) := by
    rw [← hx T]
    exact (ProbabilityMeasure.map_apply' _
      scorePrefixStep_continuous.measurable.aemeasurable
      (scoreFailure_closed Q θ).measurableSet).symm
  have hle : (x (T+1) : Measure (ScoreCoordinates k (T+1)))
      (scoreFailure Q θ) ≤
      (x T : Measure (ScoreCoordinates k T)) (scoreFailure Q θ) := by
    calc
      _ ≤ (x (T+1) : Measure (ScoreCoordinates k (T+1)))
        (scorePrefixStep ⁻¹' scoreFailure (k := k) (T := T) Q θ) :=
          measure_mono (scoreFailure_step_subset Q θ)
      _ = _ := hmass
  exact ENNReal.toReal_mono (measure_ne_top _ _) hle

/-- The closed failure probabilities are automatically antitone on
every actual physical weak-limit family; no separate monotonicity
hypothesis is needed. -/
theorem physicalScoreLawArrayLimitSet_failure_antitone {k : ℕ}
    (μ : FiniteMixture) (β Q θ : ℝ)
    {x : ScoreLawArray k} (hx : x ∈ physicalScoreLawArrayLimitSet k μ β)
    {s t : ℕ} (hst : s ≤ t) :
    ((x t : Measure (ScoreCoordinates k t)) (scoreFailure Q θ)).toReal ≤
    ((x s : Measure (ScoreCoordinates k s)) (scoreFailure Q θ)).toReal := by
  apply antitone_nat_of_succ_le (f := fun T =>
    ((x T : Measure (ScoreCoordinates k T)) (scoreFailure Q θ)).toReal) ?_ hst
  intro T
  exact consistentScoreLaw_failure_step_le Q θ
    (physicalScoreLawArrayLimitSet_consistent k μ β hx) T

/-- After projective consistency, pointwise companion extraction on
physical array limits is the only remaining limiting input for the
finite failure estimate. -/
theorem expectedFiniteFailure_eventually_small_of_pointwise_physical_limits
    {k : ℕ} (μ : FiniteMixture) (β Q θ : ℝ)
    (hpoint : ∀ x ∈ physicalScoreLawArrayLimitSet k μ β,
      Tendsto (fun T =>
        ((x T : Measure (ScoreCoordinates k T)) (scoreFailure Q θ)).toReal)
        atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T, ∀ᶠ n : ℕ in atTop,
      PureCapturePhysicalCoarseLimit.expectedFiniteFailure
        (n := n) (k := k) (T := T) μ β Q θ < ε := by
  apply expectedFiniteFailure_eventually_small_of_physical_array_limits μ β Q θ
    ?_ hpoint ε hε
  intro x hx s t hst
  exact physicalScoreLawArrayLimitSet_failure_antitone μ β Q θ hx hst

/-- Source-9.16 finite failure from the precise still-missing directing
representation, now with all physical compactness and projective
consistency discharged. -/
theorem expectedFiniteFailure_eventually_small_of_directing_representation
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    {k : ℕ} (μ : FiniteMixture) (β Q θ : ℝ) (hθ : 0 < θ)
    (hDS : ∀ x ∈ physicalScoreLawArrayLimitSet k μ β,
      ∃ R : RandomDirectingData Ω H,
        (∀ᵐ ω ∂(R.disorderLaw), ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ^ 2 = Q) ∧
        ∀ T, x T = R.scoreLaw k T)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T, ∀ᶠ n : ℕ in atTop,
      PureCapturePhysicalCoarseLimit.expectedFiniteFailure
        (n := n) (k := k) (T := T) μ β Q θ < ε := by
  apply expectedFiniteFailure_eventually_small_of_pointwise_physical_limits
    μ β Q θ ?_ ε hε
  intro x hx
  obtain ⟨R, hQ, hrepr⟩ := hDS x hx
  simp_rw [hrepr]
  exact R.scoreLaw_failure_tendsto_zero k hθ hQ

end SlowEquilibration.PureCaptureScorePrefixConsistency

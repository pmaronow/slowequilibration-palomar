-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCaptureOverlapScoreCoordinates
public import SlowEquilibration.PureCapturePhysicalCoarseLimit
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Portmanteau transfer for the fixed overlap coordinates of actual
physical and directing companion ensembles. The analytic input remains
weak convergence of the physical overlap law to a directing law. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCaptureScorePortmanteauTransfer

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalFiniteEnsembleTransfer
open PureCapturePhysicalFiniteMeasurability
open PureCapturePhysicalCoarseLimit
open PureCaptureOverlapScoreCoordinates
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The pushforward of the genuine disorder-conditioned physical Gibbs
ensemble by its overlap-score map. -/
def physicalScoreLaw {n k T : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder (n+2) μ.maxDegree) : ProbabilityMeasure (ScoreCoordinates k T) :=
  ((physicalEnsembleLaw (k := k) (T := T) μ β J).toProbabilityMeasure).map
    physicalScoreCoordinates

theorem physicalScoreLaw_failure_mass {n k T : ℕ} (μ : FiniteMixture)
    (β Q θ : ℝ) (J : Disorder (n+2) μ.maxDegree) :
    (physicalScoreLaw (k := k) (T := T) μ β J : Measure (ScoreCoordinates k T))
        (scoreFailure Q θ) =
      (physicalEnsembleLaw (k := k) (T := T) μ β J) (allBlocksFail Q θ) := by
  unfold physicalScoreLaw
  rw [ProbabilityMeasure.map_apply' _
    (physicalScoreCoordinates_continuous.measurable.aemeasurable)
    (scoreFailure_closed Q θ).measurableSet]
  exact congrArg _ (allBlocksFail_eq_scoreFailure_preimage Q θ).symm

/-- A directing law has exactly the same score coordinates and failure
event. -/
def directingScoreLaw {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H]
    {k T : ℕ} (ν : Measure H) [IsProbabilityMeasure ν] :
    ProbabilityMeasure (ScoreCoordinates k T) :=
  ((ν.prod (Measure.pi (fun _ : Fin T => Measure.pi (fun _ : Fin k => ν)))).toProbabilityMeasure).map
    directingScoreCoordinates

theorem directingScoreLaw_failure_mass {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H]
    {k T : ℕ} (ν : Measure H) [IsProbabilityMeasure ν]
    (Q θ : ℝ) :
    (directingScoreLaw (k := k) (T := T) ν : Measure (ScoreCoordinates k T))
        (scoreFailure Q θ) =
      (ν.prod (Measure.pi (fun _ : Fin T => Measure.pi (fun _ : Fin k => ν))))
        (SlowEquilibration.DirectingPhysical.companionFailureEvent k Q θ T) := by
  unfold directingScoreLaw
  rw [ProbabilityMeasure.map_apply' _
    (directingScoreCoordinates_continuous.measurable.aemeasurable)
    (scoreFailure_closed Q θ).measurableSet]
  exact congrArg _ (directingFailure_eq_scoreFailure_preimage Q θ).symm

/-- Disorder-averaged original Gibbs ensemble, formed by binding the
physical Gibbs kernel to the original Gaussian disorder law. -/
def annealedPhysicalEnsembleLaw {n k T : ℕ} (μ : FiniteMixture) (β : ℝ) :
    Measure (PhysicalEnsemble (n+2) k T) :=
  (disorderLaw (n+2) μ.maxDegree).bind
    (physicalEnsembleKernel (n := n) (k := k) (T := T) μ β)

instance annealedPhysicalEnsembleLaw_probability {n k T : ℕ}
    (μ : FiniteMixture) (β : ℝ) :
    IsProbabilityMeasure (annealedPhysicalEnsembleLaw (n := n) (k := k) (T := T) μ β) := by
  unfold annealedPhysicalEnsembleLaw
  apply isProbabilityMeasure_bind (physicalEnsembleKernel μ β).aemeasurable
  exact Filter.Eventually.of_forall fun J => by
    rw [physicalEnsembleKernel_apply]
    infer_instance

/-- Fixed-dimensional score law after averaging over the original
Gaussian disorder. -/
def annealedPhysicalScoreLaw {n k T : ℕ} (μ : FiniteMixture) (β : ℝ) :
    ProbabilityMeasure (ScoreCoordinates k T) :=
  ((annealedPhysicalEnsembleLaw (n := n) (k := k) (T := T) μ β).toProbabilityMeasure).map
    physicalScoreCoordinates

theorem annealedPhysicalScoreLaw_failure_mass {n k T : ℕ}
    (μ : FiniteMixture) (β Q θ : ℝ) :
    (annealedPhysicalScoreLaw (n := n) (k := k) (T := T) μ β :
      Measure (ScoreCoordinates k T)) (scoreFailure Q θ) =
      (annealedPhysicalEnsembleLaw (n := n) (k := k) (T := T) μ β)
        (allBlocksFail Q θ) := by
  unfold annealedPhysicalScoreLaw
  rw [ProbabilityMeasure.map_apply' _
    (physicalScoreCoordinates_continuous.measurable.aemeasurable)
    (scoreFailure_closed Q θ).measurableSet]
  exact congrArg _ (allBlocksFail_eq_scoreFailure_preimage Q θ).symm

/-- The mass of the annealed failure event is exactly the previously
defined expected finite failure probability. -/
theorem annealedPhysicalEnsembleLaw_failure_real_eq_expected {n k T : ℕ}
    (μ : FiniteMixture) (β Q θ : ℝ) :
    (annealedPhysicalEnsembleLaw (n := n) (k := k) (T := T) μ β).real
        (allBlocksFail Q θ) =
      expectedFiniteFailure (n := n) (k := k) (T := T) μ β Q θ := by
  let E : Set (PhysicalEnsemble (n+2) k T) := allBlocksFail Q θ
  let κ := physicalEnsembleKernel (n := n) (k := k) (T := T) μ β
  let d := disorderLaw (n+2) μ.maxDegree
  have hE : MeasurableSet E := allBlocksFail_measurable Q θ
  have hmeas : AEMeasurable (fun J => κ J E) d := (κ.measurable_coe hE).aemeasurable
  have hfinite : ∀ᵐ J ∂d, κ J E < ⊤ := Filter.Eventually.of_forall fun J => by
    rw [physicalEnsembleKernel_apply]
    exact lt_top_iff_ne_top.mpr (measure_ne_top _ _)
  calc
    _ = (∫⁻ J, κ J E ∂d).toReal := by
      change ((d.bind κ) E).toReal = _
      rw [Measure.bind_apply hE κ.aemeasurable]
    _ = ∫ J, (κ J E).toReal ∂d :=
      (integral_toReal hmeas hfinite).symm
    _ = expectedFiniteFailure (n := n) (k := k) (T := T) μ β Q θ := by
      dsimp only [κ, E, d, expectedFiniteFailure, Measure.real]
      simp_rw [physicalEnsembleKernel_apply]

/-- Closed score failure transfers in the favorable direction under weak
convergence, with no smoothing of overlap indicators. -/
theorem scoreFailure_limsup_le {ι : Type*} {k T : ℕ} {L : Filter ι}
    {μs : ι → ProbabilityMeasure (ScoreCoordinates k T)}
    {μ : ProbabilityMeasure (ScoreCoordinates k T)}
    (hlim : Tendsto μs L (𝓝 μ)) (Q θ : ℝ) :
    (L.limsup fun i => (μs i : Measure (ScoreCoordinates k T))
      (scoreFailure Q θ)) ≤ (μ : Measure (ScoreCoordinates k T))
      (scoreFailure Q θ) :=
  ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim
    (scoreFailure_closed Q θ)

/-- The disorder-averaged finite failure term is the real mass of the
closed failure event in the annealed score law. -/
theorem expectedFiniteFailure_eq_annealedScoreMass {n k T : ℕ}
    (μ : FiniteMixture) (β Q θ : ℝ) :
    expectedFiniteFailure (n := n) (k := k) (T := T) μ β Q θ =
      ((annealedPhysicalScoreLaw (n := n) (k := k) (T := T) μ β :
        Measure (ScoreCoordinates k T)) (scoreFailure Q θ)).toReal := by
  rw [annealedPhysicalScoreLaw_failure_mass]
  exact (annealedPhysicalEnsembleLaw_failure_real_eq_expected μ β Q θ).symm

/-- Weak convergence of the actual annealed overlap-score laws gives an
upper bound on the limsup of the original disorder-averaged Gibbs failure
probability. The limiting law may be any weak limit; its directing-measure
representation is a separate source theorem. -/
theorem expectedFiniteFailure_limsup_le_limitScoreMass {k T : ℕ}
    (μ : FiniteMixture) (β Q θ : ℝ)
    (limitLaw : ProbabilityMeasure (ScoreCoordinates k T))
    (hlim : Tendsto (fun n : ℕ =>
      annealedPhysicalScoreLaw (n := n) (k := k) (T := T) μ β) atTop (𝓝 limitLaw)) :
    (atTop.limsup fun n : ℕ => ENNReal.ofReal
      (expectedFiniteFailure (n := n) (k := k) (T := T) μ β Q θ)) ≤
      (limitLaw : Measure (ScoreCoordinates k T)) (scoreFailure Q θ) := by
  have hid (n : ℕ) : ENNReal.ofReal
      (expectedFiniteFailure (n := n) (k := k) (T := T) μ β Q θ) =
      (annealedPhysicalScoreLaw (n := n) (k := k) (T := T) μ β :
        Measure (ScoreCoordinates k T)) (scoreFailure Q θ) := by
    rw [expectedFiniteFailure_eq_annealedScoreMass]
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  calc
    (atTop.limsup fun n : ℕ => ENNReal.ofReal
      (expectedFiniteFailure (n := n) (k := k) (T := T) μ β Q θ)) =
        (atTop.limsup fun n : ℕ =>
          (annealedPhysicalScoreLaw (n := n) (k := k) (T := T) μ β :
            Measure (ScoreCoordinates k T)) (scoreFailure Q θ)) := by
        congr 1
        funext n
        exact hid n
    _ ≤ (limitLaw : Measure (ScoreCoordinates k T)) (scoreFailure Q θ) :=
      scoreFailure_limsup_le hlim Q θ

/-- When the weak limiting score law comes from an ordinary directing
measure, the bound is exactly its finite companion-failure probability. -/
theorem expectedFiniteFailure_limsup_le_directingFailure {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H]
    {k T : ℕ} (μ : FiniteMixture) (β Q θ : ℝ)
    (ν : Measure H) [IsProbabilityMeasure ν]
    (hlim : Tendsto (fun n : ℕ =>
      annealedPhysicalScoreLaw (n := n) (k := k) (T := T) μ β)
      atTop (𝓝 (directingScoreLaw (k := k) (T := T) ν))) :
    (atTop.limsup fun n : ℕ => ENNReal.ofReal
      (expectedFiniteFailure (n := n) (k := k) (T := T) μ β Q θ)) ≤
      (ν.prod (Measure.pi (fun _ : Fin T => Measure.pi (fun _ : Fin k => ν))))
        (SlowEquilibration.DirectingPhysical.companionFailureEvent k Q θ T) := by
  calc
    _ ≤ (directingScoreLaw (k := k) (T := T) ν : Measure (ScoreCoordinates k T))
      (scoreFailure Q θ) :=
        expectedFiniteFailure_limsup_le_limitScoreMass μ β Q θ _ hlim
    _ = _ := directingScoreLaw_failure_mass ν Q θ

end SlowEquilibration.PureCaptureScorePortmanteauTransfer

-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCaptureCompactFailureUniformization
public import SlowEquilibration.PureCapturePhysicalFiniteMeasurability
public import SlowEquilibration.DirectingPhysicalCompanions

/-! A common finite-dimensional overlap-coordinate space for the actual
physical Gibbs ensemble and a Dovbysh–Sudakov directing ensemble. The
failure event is closed, allowing direct Portmanteau transfer of weak
limits without smoothing the overlap score. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCaptureOverlapScoreCoordinates

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalFiniteEnsembleTransfer
open PureCapturePhysicalFiniteMeasurability
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

abbrev ScoreCoordinates (k T : ℕ) :=
  (Fin T → Fin k → ℝ) × (Fin T → Fin k → Fin k → ℝ)

def scoreBlockSuccess {k T : ℕ} (Q θ : ℝ) (c : ScoreCoordinates k T)
    (b : Fin T) : Prop :=
  (∀ i j : Fin k, i ≠ j → |c.2 b i j-Q| < θ) ∧
  (∀ i : Fin k, |c.1 b i-Q| < θ)

def scoreFailure {k T : ℕ} (Q θ : ℝ) : Set (ScoreCoordinates k T) :=
  {c | ∀ b : Fin T, ¬scoreBlockSuccess Q θ c b}

/-- The overlap-score failure event is closed in a fixed Euclidean
coordinate space, independent of the physical dimension. -/
theorem scoreFailure_closed {k T : ℕ} (Q θ : ℝ) :
    IsClosed (scoreFailure (k := k) (T := T) Q θ) := by
  have hsuccess (b : Fin T) : IsOpen
      {c : ScoreCoordinates k T | scoreBlockSuccess Q θ c b} := by
    have hpair : IsOpen {c : ScoreCoordinates k T |
        ∀ i j : Fin k, i ≠ j → |c.2 b i j-Q| < θ} := by
      simp only [Set.ofPred_forall]
      apply isOpen_iInter_of_finite
      intro i
      apply isOpen_iInter_of_finite
      intro j
      by_cases hij : i = j
      · simp [hij]
      · have hcoord : Continuous (fun c : ScoreCoordinates k T => c.2 b i j) :=
          (((continuous_apply j).comp ((continuous_apply i).comp
            ((continuous_apply b).comp continuous_snd))))
        have hopen : IsOpen {c : ScoreCoordinates k T | |c.2 b i j-Q| < θ} :=
          isOpen_lt (hcoord.sub continuous_const).abs continuous_const
        simpa only [hij, ne_eq, not_false_eq_true, iInter_true] using hopen
    have hquery : IsOpen {c : ScoreCoordinates k T |
        ∀ i : Fin k, |c.1 b i-Q| < θ} := by
      simp only [Set.ofPred_forall]
      apply isOpen_iInter_of_finite
      intro i
      have hcoord : Continuous (fun c : ScoreCoordinates k T => c.1 b i) :=
        (continuous_apply i).comp ((continuous_apply b).comp continuous_fst)
      exact isOpen_lt (hcoord.sub continuous_const).abs continuous_const
    simpa only [scoreBlockSuccess,Set.ofPred_and] using hpair.inter hquery
  unfold scoreFailure
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro b
  exact (hsuccess b).isClosed_compl

/-- The physical score uses the actual radius-square-N overlaps. -/
def physicalScoreCoordinates {N k T : ℕ}
    (p : PhysicalEnsemble N k T) : ScoreCoordinates k T :=
  ((fun b i => overlap p.1 (p.2 b i)),
    (fun b i j => if i = j then 0 else overlap (p.2 b i) (p.2 b j)))

theorem allBlocksFail_eq_scoreFailure_preimage {N k T : ℕ}
    (Q θ : ℝ) :
    allBlocksFail (N := N) (k := k) (T := T) Q θ =
      physicalScoreCoordinates ⁻¹' scoreFailure Q θ := by
  ext p
  change (∀ b : Fin T, ¬goodCompanionBlock Q θ p.1 (p.2 b)) ↔
    (∀ b : Fin T, ¬scoreBlockSuccess Q θ (physicalScoreCoordinates p) b)
  apply forall_congr'
  intro b
  apply not_congr
  unfold goodCompanionBlock scoreBlockSuccess
  constructor
  · rintro ⟨hpair, hquery⟩
    exact ⟨fun i j hij => by simpa [physicalScoreCoordinates, hij] using hpair i j hij,
      by simpa [physicalScoreCoordinates] using hquery⟩
  · rintro ⟨hpair, hquery⟩
    exact ⟨fun i j hij => by simpa [physicalScoreCoordinates, hij] using hpair i j hij,
      by simpa [physicalScoreCoordinates] using hquery⟩

theorem physicalScoreCoordinates_continuous {N k T : ℕ} :
    Continuous (physicalScoreCoordinates (N := N) (k := k) (T := T)) := by
  unfold physicalScoreCoordinates
  apply Continuous.prodMk
  · apply continuous_pi
    intro b
    apply continuous_pi
    intro i
    have hmap : Continuous (fun p : PhysicalEnsemble N k T => (p.1,p.2 b i)) :=
      continuous_fst.prodMk
        ((continuous_apply i).comp ((continuous_apply b).comp continuous_snd))
    exact overlap_joint_continuous.comp hmap
  · apply continuous_pi
    intro b
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    by_cases hij : i = j
    · simpa [hij] using
        (continuous_const : Continuous (fun _ : PhysicalEnsemble N k T => (0 : ℝ)))
    · have hmap : Continuous (fun p : PhysicalEnsemble N k T =>
          (p.2 b i,p.2 b j)) :=
        ((continuous_apply i).comp ((continuous_apply b).comp continuous_snd)).prodMk
          ((continuous_apply j).comp ((continuous_apply b).comp continuous_snd))
      simpa only [hij, ite_false, Function.comp_def] using
        overlap_joint_continuous.comp hmap

/-- The directing score uses ordinary Hilbert inner products. -/
def directingScoreCoordinates {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {k T : ℕ} (p : H × (Fin T → Fin k → H)) : ScoreCoordinates k T :=
  ((fun b i => inner ℝ p.1 (p.2 b i)),
    (fun b i j => if i = j then 0 else inner ℝ (p.2 b i) (p.2 b j)))

theorem directingFailure_eq_scoreFailure_preimage {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H]
    {k T : ℕ} (Q θ : ℝ) :
    SlowEquilibration.DirectingPhysical.companionFailureEvent
      (H := H) k Q θ T =
      directingScoreCoordinates ⁻¹' scoreFailure Q θ := by
  ext p
  simp only [SlowEquilibration.DirectingPhysical.companionFailureEvent,
    SlowEquilibration.DirectingPhysical.pointedEquilateralEvent,
    SlowEquilibration.DirectingPhysical.equilateralEvent,
    scoreFailure,scoreBlockSuccess,directingScoreCoordinates,
    Set.mem_preimage,Set.mem_ofPred_eq,Set.mem_inter_iff]
  apply forall_congr'
  intro b
  apply not_congr
  apply and_congr
  · apply forall_congr'
    intro i
    apply forall_congr'
    intro j
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  · rfl

theorem directingScoreCoordinates_continuous {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {k T : ℕ} :
    Continuous (directingScoreCoordinates (H := H) (k := k) (T := T)) := by
  unfold directingScoreCoordinates
  apply Continuous.prodMk
  · apply continuous_pi
    intro b
    apply continuous_pi
    intro i
    exact continuous_fst.inner
      ((continuous_apply i).comp ((continuous_apply b).comp continuous_snd))
  · apply continuous_pi
    intro b
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    by_cases hij : i = j
    · simpa [hij] using
        (continuous_const : Continuous (fun _ : H × (Fin T → Fin k → H) => (0 : ℝ)))
    · simpa [hij] using
        (((continuous_apply i).comp ((continuous_apply b).comp continuous_snd)).inner
          ((continuous_apply j).comp ((continuous_apply b).comp continuous_snd)))

end SlowEquilibration.PureCaptureOverlapScoreCoordinates

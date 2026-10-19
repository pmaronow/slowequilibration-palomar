-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCaptureScorePortmanteauTransfer

/-! A single compact weak-limit bridge for the physical source-9.16
coarse-cover argument. It uses the exact same closed finite overlap-score
failure witness for compact uniformization and for Portmanteau transfer
back to the original disorder-averaged Gibbs ensemble. The hypotheses
isolate the still-needed array-limit and directing-representation steps. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCaptureConditionalCoarseWeakLimit

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCaptureOverlapScoreCoordinates
open PureCaptureScorePortmanteauTransfer
open PureCaptureCompactFailureUniformization
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- For each finite replica count, the mass of the closed score-failure
event is upper semicontinuous as a function of its probability law. -/
theorem scoreFailure_mass_upperSemicontinuous {k T : ℕ} (Q θ : ℝ) :
    UpperSemicontinuous (fun ν : ProbabilityMeasure (ScoreCoordinates k T) =>
      (ν : Measure (ScoreCoordinates k T)) (scoreFailure Q θ)) := by
  rw [upperSemicontinuous_iff_limsup_le]
  intro ν
  exact ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
    (μs := id) tendsto_id (scoreFailure_closed Q θ)

/-- Real-valued failure mass has an open strict sublevel set. -/
theorem scoreFailure_realMass_sublevel_open {k T : ℕ} (Q θ ε : ℝ) :
    IsOpen {ν : ProbabilityMeasure (ScoreCoordinates k T) |
      ((ν : Measure (ScoreCoordinates k T)) (scoreFailure Q θ)).toReal < ε} := by
  have hopen := (scoreFailure_mass_upperSemicontinuous (k := k) (T := T) Q θ)
    |>.isOpen_preimage (ENNReal.ofReal ε)
  convert hopen using 1
  ext ν
  exact (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top _ _)).symm

/-- A compact family of possible limiting score laws, with pointwise
finite-block companion extraction, admits one block count that works
uniformly over that family. -/
theorem compact_uniform_scoreFailure {X : Type*} [TopologicalSpace X]
    {k : ℕ} (Q θ : ℝ) (K : Set X) (hK : IsCompact K)
    (limitScoreLaw : (T : ℕ) → X → ProbabilityMeasure (ScoreCoordinates k T))
    (hcontinuous : ∀ T, Continuous (limitScoreLaw T))
    (hanti : ∀ {s t : ℕ}, s ≤ t → ∀ x,
      ((limitScoreLaw t x : Measure (ScoreCoordinates k t))
        (scoreFailure Q θ)).toReal ≤
      ((limitScoreLaw s x : Measure (ScoreCoordinates k s))
        (scoreFailure Q θ)).toReal)
    (hpoint : ∀ x ∈ K, Tendsto (fun T =>
      ((limitScoreLaw T x : Measure (ScoreCoordinates k T))
        (scoreFailure Q θ)).toReal) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T, ∀ x ∈ K,
      ((limitScoreLaw T x : Measure (ScoreCoordinates k T))
        (scoreFailure Q θ)).toReal < ε := by
  let f : ℕ → X → ℝ := fun T x =>
    ((limitScoreLaw T x : Measure (ScoreCoordinates k T))
      (scoreFailure Q θ)).toReal
  apply compact_uniform_tendsto_zero K hK f hanti ?_ hpoint ε hε
  intro δ _ T
  exact (scoreFailure_realMass_sublevel_open (k := k) (T := T) Q θ δ).preimage
    (hcontinuous T)

/-- Conditional source-9.16 failure estimate. Weak limits are represented
by a compact family of continuous finite-score laws, their failure
probabilities decrease with more independent blocks, and they vanish
pointwise. The conclusion concerns the genuine annealed Gibbs failure
probability appearing in the physical coarse-cover inequality. -/
theorem expectedFiniteFailure_eventually_small_of_compact_weak_limits
    {X : Type*} [TopologicalSpace X] {k : ℕ}
    (μ : FiniteMixture) (β Q θ : ℝ) (K : Set X) (hK : IsCompact K)
    (limitScoreLaw : (T : ℕ) → X → ProbabilityMeasure (ScoreCoordinates k T))
    (hcontinuous : ∀ T, Continuous (limitScoreLaw T))
    (hanti : ∀ {s t : ℕ}, s ≤ t → ∀ x,
      ((limitScoreLaw t x : Measure (ScoreCoordinates k t))
        (scoreFailure Q θ)).toReal ≤
      ((limitScoreLaw s x : Measure (ScoreCoordinates k s))
        (scoreFailure Q θ)).toReal)
    (hpoint : ∀ x ∈ K, Tendsto (fun T =>
      ((limitScoreLaw T x : Measure (ScoreCoordinates k T))
        (scoreFailure Q θ)).toReal) atTop (𝓝 0))
    (hweak : ∀ T, ∃ x ∈ K, Tendsto (fun n : ℕ =>
      annealedPhysicalScoreLaw (n := n) (k := k) (T := T) μ β)
      atTop (𝓝 (limitScoreLaw T x)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T, ∀ᶠ n : ℕ in atTop,
      PureCapturePhysicalCoarseLimit.expectedFiniteFailure
        (n := n) (k := k) (T := T) μ β Q θ < ε := by
  obtain ⟨T, hT⟩ := compact_uniform_scoreFailure Q θ K hK limitScoreLaw
    hcontinuous hanti hpoint ε hε
  obtain ⟨x, hx, hlim⟩ := hweak T
  have hlimit : ((limitScoreLaw T x : Measure (ScoreCoordinates k T))
      (scoreFailure Q θ)) < ENNReal.ofReal ε :=
    (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top _ _)).2 (hT x hx)
  have hlimsup := expectedFiniteFailure_limsup_le_limitScoreMass μ β Q θ
    (limitScoreLaw T x) hlim
  have heventually := eventually_lt_of_limsup_lt (lt_of_le_of_lt hlimsup hlimit)
  refine ⟨T, ?_⟩
  filter_upwards [heventually] with n hn
  exact (ENNReal.ofReal_lt_ofReal_iff hε).1 hn

/-- Sequential compactness can replace full-sequence weak convergence.
It suffices that every subsequence of the actual annealed score laws has
a further subsequence converging to one of the compact family's score
laws. This is the form needed when the overlap array has many possible
limiting directing measures. -/
theorem expectedFiniteFailure_eventually_small_of_compact_cluster_limits
    {X : Type*} [TopologicalSpace X] {k : ℕ}
    (μ : FiniteMixture) (β Q θ : ℝ) (K : Set X) (hK : IsCompact K)
    (limitScoreLaw : (T : ℕ) → X → ProbabilityMeasure (ScoreCoordinates k T))
    (hcontinuous : ∀ T, Continuous (limitScoreLaw T))
    (hanti : ∀ {s t : ℕ}, s ≤ t → ∀ x,
      ((limitScoreLaw t x : Measure (ScoreCoordinates k t))
        (scoreFailure Q θ)).toReal ≤
      ((limitScoreLaw s x : Measure (ScoreCoordinates k s))
        (scoreFailure Q θ)).toReal)
    (hpoint : ∀ x ∈ K, Tendsto (fun T =>
      ((limitScoreLaw T x : Measure (ScoreCoordinates k T))
        (scoreFailure Q θ)).toReal) atTop (𝓝 0))
    (hcluster : ∀ T (s : ℕ → ℕ), StrictMono s →
      ∃ (x : X) (t : ℕ → ℕ), x ∈ K ∧ StrictMono t ∧
        Tendsto (fun m : ℕ =>
          annealedPhysicalScoreLaw (n := s (t m)) (k := k) (T := T) μ β)
          atTop (𝓝 (limitScoreLaw T x)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T, ∀ᶠ n : ℕ in atTop,
      PureCapturePhysicalCoarseLimit.expectedFiniteFailure
        (n := n) (k := k) (T := T) μ β Q θ < ε := by
  obtain ⟨T, hT⟩ := compact_uniform_scoreFailure Q θ K hK limitScoreLaw
    hcontinuous hanti hpoint ε hε
  refine ⟨T, ?_⟩
  by_contra hnot
  have hbad (N : ℕ) : ∃ n > N,
      ε ≤ PureCapturePhysicalCoarseLimit.expectedFiniteFailure
        (n := n) (k := k) (T := T) μ β Q θ := by
    by_contra h
    push Not at h
    apply hnot
    apply Filter.eventually_atTop.2
    refine ⟨N+1, ?_⟩
    intro n hn
    exact h n (by omega)
  obtain ⟨s, hs, hsbad⟩ := Nat.exists_strictMono_subsequence hbad
  obtain ⟨x, t, hx, ht, hlim⟩ := hcluster T s hs
  have hlimit : ((limitScoreLaw T x : Measure (ScoreCoordinates k T))
      (scoreFailure Q θ)) < ENNReal.ofReal ε :=
    (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top _ _)).2 (hT x hx)
  have heventually : ∀ᶠ m : ℕ in atTop,
      (annealedPhysicalScoreLaw (n := s (t m)) (k := k) (T := T) μ β :
        Measure (ScoreCoordinates k T)) (scoreFailure Q θ) < ENNReal.ofReal ε :=
    eventually_lt_of_limsup_lt
      (lt_of_le_of_lt (scoreFailure_limsup_le hlim Q θ) hlimit)
  obtain ⟨m, hm⟩ := heventually.exists
  have hmass : (annealedPhysicalScoreLaw (n := s (t m)) (k := k) (T := T) μ β :
      Measure (ScoreCoordinates k T)) (scoreFailure Q θ) =
      ENNReal.ofReal (PureCapturePhysicalCoarseLimit.expectedFiniteFailure
        (n := s (t m)) (k := k) (T := T) μ β Q θ) := by
    rw [expectedFiniteFailure_eq_annealedScoreMass]
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  rw [hmass] at hm
  exact (not_lt_of_ge (ENNReal.ofReal_le_ofReal (hsbad (t m)))) hm

end SlowEquilibration.PureCaptureConditionalCoarseWeakLimit

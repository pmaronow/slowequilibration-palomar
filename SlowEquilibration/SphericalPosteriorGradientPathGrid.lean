-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPosteriorGradientGridTail
public import SlowEquilibration.SphericalPosteriorGradientShortCells

/-!
The Gaussian source gradient is independent of the complete posterior path.
This file turns the fixed-time tail into a finite-horizon path tail, with the
only remaining error being the genuine Brownian short-cell event.
-/
@[expose] public section
namespace SlowEquilibration.SphericalPosteriorGradientIndependence
noncomputable section
open Function MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm SphericalGaussianJet SphericalPosteriorMaps
open SphericalRotationCovariance SphericalOverlapExponential
open SphericalAging HardSphereDynamics
open scoped Topology ENNReal NNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000

/-- A hit before the horizon is detected at a grid point unless the path makes
an increment larger than half the threshold on a genuine short cell. -/
theorem hit_subset_grid_or_bad {Ω : Type*} (r : ℝ≥0 → Ω → ℝ)
    (H T : ℝ≥0) (hT : 0<T) {α : ℝ} (_hα : 0≤α) :
    {ω | ∃ t : ℝ≥0, t≤H ∧ α≤|r t ω|} ⊆
      {ω | ∃ j : Fin (gridSize H T), α/2≤|r (gridStart T j.val) ω|} ∪
        badGrid r H T (α/2) := by
  intro ω hω
  obtain ⟨t,ht,hcap⟩ := hω
  obtain ⟨j,v,hv,he,_⟩ := grid_cell_of_time H T hT t ht
  by_cases hb : ω ∈ badGrid r H T (α/2)
  · exact Or.inr hb
  · left
    refine ⟨j,?_⟩
    have hd := good_grid_cell_bound r H T (α/2) ω hb j v hv
    rw [he] at hd
    have htri := abs_add_le (r t ω-r (gridStart T j.val) ω) (r (gridStart T j.val) ω)
    rw [sub_add_cancel] at htri
    linarith

theorem hit_probability_le_grid_add_bad {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsFiniteMeasure ρ] (r : ℝ≥0 → Ω → ℝ)
    (H T : ℝ≥0) (hT : 0<T) {α : ℝ} (hα : 0≤α) :
    ρ.real {ω | ∃ t : ℝ≥0, t≤H ∧ α≤|r t ω|} ≤
      ρ.real {ω | ∃ j : Fin (gridSize H T), α/2≤|r (gridStart T j.val) ω|}+
        ρ.real (badGrid r H T (α/2)) := by
  exact (measureReal_mono (hit_subset_grid_or_bad r H T hT hα)).trans
    (measureReal_union_le _ _)

/-- Clipping only permits the auxiliary grid cells to extend beyond the
observation horizon. On every time at or before the observation horizon this
is the literal posterior path. -/
def clippedGradientScore {N : ℕ} {S : ℝ≥0}
    (G : Vector N) (p : ContinuousPath N S) (t : ℝ≥0) : ℝ :=
  gradientScore G (p ⟨min t S, ⟨zero_le, min_le_right _ _⟩⟩)

theorem clippedGradientScore_of_le {N : ℕ} {S : ℝ≥0}
    (G : Vector N) (p : ContinuousPath N S) (t : ℝ≥0) (ht : t≤S) :
    clippedGradientScore G p t=gradientScore G (p ⟨t,⟨zero_le,ht⟩⟩) := by
  simp only [clippedGradientScore,min_eq_left ht]

def mixedPosteriorOriginalGradientScore (n : ℕ) (μ : FiniteMixture)
    (Q : ℝ) (u : Vector (n+1)) (marks : EuclideanSpace ℝ (Fin 2))
    (β : ℝ) (S : ℝ≥0) (t : ℝ≥0)
    (q : EuclideanDisorder (n+1) μ.maxDegree×
      (Vector (n+1)×VectorBrownian.Space (n+1))) : ℝ :=
  clippedGradientScore
    (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q)
      (unpackDisorder q.1)) u)
    (mixedPosteriorContinuousPath n μ Q u marks β S q) t

def valuePosteriorOriginalGradientScore (n : ℕ) (μ : FiniteMixture)
    (Q : ℝ) (u : Vector (n+1)) (mark : ℝ)
    (β : ℝ) (S : ℝ≥0) (t : ℝ≥0)
    (q : EuclideanDisorder (n+1) μ.maxDegree×
      (Vector (n+1)×VectorBrownian.Space (n+1))) : ℝ :=
  clippedGradientScore
    (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q)
      (unpackDisorder q.1)) u)
    (valuePosteriorContinuousPath n μ Q u mark β S q) t

/-- A pathwise excursion of the actual mixed posterior center-gradient score
is bounded by its proved Gaussian finite-grid tail plus its Brownian
short-cell event. -/
theorem mixedPosterior_gradient_horizon_tail_le_badGrid
    (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0<Q)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ))
    (marks : EuclideanSpace ℝ (Fin 2)) (β : ℝ)
    (S H T : ℝ≥0) (_hH : H≤S) (hT : 0<T)
    {α : ℝ} (hα : 0≤α) :
    (posteriorTrajectoryLaw n μ).real
      {q | ∃ t : ℝ≥0,t≤H ∧ α≤
        |mixedPosteriorOriginalGradientScore n μ Q u marks β S t q|} ≤
      (gridSize H T:ℝ)*2*
        Real.exp (-((n+1:ℕ):ℝ)*α^2/(8*(Q*μ.xi1 Q)))+
      (posteriorTrajectoryLaw n μ).real
        (badGrid (mixedPosteriorOriginalGradientScore n μ Q u marks β S)
          H T (α/2)) := by
  let times : Fin (gridSize H T)→PathTime S :=
    fun j=>⟨min (gridStart T j.val) S,⟨zero_le,min_le_right _ _⟩⟩
  have hgrid := mixedPosterior_finiteTime_original_gradient_tail n μ hQ u hu
    marks β S times hα
  have hbase := hit_probability_le_grid_add_bad (posteriorTrajectoryLaw n μ)
    (mixedPosteriorOriginalGradientScore n μ Q u marks β S) H T hT hα
  change (posteriorTrajectoryLaw n μ).real
    {q | ∃ j : Fin (gridSize H T), α/2≤
      |mixedPosteriorOriginalGradientScore n μ Q u marks β S
        (gridStart T j.val) q|} ≤ _ at hgrid
  have hsum := add_le_add_left hgrid
    ((posteriorTrajectoryLaw n μ).real
      (badGrid (mixedPosteriorOriginalGradientScore n μ Q u marks β S) H T (α/2)))
  exact hbase.trans (by simpa only [Fintype.card_fin] using hsum)

/-- The same path bound for the source's proper-pure value posterior. -/
theorem valuePosterior_gradient_horizon_tail_le_badGrid
    (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0<Q)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ))
    (mark : ℝ) (β : ℝ)
    (S H T : ℝ≥0) (_hH : H≤S) (hT : 0<T)
    {α : ℝ} (hα : 0≤α) :
    (posteriorTrajectoryLaw n μ).real
      {q | ∃ t : ℝ≥0,t≤H ∧ α≤
        |valuePosteriorOriginalGradientScore n μ Q u mark β S t q|} ≤
      (gridSize H T:ℝ)*2*
        Real.exp (-((n+1:ℕ):ℝ)*α^2/(8*(Q*μ.xi1 Q)))+
      (posteriorTrajectoryLaw n μ).real
        (badGrid (valuePosteriorOriginalGradientScore n μ Q u mark β S)
          H T (α/2)) := by
  let times : Fin (gridSize H T)→PathTime S :=
    fun j=>⟨min (gridStart T j.val) S,⟨zero_le,min_le_right _ _⟩⟩
  have hgrid := valuePosterior_finiteTime_original_gradient_tail n μ hQ u hu
    mark β S times hα
  have hbase := hit_probability_le_grid_add_bad (posteriorTrajectoryLaw n μ)
    (valuePosteriorOriginalGradientScore n μ Q u mark β S) H T hT hα
  change (posteriorTrajectoryLaw n μ).real
    {q | ∃ j : Fin (gridSize H T), α/2≤
      |valuePosteriorOriginalGradientScore n μ Q u mark β S
        (gridStart T j.val) q|} ≤ _ at hgrid
  have hsum := add_le_add_left hgrid
    ((posteriorTrajectoryLaw n μ).real
      (badGrid (valuePosteriorOriginalGradientScore n μ Q u mark β S) H T (α/2)))
  exact hbase.trans (by simpa only [Fintype.card_fin] using hsum)

end
end SlowEquilibration.SphericalPosteriorGradientIndependence

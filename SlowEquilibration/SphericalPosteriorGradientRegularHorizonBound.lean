-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalPosteriorGradientShortCellTransfer

/-! The source's original center-gradient coordinate of the actual mixed
posterior path has a complete finite-horizon tail on the true tensor
regularity event. The two terms are the Gaussian grid tail and the
physical Brownian short-cell tail, with no supplied path-tail premise. -/
@[expose] public section
noncomputable section
open Function MeasureTheory ProbabilityTheory Set
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalGaussianJet SlowEquilibration.SphericalPosteriorMaps
open SlowEquilibration.SphericalOverlapExponential
open SlowEquilibration.SphericalMarkedWindows
open SlowEquilibration.ConditionedEntrance.PhysicalHitting
open SphericalAging SphericalAging.HardSphereDynamics
open scoped Topology ENNReal NNReal RealInnerProductSpace
namespace SlowEquilibration.SphericalPosteriorGradientIndependence
set_option autoImplicit false
set_option maxHeartbeats 500000

/-- Joint original-Gaussian/Wiener probability of a source tangent-cutoff
excursion along the literal mixed conditioned path, restricted to the
actual regularity event. The source's small fixed mesh can be chosen
after the physical cutoff radius. -/
theorem mixedPosterior_regular_gradient_horizon_tail
    (n : ℕ) (μ : FiniteMixture) (hnp : μ.minDegree < μ.maxDegree)
    (Q : ℝ) (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (u : Vector (n+1)) (hu : ‖u‖ ^ 2 = (n+1 : ℕ))
    (e k β : ℝ) (hβ : 0 ≤ β)
    {α : ℝ} (hα : 0 < α)
    (S H T : ℝ≥0) (hT : 0 < T) (hS : H + 2*T ≤ S)
    (hshort : 4*(1+β*mixedDeletedGradientConstant μ Q e k)*(T:ℝ) ≤
      α/(2*centerConstant μ Q)) :
    (posteriorTrajectoryLaw n μ).real
      {q | unpackDisorder q.1 ∈ regularDisorder ∧
        ∃ t : ℝ≥0, t ≤ H ∧ α ≤
          |mixedPosteriorOriginalGradientScore n μ Q u
            (scorePairEquiv (e,k)) β S t q|} ≤
      (gridSize H T : ℝ)*2*
        Real.exp (-((n+1 : ℕ) : ℝ)*α^2/(8*(Q*μ.xi1 Q))) +
      (gridSize H T : ℝ)*2*
        Real.exp (-((n+1 : ℕ) : ℝ)*(α/(2*centerConstant μ Q))^2/
          (16*(T:ℝ))) := by
  let r := mixedPosteriorOriginalGradientScore n μ Q u
    (scorePairEquiv (e,k)) β S
  let G : Set (EuclideanDisorder (n+1) μ.maxDegree ×
      (Vector (n+1) × VectorBrownian.Space (n+1))) :=
    {q | unpackDisorder q.1 ∈ regularDisorder}
  let A := {q | ∃ t : ℝ≥0, t ≤ H ∧ α ≤ |r t q|}
  let B := {q | ∃ j : Fin (gridSize H T),
    α/2 ≤ |r (gridStart T j.val) q|}
  let D := badGrid r H T (α/2)
  have hsub : G ∩ A ⊆ B ∪ (G ∩ D) := by
    intro q hq
    rcases (hit_subset_grid_or_bad r H T hT hα.le hq.2) with hb | hd
    · exact Or.inl hb
    · exact Or.inr ⟨hq.1,hd⟩
  have hB := mixedPosterior_finiteTime_original_gradient_tail
    n μ hQ u hu (scorePairEquiv (e,k)) β S
    (fun j : Fin (gridSize H T) =>
      ⟨min (gridStart T j.val) S,⟨zero_le,min_le_right _ _⟩⟩) hα.le
  change (posteriorTrajectoryLaw n μ).real B ≤ _ at hB
  have hD := mixedPosterior_regular_badGrid_joint_bound
    n μ hnp Q hQ hQ1 u hu e k β hβ hα S H T hT hS hshort
  change (posteriorTrajectoryLaw n μ).real (G ∩ D) ≤ _ at hD
  have h := (measureReal_mono (μ := posteriorTrajectoryLaw n μ) hsub).trans
    (measureReal_union_le B (G ∩ D))
  change (posteriorTrajectoryLaw n μ).real (G ∩ A) ≤ _ at h
  have h' := h.trans (add_le_add hB hD)
  simpa only [G,A,B,D,r,Set.inter_def,Set.mem_ofPred_eq,
    Fintype.card_fin] using h'

end SlowEquilibration.SphericalPosteriorGradientIndependence

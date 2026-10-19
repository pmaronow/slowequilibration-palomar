-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPurePosteriorGradientShortCellTransfer

/-! Finite-horizon source-gradient tail for the actual value posterior on
the intersection of original and posterior tensor regularity events. -/
@[expose] public section
namespace SlowEquilibration.SphericalPosteriorGradientIndependence
noncomputable section
open Function MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm SphericalGaussianJet SphericalPosteriorMaps
open SphericalOverlapExponential SphericalMarkedWindows
open ConditionedEntrance.PhysicalHitting
open SphericalAging HardSphereDynamics
open SlowEquilibration.PairConditionalDeterminantMoments
open SlowEquilibration.SphericalTAPPosteriorBallRegularity
open scoped Topology ENNReal NNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem valuePosterior_regular_gradient_horizon_tail
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (hQ : 0 < Q)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ)) (e β : ℝ) (hβ : 0 ≤ β)
    (K : ℝ) (hK : 0 ≤ K) {α : ℝ} (hα : 0 < α)
    (S H T : ℝ≥0) (hT : 0 < T) (hS : H+2*T ≤ S)
    (hshort : 4*(1+β*posteriorDerivativeConstant (mixtureCoefficients μ) K)*(T:ℝ) ≤
      α/(2*centerConstant μ Q)) :
    (posteriorTrajectoryLaw n μ).real
      {q | unpackDisorder q.1 ∈ regularDisorder ∧
        unpackDisorder (valuePosterior n μ Q u e q.1) ∈ sourcePosteriorOrderedRegularity K ∧
        ∃ t : ℝ≥0, t ≤ H ∧ α ≤
          |valuePosteriorOriginalGradientScore n μ Q u e β S t q|} ≤
      (gridSize H T:ℝ)*2*
        Real.exp (-((n+1:ℕ):ℝ)*α^2/(8*(Q*μ.xi1 Q))) +
      (gridSize H T:ℝ)*2*
        Real.exp (-((n+1:ℕ):ℝ)*(α/(2*centerConstant μ Q))^2/(16*(T:ℝ))) := by
  let r := valuePosteriorOriginalGradientScore n μ Q u e β S
  let G : Set (EuclideanDisorder (n+1) μ.maxDegree ×
      (Vector (n+1) × VectorBrownian.Space (n+1))) :=
    {q | unpackDisorder q.1 ∈ regularDisorder ∧
      unpackDisorder (valuePosterior n μ Q u e q.1) ∈ sourcePosteriorOrderedRegularity K}
  let A := {q | ∃ t : ℝ≥0, t ≤ H ∧ α ≤ |r t q|}
  let B := {q | ∃ j : Fin (gridSize H T), α/2 ≤ |r (gridStart T j.val) q|}
  let D := badGrid r H T (α/2)
  have hsub : G ∩ A ⊆ B ∪ (G ∩ D) := by
    intro q hq
    rcases (hit_subset_grid_or_bad r H T hT hα.le hq.2) with hb | hd
    · exact Or.inl hb
    · exact Or.inr ⟨hq.1,hd⟩
  have hB := valuePosterior_finiteTime_original_gradient_tail
    n μ hQ u hu e β S
    (fun j : Fin (gridSize H T) =>
      ⟨min (gridStart T j.val) S,⟨zero_le,min_le_right _ _⟩⟩) hα.le
  change (posteriorTrajectoryLaw n μ).real B ≤ _ at hB
  have hD := valuePosterior_regular_badGrid_joint_bound
    n μ Q u hu e K hK β hβ hα S H T hT hS hshort
  have hD' : (posteriorTrajectoryLaw n μ).real (G ∩ D) ≤
      (gridSize H T:ℝ)*2*
        Real.exp (-((n+1:ℕ):ℝ)*(α/(2*centerConstant μ Q))^2/(16*(T:ℝ))) := by
    simpa only [G,D,r,Set.inter_def,Set.mem_ofPred_eq,and_assoc] using hD
  have h := (measureReal_mono (μ := posteriorTrajectoryLaw n μ) hsub).trans
    (measureReal_union_le B (G ∩ D))
  change (posteriorTrajectoryLaw n μ).real (G ∩ A) ≤ _ at h
  have h' := h.trans (add_le_add hB hD')
  simpa only [G,A,B,D,r,Set.inter_def,Set.mem_ofPred_eq,
    Fintype.card_fin,and_assoc] using h'

end
end SlowEquilibration.SphericalPosteriorGradientIndependence

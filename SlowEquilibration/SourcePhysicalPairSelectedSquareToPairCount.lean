-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairSelectedCentralPairCount
public import SlowEquilibration.SourcePhysicalPairDecoupledSquareCollar

/-! A finite-set second-moment inequality expressed with the actual
retained ordered sphere pair count, before taking disorder expectation. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalMorse
open SphericalPairCountGluing SphericalForm
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem sourceRetainedMixedPairCount_lt_top_of_finite {n P : ℕ}
    (c : Degree P → ℝ) (J : Disorder (n+1) P)
    (ρ cut : ℝ) (K : Set (EuclideanSpace ℝ (Fin 2)))
    (κ C ε η E G : ℝ) (hfinite : (sphereCriticalSet n c J).Finite) :
    sourceRetainedMixedPairCount n c ρ cut K κ C ε η E G J < ⊤ := by
  classical
  let D : Set (Vector (n+1) × Vector (n+1)) :=
    {p | ‖p.1‖^2=(n+1:ℕ) ∧ ‖p.2‖^2=(n+1:ℕ) ∧
      |overlap p.1 p.2|<ρ ∧ surfaceGradient (field c J) p.1=0 ∧
      surfaceGradient (field c J) p.2=0}
  have hD : D.Finite := (hfinite.prod hfinite).subset (by
    intro p hp
    exact ⟨⟨hp.1,hp.2.2.2.1⟩,⟨hp.2.1,hp.2.2.2.2⟩⟩)
  have instD : Fintype D := hD.fintype
  unfold sourceRetainedMixedPairCount actualSpherePairCount
  change (∑' p : D, actualMixedPairWindowMark c K cut
    (sourceSelectionPairMark c κ C ε η E G) J p.val) < ⊤
  rw [tsum_fintype]
  apply ENNReal.sum_lt_top.mpr
  intro p hp
  have hmark : actualMixedPairWindowMark c K cut
      (sourceSelectionPairMark c κ C ε η E G) J p.val ≤ 1 := by
    unfold actualMixedPairWindowMark
    split_ifs
    · exact sourceSelectionPairMark_le_one c κ C ε η E G J p.val
    all_goals exact zero_le_one
  exact hmark.trans_lt (by simp)

theorem source_actual_selected_square_le_literal_retained_pair_count {n P : ℕ}
    (c : Degree P → ℝ) (J : Disorder (n+1) P)
    {κ C ε η E G ω δ ρ : ℝ} (hκ : 0 < κ) (hC : 0 < C)
    (hη : η ≤ sourceCriticalCollarOverlapLoss κ C) (hωG : ω < G/2)
    (hδ : 0 < δ) (hδOne : δ ≤ 1) (hε : ε < δ^2) (hδρ : δ ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin 2)))
    (hwindow : ∀ z ∈ K, E-ω ≤ z 0)
    (hfinite : (sphereCriticalSet n c J).Finite) :
    let s := (sourceSelectedScoreWindowSet_finite c J K κ C ε η E G hfinite).toFinset
    (s.card:ℝ)^2 ≤
      (sourceRetainedMixedPairCount n c ρ δ K κ C ε η E G J).toReal +
      (1+(1-ε)/(δ^2-ε))*(s.card:ℝ) := by
  classical
  let s := (sourceSelectedScoreWindowSet_finite c J K κ C ε η E G hfinite).toFinset
  have hsplit := source_actual_selected_score_window_square_bound_decoupled
    c J hκ hC hη hωG hδ hδOne hε K hwindow hfinite
  have hpair := source_selected_central_pairs_le_literal_retained_pair_count
    c J hδρ K κ C ε η E G hfinite
  have hpairFinite := sourceRetainedMixedPairCount_lt_top_of_finite c J ρ δ K
    κ C ε η E G hfinite
  have hreal := ENNReal.toReal_mono hpairFinite.ne hpair
  have hsumCast :
      (∑ u ∈ s, ((s.filter fun v => v ≠ u ∧ |overlap u v| < δ).card:ℝ)) =
      ((∑ u ∈ s, (s.filter fun v => v ≠ u ∧ |overlap u v| < δ).card : ℕ):ℝ) := by
    norm_cast
  have hcentral :
      (∑ u ∈ s, ((s.filter fun v => v ≠ u ∧ |overlap u v| < δ).card:ℝ)) ≤
      (sourceRetainedMixedPairCount n c ρ δ K κ C ε η E G J).toReal := by
    rw [hsumCast]
    simpa only [ENNReal.toReal_natCast] using hreal
  exact hsplit.trans (add_le_add_left hcentral _)

end
end SlowEquilibration.PairConditionalDeterminantMoments

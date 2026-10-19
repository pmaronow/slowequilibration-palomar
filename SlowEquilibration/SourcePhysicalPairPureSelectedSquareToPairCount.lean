-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairPureSelectedCentralPairs

/-! The pure value-window selected count squared is controlled pointwise
by the literal retained ordered-pair count and the simplex constant. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalMorse
open SphericalPairCountGluing SphericalPairMarkedWindows SphericalForm
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem sourceRetainedPurePairCount_lt_top_of_finite {n P : ℕ}
    (c : Degree P → ℝ) (J : Disorder (n+1) P)
    (ρ cut : ℝ) (I : Set ℝ) (κ C ε η E G : ℝ)
    (hfinite : (sphereCriticalSet n c J).Finite) :
    sourceRetainedPurePairCount n c ρ cut I κ C ε η E G J < ⊤ := by
  classical
  let D : Set (Vector (n+1) × Vector (n+1)) :=
    {p | ‖p.1‖^2=(n+1:ℕ) ∧ ‖p.2‖^2=(n+1:ℕ) ∧
      |overlap p.1 p.2|<ρ ∧ surfaceGradient (field c J) p.1=0 ∧
      surfaceGradient (field c J) p.2=0}
  have hD : D.Finite := (hfinite.prod hfinite).subset (by
    intro p hp
    exact ⟨⟨hp.1,hp.2.2.2.1⟩,⟨hp.2.1,hp.2.2.2.2⟩⟩)
  have instD : Fintype D := hD.fintype
  unfold sourceRetainedPurePairCount actualSpherePairCount
  change (∑' p : D, actualValuePairWindowMark c I cut
    (sourceSelectionPairMark c κ C ε η E G) J p.val) < ⊤
  rw [tsum_fintype]
  apply ENNReal.sum_lt_top.mpr
  intro p hp
  have hmark : actualValuePairWindowMark c I cut
      (sourceSelectionPairMark c κ C ε η E G) J p.val ≤ 1 := by
    unfold actualValuePairWindowMark
    split_ifs
    · exact sourceSelectionPairMark_le_one c κ C ε η E G J p.val
    all_goals exact zero_le_one
  exact hmark.trans_lt (by simp)

theorem source_actual_selected_pure_square_le_literal_retained_pair_count {n P : ℕ}
    (c : Degree P → ℝ) (J : Disorder (n+1) P)
    {κ C ε η E G ω cut ρ : ℝ} (hκ : 0 < κ) (hC : 0 < C)
    (hη : η ≤ sourceCriticalCollarOverlapLoss κ C) (hωG : ω < G/2)
    (hcut : 0 < cut) (hcutOne : cut ≤ 1) (hε : ε < cut^2)
    (hcutρ : cut ≤ ρ)
    (I : Set ℝ) (hwindow : ∀ z ∈ I, E-ω ≤ z)
    (hfinite : (sphereCriticalSet n c J).Finite) :
    let s := (sourceSelectedValueWindowSet_finite c J I κ C ε η E G
      hfinite).toFinset
    (s.card:ℝ)^2 ≤
      (sourceRetainedPurePairCount n c ρ cut I κ C ε η E G J).toReal+
      (1+(1-ε)/(cut^2-ε))*(s.card:ℝ) := by
  classical
  let s := (sourceSelectedValueWindowSet_finite c J I κ C ε η E G hfinite).toFinset
  have hsplit := source_actual_selected_value_window_square_bound c J hκ hC
    hη hωG hcut hcutOne hε I hwindow hfinite
  have hpair := source_selected_pure_central_pairs_le_literal_retained_pair_count
    c J hcutρ I κ C ε η E G hfinite
  have hpairFinite := sourceRetainedPurePairCount_lt_top_of_finite c J ρ cut I
    κ C ε η E G hfinite
  have hreal := ENNReal.toReal_mono hpairFinite.ne hpair
  have hsumCast :
      (∑ u ∈ s,
        ((s.filter fun v => v ≠ u ∧ |overlap u v| < cut).card:ℝ)) =
      ((∑ u ∈ s,
        (s.filter fun v => v ≠ u ∧ |overlap u v| < cut).card : ℕ):ℝ) := by
    norm_cast
  have hcentral :
      (∑ u ∈ s,
        ((s.filter fun v => v ≠ u ∧ |overlap u v| < cut).card:ℝ)) ≤
      (sourceRetainedPurePairCount n c ρ cut I κ C ε η E G J).toReal := by
    rw [hsumCast]
    simpa only [ENNReal.toReal_natCast] using hreal
  exact hsplit.trans (add_le_add_left hcentral _)

end
end SlowEquilibration.PairConditionalDeterminantMoments

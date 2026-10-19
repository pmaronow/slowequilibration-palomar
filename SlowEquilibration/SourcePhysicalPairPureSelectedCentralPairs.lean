-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairPureSelectedSquare

/-! Inject each selected pure value-window central ordered pair into the
literal actual retained value-window sphere pair count. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalMorse
open SphericalPairCountGluing SphericalPairMarkedWindows SphericalForm
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem source_selected_pure_central_pairs_le_literal_retained_pair_count {n P : ℕ}
    (c : Degree P → ℝ) (J : Disorder (n+1) P)
    {ρ cut : ℝ} (hcutρ : cut ≤ ρ)
    (I : Set ℝ) (κ C ε η E G : ℝ)
    (hfinite : (sphereCriticalSet n c J).Finite) :
    let s := (sourceSelectedValueWindowSet_finite c J I κ C ε η E G
      hfinite).toFinset
    ((∑ u ∈ s,
      (s.filter fun v => v ≠ u ∧ |overlap u v| < cut).card : ℕ) : ℝ≥0∞) ≤
      sourceRetainedPurePairCount n c ρ cut I κ C ε η E G J := by
  classical
  let hs := sourceSelectedValueWindowSet_finite c J I κ C ε η E G hfinite
  let s := hs.toFinset
  let t := (s.product s).filter fun p => p.2 ≠ p.1 ∧ |overlap p.1 p.2| < cut
  let D : Set (Vector (n+1) × Vector (n+1)) :=
    {p | ‖p.1‖^2=(n+1:ℕ) ∧ ‖p.2‖^2=(n+1:ℕ) ∧
      |overlap p.1 p.2|<ρ ∧ surfaceGradient (field c J) p.1=0 ∧
      surfaceGradient (field c J) p.2=0}
  have hm : ∀ u ∈ s, u ∈ sourceSelectedValueWindowSet c J I κ C ε η E G := by
    intro u hu
    exact (Set.Finite.mem_toFinset hs).mp hu
  let f : t ↪ D := {
    toFun := fun p => ⟨p.val, by
      have hp := Finset.mem_filter.mp p.property
      have hxy := Finset.mem_product.mp hp.1
      have hx := hm _ hxy.1
      have hy := hm _ hxy.2
      exact ⟨hx.1.1,hy.1.1,hp.2.2.trans_le hcutρ,hx.1.2,hy.1.2⟩⟩
    inj' := by
      intro p q h
      exact Subtype.ext (congrArg (fun d : D => d.val) h) }
  have hrows :
      (∑ u ∈ s, (s.filter fun v => v ≠ u ∧ |overlap u v| < cut).card) = t.card := by
    calc
      _ = ∑ u ∈ s, ∑ v ∈ s, if v ≠ u ∧ |overlap u v| < cut then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro u hu
        exact Finset.card_filter (fun v => v ≠ u ∧ |overlap u v| < cut) s
      _ = ∑ p ∈ s.product s,
          if p.2 ≠ p.1 ∧ |overlap p.1 p.2| < cut then 1 else 0 := by
        convert (Finset.sum_product s s
          (fun p => if p.2 ≠ p.1 ∧ |overlap p.1 p.2| < cut then (1:ℕ) else 0)).symm
          using 1
      _ = t.card := (Finset.card_filter
        (fun p => p.2 ≠ p.1 ∧ |overlap p.1 p.2| < cut) (s.product s)).symm
  have hmark : ∀ p : t,
      actualValuePairWindowMark c I cut
        (sourceSelectionPairMark c κ C ε η E G) J (f p).val = 1 := by
    intro p
    have hp := Finset.mem_filter.mp p.property
    have hxy := Finset.mem_product.mp hp.1
    have hx := hm _ hxy.1
    have hy := hm _ hxy.2
    change actualValuePairWindowMark c I cut
      (sourceSelectionPairMark c κ C ε η E G) J p.val = 1
    simp [actualValuePairWindowMark,sourceSelectionPairMark,sourceSelectionMark,
      hp.2.2,hx.2.1,hy.2.1,hx.2.2,hy.2.2]
  unfold sourceRetainedPurePairCount actualSpherePairCount
  change ((∑ u ∈ s,
    (s.filter fun v => v ≠ u ∧ |overlap u v| < cut).card : ℕ) : ℝ≥0∞) ≤
    ∑' p : D, actualValuePairWindowMark c I cut
      (sourceSelectionPairMark c κ C ε η E G) J p.val
  calc
    _ = (t.card : ℝ≥0∞) := congrArg (fun k : ℕ => (k:ℝ≥0∞)) hrows
    _ = ∑' p : t, (1:ℝ≥0∞) := by rw [tsum_fintype]; simp
    _ = ∑' p : t, actualValuePairWindowMark c I cut
        (sourceSelectionPairMark c κ C ε η E G) J (f p).val := by
      apply tsum_congr
      intro p
      exact (hmark p).symm
    _ ≤ ∑' p : D, actualValuePairWindowMark c I cut
        (sourceSelectionPairMark c κ C ε η E G) J p.val :=
      ENNReal.tsum_comp_le_tsum_of_injective f.injective
        (fun p : D => actualValuePairWindowMark c I cut
          (sourceSelectionPairMark c κ C ε η E G) J p.val)

end
end SlowEquilibration.PairConditionalDeterminantMoments

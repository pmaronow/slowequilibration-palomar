-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairJetBounds

/-! A subcritical annulus envelope for the actual physical pair jet
intensity, normalized by its true positive one-point marginals. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open Filter SphericalModel SphericalGaussianJet
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

theorem source_mixed_subcritical_pair_jet_bound (μ:FiniteMixture) {Q M gap:ℝ}
    (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree) (hd:4 ≤ μ.minDegree) (hM:0 ≤ M) (hgap:0<gap) :
    ∃ δ C:ℝ,0<δ ∧ δ ≤ 1 ∧ 0<C ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ))
      (h1 k1 h2 k2:ℝ),|h1| ≤ M → |k1| ≤ M → |h2| ≤ M → |k2| ≤ M → |overlap x y| ≤ δ →
      2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ k1 → 2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ k2 →
      sourceMixedPairJetIntensity μ Q x y hx hy h1 k1 h2 k2 ≤
        C*Real.exp (((n+3:ℕ):ℝ)*(overlap x y)^2/8)*(sourceMixedOnePointJetIntensity μ Q x hx h1 k1*sourceMixedOnePointJetIntensity μ Q y hy h2 k2):=by
  obtain ⟨δ,C,hδ,hδOne,hC,hall⟩:=source_mixed_physical_pair_subcritical_envelope μ hQ hnp hd hM hgap
  refine ⟨δ,C,hδ,hδOne,hC,?_⟩
  filter_upwards [hall] with n hn
  intro x y hx hy h1 k1 h2 k2 hh1 hk1M hh2 hk2M hr hk1 hk2
  have hR:=hn x y hx hy h1 k1 h2 k2 hh1 hk1M hh2 hk2M hk1 hk2 hr
  have h1pos:=source_mixed_one_point_jet_positive μ hQ hnp x hx h1 k1 (by linarith)
  have h2pos:=source_mixed_one_point_jet_positive μ hQ hnp y hy h2 k2 (by linarith)
  rw [source_mixed_physical_pair_ratio_eq_jetIntensity_quotient] at hR
  exact (div_le_iff₀ (mul_pos h1pos h2pos)).mp hR

theorem source_pure_subcritical_pair_jet_bound (p:ℕ) (hp:4 ≤ p) (alpha:ℝ) (halpha:0<alpha) {Q M gap:ℝ}
    (hQ:0<Q) (hM:0 ≤ M) (hgap:0<gap) :
    let μ:=FiniteMixture.pure p (by omega) alpha halpha
    ∃ δ C:ℝ,0<δ ∧ δ ≤ 1 ∧ 0<C ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ))
      (h1 h2:ℝ),|h1| ≤ M → |h2| ≤ M → |overlap x y| ≤ δ →
      2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ (p:ℝ)*h1 → 2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ (p:ℝ)*h2 →
      sourcePurePairJetIntensity p (by omega) alpha halpha Q x y hx hy h1 h2 ≤
        C*Real.exp (((n+3:ℕ):ℝ)*(overlap x y)^2/8)*(sourcePureOnePointJetIntensity p (by omega) alpha halpha Q x hx h1*sourcePureOnePointJetIntensity p (by omega) alpha halpha Q y hy h2):=by
  dsimp only
  obtain ⟨δ,C,hδ,hδOne,hC,hall⟩:=source_pure_physical_pair_subcritical_envelope p hp alpha halpha hQ hM hgap
  refine ⟨δ,C,hδ,hδOne,hC,?_⟩
  filter_upwards [hall] with n hn
  intro x y hx hy h1 h2 hh1 hh2 hr hk1 hk2
  have hR:=hn x y hx hy h1 h2 hh1 hh2 hk1 hk2 hr
  have h1pos:=source_pure_one_point_jet_positive p (by omega) alpha halpha hQ x hx h1 (by linarith)
  have h2pos:=source_pure_one_point_jet_positive p (by omega) alpha halpha hQ y hy h2 (by linarith)
  rw [source_pure_physical_pair_ratio_eq_jetIntensity_quotient] at hR
  exact (div_le_iff₀ (mul_pos h1pos h2pos)).mp hR

end
end SlowEquilibration.PairConditionalDeterminantMoments

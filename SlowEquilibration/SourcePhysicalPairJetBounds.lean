-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalOnePointJetIntensity
public import SlowEquilibration.SourcePhysicalPairCentralFactorization
public import SlowEquilibration.SourcePhysicalPairSubcriticalEnvelope
public import SlowEquilibration.SphericalScoreDensityRates

/-! Source estimates for the literal physical pair jet intensity, with
strict positivity of its genuine one-point normalizers proved internally. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open GaussianRegression GaussianObservationCoercivity IntrinsicHessianLaw
open SphericalMarkedWindows SphericalSequentialRegression GOEPhysicalPotential GOEPhysicalNormalizedMoments
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000

lemma source_mixed_one_point_jet_positive {n:ℕ} (μ:FiniteMixture) {Q:ℝ} (hQ:0<Q)
    (hnp:μ.minDegree<μ.maxDegree) (x:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (h k:ℝ)
    (hk:2*Real.sqrt (Q^2*μ.xi2 Q)<k) : 0<sourceMixedOnePointJetIntensity μ Q x hx h k:=by
  unfold sourceMixedOnePointJetIntensity
  dsimp only
  refine mul_pos (mul_pos (realObservationDensity_pos _
    (center_gradient_surjective (by omega) μ hQ x hx _
      (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx)) _) ?_)
    (physicalMean_pos (n+1) 1 (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)) hk)
  rw [normalizedScorePdf_eq (by omega) μ hQ hnp x hx]
  exact physicalScorePdf_toReal_pos (n+3) (by omega) μ hQ hnp _

lemma source_pure_one_point_jet_positive {n:ℕ} (p:ℕ) (hp:2 ≤ p) (alpha:ℝ) (halpha:0<alpha)
    {Q:ℝ} (hQ:0<Q) (x:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (h:ℝ)
    (hk:2*Real.sqrt (Q^2*(FiniteMixture.pure p hp alpha halpha).xi2 Q)<(p:ℝ)*h) :
    0<sourcePureOnePointJetIntensity p hp alpha halpha Q x hx h:=by
  let μ:=FiniteMixture.pure p hp alpha halpha
  unfold sourcePureOnePointJetIntensity
  dsimp only
  refine mul_pos (mul_pos (realObservationDensity_pos _
    (center_gradient_surjective (by omega) μ hQ x hx _
      (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx)) _) ?_)
    (physicalMean_pos (n+1) 1 (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)) hk)
  rw [normalizedValuePdf_eq μ hQ x hx]
  exact physicalValuePdf_toReal_pos (n+3) (by omega) μ hQ h

lemma pair_jet_error_of_ratio {P W E:ℝ} (hW:0<W) (hR:|P/W-1| ≤ E) :
    |P-W| ≤ E*W ∧ P ≤ (1+E)*W:=by
  rw [div_sub_one hW.ne',abs_div,abs_of_pos hW] at hR
  have he:|P-W| ≤ E*W:=(div_le_iff₀ hW).mp hR
  refine ⟨he,?_⟩
  nlinarith [le_abs_self (P-W)]

theorem source_mixed_central_pair_jet_bounds (μ:FiniteMixture) {Q M gap α:ℝ}
    (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree) (hd:4 ≤ μ.minDegree)
    (hM:0 ≤ M) (hgap:0<gap) (hα:1/4<α) :
    ∃ C:ℝ,0<C ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ))
      (h1 k1 h2 k2:ℝ),|h1| ≤ M → |k1| ≤ M → |h2| ≤ M → |k2| ≤ M →
      2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ k1 → 2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ k2 →
      |overlap x y| ≤ ((n+3:ℕ):ℝ)^(-α) →
      let W:=sourceMixedOnePointJetIntensity μ Q x hx h1 k1*sourceMixedOnePointJetIntensity μ Q y hy h2 k2
      let P:=sourceMixedPairJetIntensity μ Q x y hx hy h1 k1 h2 k2
      let E:=C*(((n+3:ℕ):ℝ)^(1-4*α)+1/Real.sqrt (n+3:ℕ))
      |P-W| ≤ E*W ∧ P ≤ (1+E)*W:=by
  obtain ⟨C,hC,hall⟩:=source_mixed_physical_pair_central_factorization μ hQ hnp hd hM hgap hα
  refine ⟨C,hC,?_⟩
  filter_upwards [hall] with n hn
  intro x y hx hy h1 k1 h2 k2 hh1 hk1M hh2 hk2M hk1 hk2 hr
  have h1pos:=source_mixed_one_point_jet_positive μ hQ hnp x hx h1 k1 (by linarith)
  have h2pos:=source_mixed_one_point_jet_positive μ hQ hnp y hy h2 k2 (by linarith)
  have hh:=hn x y hx hy h1 k1 h2 k2 hh1 hk1M hh2 hk2M hk1 hk2 hr
  rw [source_mixed_physical_pair_ratio_eq_jetIntensity_quotient] at hh
  exact pair_jet_error_of_ratio (mul_pos h1pos h2pos) hh

theorem source_pure_central_pair_jet_bounds (p:ℕ) (hp:4 ≤ p) (alpha:ℝ) (halpha:0<alpha) {Q M gap α:ℝ}
    (hQ:0<Q) (hM:0 ≤ M) (hgap:0<gap) (hα:1/4<α) :
    let μ:=FiniteMixture.pure p (by omega) alpha halpha
    ∃ C:ℝ,0<C ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (x y:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ))
      (h1 h2:ℝ),|h1| ≤ M → |h2| ≤ M →
      2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ (p:ℝ)*h1 → 2*Real.sqrt (Q^2*μ.xi2 Q)+gap ≤ (p:ℝ)*h2 →
      |overlap x y| ≤ ((n+3:ℕ):ℝ)^(-α) →
      let W:=sourcePureOnePointJetIntensity p (by omega) alpha halpha Q x hx h1*
        sourcePureOnePointJetIntensity p (by omega) alpha halpha Q y hy h2
      let P:=sourcePurePairJetIntensity p (by omega) alpha halpha Q x y hx hy h1 h2
      let E:=C*(((n+3:ℕ):ℝ)^(1-4*α)+1/Real.sqrt (n+3:ℕ))
      |P-W| ≤ E*W ∧ P ≤ (1+E)*W:=by
  dsimp only
  obtain ⟨C,hC,hall⟩:=source_pure_physical_pair_central_factorization p hp alpha halpha hQ hM hgap hα
  refine ⟨C,hC,?_⟩
  filter_upwards [hall] with n hn
  intro x y hx hy h1 h2 hh1 hh2 hk1 hk2 hr
  have h1pos:=source_pure_one_point_jet_positive p (by omega) alpha halpha hQ x hx h1 (by linarith)
  have h2pos:=source_pure_one_point_jet_positive p (by omega) alpha halpha hQ y hy h2 (by linarith)
  have hh:=hn x y hx hy h1 h2 hh1 hh2 hk1 hk2 hr
  rw [source_pure_physical_pair_ratio_eq_jetIntensity_quotient] at hh
  exact pair_jet_error_of_ratio (mul_pos h1pos h2pos) hh

end
end SlowEquilibration.PairConditionalDeterminantMoments

-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairPureCountBounds

/-! Vanishing of the literal manuscript integrated-pair error, and removal
of bounded selection indicators from the actual ordered critical-pair sum. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Filter Set
open SphericalModel SphericalPairCountGluing
open scoped ENNReal Topology
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

lemma source_pair_annulus_error_tendsto {α:ℝ} (hα:α<1/2) :
    Tendsto (fun n:ℕ=>Real.exp (-((n+3:ℕ):ℝ)^(1-2*α)/4)) atTop (𝓝 0):=by
  have hN:Tendsto (fun n:ℕ=>((n+3:ℕ):ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  have hPow:=(tendsto_rpow_atTop (show 0<1-2*α by linarith)).comp hN
  have hNeg:=(hPow.const_mul_atTop_of_neg (r:=-(1/4:ℝ)) (by norm_num))
  have hh:=Real.tendsto_exp_atBot.comp hNeg
  convert hh using 1
  funext n
  congr 1
  simp only [Function.comp_def]
  ring

theorem source_pair_count_error_tendsto (C:ℝ) {α:ℝ} (hα:1/4<α) (hαHalf:α<1/2) :
    Tendsto (fun n:ℕ=>C*(((n+3:ℕ):ℝ)^(1-4*α)+1/Real.sqrt (n+3:ℕ)+
      Real.exp (-((n+3:ℕ):ℝ)^(1-2*α)/4))) atTop (𝓝 0):=by
  simpa only [add_zero,mul_zero] using
    ((PairSchurExpectation.ambient_central_rate_tendsto hα).add
      PairSchurExpectation.ambient_inverse_sqrt_tendsto).add
        (source_pair_annulus_error_tendsto hαHalf) |>.const_mul C

lemma actualSpherePairCount_mono {P:ℕ} (n:ℕ) (c:Degree P→ℝ) (ρ:ℝ)
    (psi chi:Disorder (n+1) P→Vector (n+1)×Vector (n+1)→ℝ≥0∞)
    (hMark:∀ J p,psi J p ≤ chi J p) (J:Disorder (n+1) P) :
    actualSpherePairCount n c ρ psi J ≤ actualSpherePairCount n c ρ chi J:=by
  unfold actualSpherePairCount
  exact ENNReal.tsum_le_tsum (fun p=>hMark J p)

lemma actualMixedPairWindowMark_le_one {N P:ℕ} (c:Degree P→ℝ)
    (K:Set (EuclideanSpace ℝ (Fin 2))) (δ:ℝ)
    (psi:Disorder N P→Vector N×Vector N→ℝ≥0∞) (hpsi:∀ J p,psi J p ≤ 1)
    (J:Disorder N P) (p:Vector N×Vector N) :
    actualMixedPairWindowMark c K δ psi J p ≤ actualMixedPairWindowMark c K δ (fun _ _=>1) J p:=by
  unfold actualMixedPairWindowMark
  split_ifs <;> first | exact hpsi J p | exact le_rfl

lemma actualValuePairWindowMark_le_one {N P:ℕ} (c:Degree P→ℝ)
    (K:Set ℝ) (δ:ℝ)
    (psi:Disorder N P→Vector N×Vector N→ℝ≥0∞) (hpsi:∀ J p,psi J p ≤ 1)
    (J:Disorder N P) (p:Vector N×Vector N) :
    actualValuePairWindowMark c K δ psi J p ≤ actualValuePairWindowMark c K δ (fun _ _=>1) J p:=by
  unfold actualValuePairWindowMark
  split_ifs <;> first | exact hpsi J p | exact le_rfl

theorem source_mixed_actual_pair_filter_count_le {P:ℕ} (n:ℕ) (c:Degree P→ℝ) (ρ δ:ℝ)
    (K:Set (EuclideanSpace ℝ (Fin 2)))
    (psi:Disorder (n+1) P→Vector (n+1)×Vector (n+1)→ℝ≥0∞) (hpsi:∀ J p,psi J p ≤ 1) :
    (∫⁻ J,actualSpherePairCount n c ρ (actualMixedPairWindowMark c K δ psi) J ∂disorderLaw (n+1) P) ≤
      ∫⁻ J,actualSpherePairCount n c ρ (actualMixedPairWindowMark c K δ (fun _ _=>1)) J ∂disorderLaw (n+1) P:=by
  apply lintegral_mono
  intro J
  exact actualSpherePairCount_mono n c ρ _ _ (actualMixedPairWindowMark_le_one c K δ psi hpsi) J

theorem source_pure_actual_pair_filter_count_le {P:ℕ} (n:ℕ) (c:Degree P→ℝ) (ρ δ:ℝ)
    (K:Set ℝ)
    (psi:Disorder (n+1) P→Vector (n+1)×Vector (n+1)→ℝ≥0∞) (hpsi:∀ J p,psi J p ≤ 1) :
    (∫⁻ J,actualSpherePairCount n c ρ (actualValuePairWindowMark c K δ psi) J ∂disorderLaw (n+1) P) ≤
      ∫⁻ J,actualSpherePairCount n c ρ (actualValuePairWindowMark c K δ (fun _ _=>1)) J ∂disorderLaw (n+1) P:=by
  apply lintegral_mono
  intro J
  exact actualSpherePairCount_mono n c ρ _ _ (actualValuePairWindowMark_le_one c K δ psi hpsi) J

end
end SlowEquilibration.PairConditionalDeterminantMoments

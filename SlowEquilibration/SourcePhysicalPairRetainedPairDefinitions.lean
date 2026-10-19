-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairRetainedNormalization
public import SlowEquilibration.SourcePhysicalPairCountRates

/-! Literal actual retained ordered pair counts and their normalization
transfer. Each endpoint uses the selection indicator at both original
sphere points and the actual retained one-point mean a_N. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalPairCountGluing
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

def sourceSelectionPairMark {N P:ℕ} (c:Degree P→ℝ) (κ C ε η E G:ℝ)
    (J:Disorder N P) (p:Vector N×Vector N):ℝ≥0∞:=
  sourceSelectionMark c κ C ε η E G J p.1*sourceSelectionMark c κ C ε η E G J p.2

lemma sourceSelectionPairMark_le_one {N P:ℕ} (c:Degree P→ℝ) (κ C ε η E G:ℝ)
    (J:Disorder N P) (p:Vector N×Vector N) : sourceSelectionPairMark c κ C ε η E G J p ≤ 1:=by
  exact (mul_le_mul' (sourceSelectionMark_le_one c κ C ε η E G J p.1)
    (sourceSelectionMark_le_one c κ C ε η E G J p.2)).trans_eq (mul_one 1)

def sourceRetainedMixedPairCount {P:ℕ} (n:ℕ) (c:Degree P→ℝ) (ρ cut:ℝ)
    (K:Set (EuclideanSpace ℝ (Fin 2))) (κ C ε η E G:ℝ) (J:Disorder (n+1) P):ℝ≥0∞:=
  actualSpherePairCount n c ρ (actualMixedPairWindowMark c K cut
    (sourceSelectionPairMark c κ C ε η E G)) J

def sourceRetainedMixedPairMean (n:ℕ) (μ:FiniteMixture) (Q ρ cut:ℝ)
    (K:Set (EuclideanSpace ℝ (Fin 2))) (κ C ε η E G:ℝ):ℝ:=
  (∫⁻ J,sourceRetainedMixedPairCount n (centerCoefficients (mixtureCoefficients μ) Q) ρ cut K
    κ C ε η E G J ∂disorderLaw (n+1) μ.maxDegree).toReal

lemma source_retained_pair_normalization_transfer {p a b A t:ℝ}
    (ha:0 ≤ a) (hb:0 ≤ b) (hA:0 ≤ A) (ht:t<1)
    (hp:p ≤ A*b^2) (hnorm:(1-t)*b ≤ a) : p ≤ A/(1-t)^2*a^2:=by
  have hden:0<1-t:=sub_pos.mpr ht
  have hs:((1-t)*b)^2 ≤ a^2:=(sq_le_sq₀ (mul_nonneg hden.le hb) ha).mpr hnorm
  have hsq:b^2 ≤ a^2/(1-t)^2:=by
    apply (le_div_iff₀ (sq_pos_of_pos hden)).mpr
    nlinarith [hs]
  calc
    p ≤ A*b^2:=hp
    _ ≤ A*(a^2/(1-t)^2):=mul_le_mul_of_nonneg_left hsq hA
    _ = _:=by ring

theorem source_mixed_retained_pair_mean_bound_of_normalization (n:ℕ) (hn:1 ≤ n)
    (μ:FiniteMixture) {Q:ℝ} (hQ:0<Q) (ρ cut:ℝ)
    (K:Set (EuclideanSpace ℝ (Fin 2))) (κ C ε η E G A t:ℝ) (hA:0 ≤ A) (ht:t<1)
    (hpair:let c:=centerCoefficients (mixtureCoefficients μ) Q
      (∫⁻ J,actualSpherePairCount n c ρ (actualMixedPairWindowMark c K cut (fun _ _=>1)) J
        ∂disorderLaw (n+1) μ.maxDegree) ≤ ENNReal.ofReal A*
          (∫⁻ J,actualScoreWindowCount n c K (fun _ _=>1) J ∂disorderLaw (n+1) μ.maxDegree)^2)
    (hnorm:(1-t)*sourceUnfilteredScoreWindowMean n μ Q K ≤
      sourceRetainedScoreWindowMean n μ Q K κ C ε η E G) :
    sourceRetainedMixedPairMean n μ Q ρ cut K κ C ε η E G ≤
      A/(1-t)^2*(sourceRetainedScoreWindowMean n μ Q K κ C ε η E G)^2:=by
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have hB:=bounded_scoreWindowCount_lintegral_lt_top n hn μ hQ K (fun _ _=>1) 1 (by simp) (by simp)
  have hfinite:ENNReal.ofReal A*
      (∫⁻ J,actualScoreWindowCount n c K (fun _ _=>1) J ∂disorderLaw (n+1) μ.maxDegree)^2≠⊤:=by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hB.ne)
  have hup:=source_mixed_actual_pair_filter_count_le n c ρ cut K
    (sourceSelectionPairMark c κ C ε η E G) (sourceSelectionPairMark_le_one c κ C ε η E G)
  have hR:=ENNReal.toReal_mono hfinite (hup.trans hpair)
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hA,ENNReal.toReal_pow] at hR
  exact source_retained_pair_normalization_transfer ENNReal.toReal_nonneg ENNReal.toReal_nonneg hA ht hR hnorm

end
end SlowEquilibration.PairConditionalDeterminantMoments

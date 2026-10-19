-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPurePairRetainedNormalization
public import SlowEquilibration.SourcePhysicalPairRetainedPairDefinitions

@[expose] public section
/-! Literal retained ordered value-window pairs and actual retained mean
normalization, using the original source selection at both sphere points. -/
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Set
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalPairCountGluing
open SphericalPairMarkedWindows
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

def sourceRetainedPurePairCount {P:ℕ} (n:ℕ) (c:Degree P→ℝ) (ρ cut:ℝ)
    (I:Set ℝ) (κ C ε η E G:ℝ) (J:Disorder (n+1) P):ℝ≥0∞:=
  actualSpherePairCount n c ρ (actualValuePairWindowMark c I cut
    (sourceSelectionPairMark c κ C ε η E G)) J

def sourceRetainedPurePairMean (n:ℕ) (μ:FiniteMixture) (Q ρ cut:ℝ)
    (I:Set ℝ) (κ C ε η E G:ℝ):ℝ:=
  (∫⁻ J,sourceRetainedPurePairCount n (centerCoefficients (mixtureCoefficients μ) Q) ρ cut I
    κ C ε η E G J ∂disorderLaw (n+1) μ.maxDegree).toReal

/-- Literal value-window pair normalization reduction; the physical
certificate consumer will derive both count and retained-mean inputs. -/
theorem source_pure_retained_pair_mean_bound_of_normalization (n:ℕ) (hn:1 ≤ n)
    (μ:FiniteMixture) {Q:ℝ} (hQ:0<Q) (ρ cut:ℝ)
    (I:Set ℝ) (κ C ε η E G A t:ℝ) (hA:0 ≤ A) (ht:t<1)
    (hpair:let c:=centerCoefficients (mixtureCoefficients μ) Q
      (∫⁻ J,actualSpherePairCount n c ρ (actualValuePairWindowMark c I cut (fun _ _=>1)) J
        ∂disorderLaw (n+1) μ.maxDegree) ≤ ENNReal.ofReal A*
          (∫⁻ J,actualValueWindowCount n c I (fun _ _=>1) J ∂disorderLaw (n+1) μ.maxDegree)^2)
    (hnorm:(1-t)*sourceUnfilteredValueWindowMean n μ Q I ≤
      sourceRetainedValueWindowMean n μ Q I κ C ε η E G) :
    sourceRetainedPurePairMean n μ Q ρ cut I κ C ε η E G ≤
      A/(1-t)^2*(sourceRetainedValueWindowMean n μ Q I κ C ε η E G)^2:=by
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have hB:=sourceUnfilteredValueWindowCount_lintegral_lt_top n hn μ hQ I
  have hfinite:ENNReal.ofReal A*
      (∫⁻ J,actualValueWindowCount n c I (fun _ _=>1) J ∂disorderLaw (n+1) μ.maxDegree)^2≠⊤:=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hB.ne)
  have hup:=source_pure_actual_pair_filter_count_le n c ρ cut I
    (sourceSelectionPairMark c κ C ε η E G) (sourceSelectionPairMark_le_one c κ C ε η E G)
  have hR:=ENNReal.toReal_mono hfinite (hup.trans hpair)
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hA,ENNReal.toReal_pow] at hR
  exact source_retained_pair_normalization_transfer ENNReal.toReal_nonneg ENNReal.toReal_nonneg hA ht hR hnorm

end
end SlowEquilibration.PairConditionalDeterminantMoments

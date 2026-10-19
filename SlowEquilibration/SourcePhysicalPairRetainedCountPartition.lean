-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairSelectionMaxima

/-! Exact partition of the literal critical-window mean into selected
(retained maximum) and discarded parts. This identifies the actual a_N
normalizer and its difference from the actual unfiltered b_N. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Set
open SphericalModel SphericalGaussianJet SphericalMarkedWindows
open scoped ENNReal
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance] Classical.propDecidable

def sourceDiscardedMark {N P:ℕ} (c:Degree P→ℝ) (κ C ε η E G:ℝ)
    (J:Disorder N P) (u:Vector N):ℝ≥0∞:=
  if sourceSelectionEvent c κ C ε η E G J u then 0 else 1

lemma sourceDiscardedMark_measurable {N P:ℕ} (c:Degree P→ℝ) (κ C ε η E G:ℝ) :
    Measurable (fun p:Disorder N P×Vector N=>sourceDiscardedMark c κ C ε η E G p.1 p.2):=
  Measurable.ite (sourceSelectionEvent_measurable c κ C ε η E G) measurable_const measurable_const

lemma sourceSelectionMark_add_discarded {N P:ℕ} (c:Degree P→ℝ) (κ C ε η E G:ℝ)
    (J:Disorder N P) (u:Vector N):
    sourceSelectionMark c κ C ε η E G J u+sourceDiscardedMark c κ C ε η E G J u=1:=by
  unfold sourceSelectionMark sourceDiscardedMark
  by_cases h:sourceSelectionEvent c κ C ε η E G J u
  · simp only [ite_eq_left h,add_zero]
  · simp only [ite_eq_right h,zero_add]

theorem sourceRetainedScoreWindowCount_add_discarded {P:ℕ} (n:ℕ) (c:Degree P→ℝ)
    (K:Set (EuclideanSpace ℝ (Fin 2))) (κ C ε η E G:ℝ) (J:Disorder (n+1) P) :
    sourceRetainedScoreWindowCount n c K κ C ε η E G J+
      actualScoreWindowCount n c K (sourceDiscardedMark c κ C ε η E G) J=
        actualScoreWindowCount n c K (fun _ _=>1) J:=by
  unfold sourceRetainedScoreWindowCount actualScoreWindowCount
  rw [←ENNReal.tsum_add]
  apply tsum_congr
  intro u
  exact sourceSelectionMark_add_discarded c κ C ε η E G J u

theorem sourceRetainedValueWindowCount_add_discarded {P:ℕ} (n:ℕ) (c:Degree P→ℝ)
    (I:Set ℝ) (κ C ε η E G:ℝ) (J:Disorder (n+1) P) :
    sourceRetainedValueWindowCount n c I κ C ε η E G J+
      actualValueWindowCount n c I (sourceDiscardedMark c κ C ε η E G) J=
        actualValueWindowCount n c I (fun _ _=>1) J:=by
  unfold sourceRetainedValueWindowCount actualValueWindowCount
  rw [←ENNReal.tsum_add]
  apply tsum_congr
  intro u
  exact sourceSelectionMark_add_discarded c κ C ε η E G J u

theorem sourceRetainedScoreWindowMean_add_discarded (n:ℕ) (hn:1 ≤ n) (μ:FiniteMixture)
    {Q:ℝ} (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree)
    (K:Set (EuclideanSpace ℝ (Fin 2))) (hK:MeasurableSet K) (κ C ε η E G:ℝ) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J,sourceRetainedScoreWindowCount n c K κ C ε η E G J ∂disorderLaw (n+1) μ.maxDegree)+
      (∫⁻ J,actualScoreWindowCount n c K (sourceDiscardedMark c κ C ε η E G) J ∂disorderLaw (n+1) μ.maxDegree)=
        ∫⁻ J,actualScoreWindowCount n c K (fun _ _=>1) J ∂disorderLaw (n+1) μ.maxDegree:=by
  dsimp only
  rw [←lintegral_add_left' (sourceRetainedScoreWindowCount_kacRice n hn μ hQ hnp K hK κ C ε η E G).1]
  exact lintegral_congr (fun J=>sourceRetainedScoreWindowCount_add_discarded n _ K κ C ε η E G J)

theorem sourceRetainedValueWindowMean_add_discarded (n:ℕ) (hn:1 ≤ n) (μ:FiniteMixture)
    {Q:ℝ} (hQ:0<Q) (I:Set ℝ) (hI:MeasurableSet I) (κ C ε η E G:ℝ) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J,sourceRetainedValueWindowCount n c I κ C ε η E G J ∂disorderLaw (n+1) μ.maxDegree)+
      (∫⁻ J,actualValueWindowCount n c I (sourceDiscardedMark c κ C ε η E G) J ∂disorderLaw (n+1) μ.maxDegree)=
        ∫⁻ J,actualValueWindowCount n c I (fun _ _=>1) J ∂disorderLaw (n+1) μ.maxDegree:=by
  dsimp only
  rw [←lintegral_add_left' (sourceRetainedValueWindowCount_kacRice n hn μ hQ I hI κ C ε η E G).1]
  exact lintegral_congr (fun J=>sourceRetainedValueWindowCount_add_discarded n _ I κ C ε η E G J)

end
end SlowEquilibration.PairConditionalDeterminantMoments

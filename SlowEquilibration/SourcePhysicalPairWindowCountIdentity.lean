-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairWindowDefinitions
public import SlowEquilibration.SphericalPairIntrinsicKacRice

/-! Literal ordered critical-pair window counts equal the spatial integral
of their true intrinsic window intensity. The overlap neighborhood is chosen
inside the proved Kac--Rice neighborhood and all full-field marks remain. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalGaussianJet SphericalForm WholeFieldRegression SphereHessian
open GaussianRegression SphericalMarkedWindows SphericalPairIntrinsicCoordinates
open SphericalPairChartKacRice SphericalPairCountGluing SphericalPairIntrinsicKacRice SphereChartVolume
open scoped ENNReal
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 1100000
attribute [local instance] Classical.propDecidable

def actualMixedPairWindowMark {N P:ℕ} (c:Degree P→ℝ) (K:Set (EuclideanSpace ℝ (Fin 2))) (δ:ℝ)
    (psi:Disorder N P→Vector N×Vector N→ℝ≥0∞)
    (J:Disorder N P) (p:Vector N×Vector N):ℝ≥0∞:=
  if |overlap p.1 p.2|<δ then
    if actualScore c J p.1∈K ∧ actualScore c J p.2∈K then psi J p else 0 else 0

lemma actualMixedPairWindowMark_measurable {N P:ℕ} (c:Degree P→ℝ) (K:Set (EuclideanSpace ℝ (Fin 2)))
    (hK:MeasurableSet K) (δ:ℝ) (psi:Disorder N P→Vector N×Vector N→ℝ≥0∞)
    (hpsi:Measurable (fun p:Disorder N P×(Vector N×Vector N)=>psi p.1 p.2)) :
    Measurable (fun p:Disorder N P×(Vector N×Vector N)=>actualMixedPairWindowMark c K δ psi p.1 p.2):=by
  unfold actualMixedPairWindowMark
  have hProj1:Measurable (fun p:Disorder N P×(Vector N×Vector N)=>(p.1,p.2.1)):=by fun_prop
  have hProj2:Measurable (fun p:Disorder N P×(Vector N×Vector N)=>(p.1,p.2.2)):=by fun_prop
  have hx:Measurable (fun p:Disorder N P×(Vector N×Vector N)=>actualScore c p.1 p.2.1):=by
    simpa only [Function.comp_def] using (actualScore_jointContinuous (N:=N) (P:=P) c).measurable.comp hProj1
  have hy:Measurable (fun p:Disorder N P×(Vector N×Vector N)=>actualScore c p.1 p.2.2):=by
    simpa only [Function.comp_def] using (actualScore_jointContinuous (N:=N) (P:=P) c).measurable.comp hProj2
  have hOverlap:Measurable (fun p:Vector N×Vector N=>|overlap p.1 p.2|):=by unfold overlap;fun_prop
  have hδ:MeasurableSet {p:Disorder N P×(Vector N×Vector N) | |overlap p.2.1 p.2.2|<δ}:=
    measurableSet_lt (hOverlap.comp measurable_snd) measurable_const
  exact Measurable.ite hδ (Measurable.ite ((hK.preimage hx).inter (hK.preimage hy)) hpsi measurable_const) measurable_const

theorem source_mixed_actual_pair_window_count_identity (n:ℕ) (μ:FiniteMixture) {Q δ:ℝ}
    (hQ:0<Q) (hd:4 ≤ μ.minDegree) (hδ:δ ≤ pairRadius μ hQ hd)
    (K:Set (EuclideanSpace ℝ (Fin 2))) (hK:MeasurableSet K)
    (psi:Disorder (n+3) μ.maxDegree→Vector (n+3)×Vector (n+3)→ℝ≥0∞)
    (hpsi:Measurable (fun p:Disorder (n+3) μ.maxDegree×(Vector (n+3)×Vector (n+3))=>psi p.1 p.2)) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J,actualSpherePairCount (n+2) c (pairRadius μ hQ hd)
      (actualMixedPairWindowMark c K δ psi) J ∂disorderLaw (n+3) μ.maxDegree)=
      ∫⁻ p,{p:Vector (n+3)×Vector (n+3) | |overlap p.1 p.2|<δ}.indicator
        (fun p=>intrinsicMixedPairWindowIntensity c p.1 p.2 K (fun J=>psi J p)) p
        ∂(manuscriptRoundVolume (n+2)).prod (manuscriptRoundVolume (n+2)):=by
  dsimp only
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have hk:=actual_sphere_pair_marked_kacRice (n+2) (by omega) μ hQ hd
    (actualMixedPairWindowMark c K δ psi) (actualMixedPairWindowMark_measurable c K hK δ psi hpsi)
  refine hk.2.trans ?_
  have hA:MeasurableSet {p:Vector (n+3)×Vector (n+3) | |overlap p.1 p.2|<pairRadius μ hQ hd}:=
    measurableSet_lt (by unfold overlap;fun_prop) measurable_const
  rw [←lintegral_indicator hA]
  simp only [Set.indicator_apply,Set.mem_ofPred_eq]
  apply lintegral_congr
  intro p
  by_cases hp:|overlap p.1 p.2|<δ
  · have hpρ:|overlap p.1 p.2|<pairRadius μ hQ hd:=hp.trans_le hδ
    rw [ite_eq_left hpρ,ite_eq_left hp]
    simp only [actualMixedPairWindowMark,ite_eq_left hp]
    rfl
  · rw [ite_eq_right hp]
    by_cases hpρ:|overlap p.1 p.2|<pairRadius μ hQ hd
    · rw [ite_eq_left hpρ]
      simp only [actualMixedPairWindowMark,ite_eq_right hp,mul_zero,lintegral_zero]
    · rw [ite_eq_right hpρ]

def actualValuePairWindowMark {N P:ℕ} (c:Degree P→ℝ) (K:Set (ℝ)) (δ:ℝ)
    (psi:Disorder N P→Vector N×Vector N→ℝ≥0∞)
    (J:Disorder N P) (p:Vector N×Vector N):ℝ≥0∞:=
  if |overlap p.1 p.2|<δ then
    if actualValue c J p.1∈K ∧ actualValue c J p.2∈K then psi J p else 0 else 0

lemma actualValuePairWindowMark_measurable {N P:ℕ} (c:Degree P→ℝ) (K:Set (ℝ))
    (hK:MeasurableSet K) (δ:ℝ) (psi:Disorder N P→Vector N×Vector N→ℝ≥0∞)
    (hpsi:Measurable (fun p:Disorder N P×(Vector N×Vector N)=>psi p.1 p.2)) :
    Measurable (fun p:Disorder N P×(Vector N×Vector N)=>actualValuePairWindowMark c K δ psi p.1 p.2):=by
  unfold actualValuePairWindowMark
  have hProj1:Measurable (fun p:Disorder N P×(Vector N×Vector N)=>(p.1,p.2.1)):=by fun_prop
  have hProj2:Measurable (fun p:Disorder N P×(Vector N×Vector N)=>(p.1,p.2.2)):=by fun_prop
  have hx:Measurable (fun p:Disorder N P×(Vector N×Vector N)=>actualValue c p.1 p.2.1):=by
    simpa only [Function.comp_def] using (actualValue_jointContinuous (N:=N) (P:=P) c).measurable.comp hProj1
  have hy:Measurable (fun p:Disorder N P×(Vector N×Vector N)=>actualValue c p.1 p.2.2):=by
    simpa only [Function.comp_def] using (actualValue_jointContinuous (N:=N) (P:=P) c).measurable.comp hProj2
  have hOverlap:Measurable (fun p:Vector N×Vector N=>|overlap p.1 p.2|):=by unfold overlap;fun_prop
  have hδ:MeasurableSet {p:Disorder N P×(Vector N×Vector N) | |overlap p.2.1 p.2.2|<δ}:=
    measurableSet_lt (hOverlap.comp measurable_snd) measurable_const
  exact Measurable.ite hδ (Measurable.ite ((hK.preimage hx).inter (hK.preimage hy)) hpsi measurable_const) measurable_const

theorem source_value_actual_pair_window_count_identity (n:ℕ) (μ:FiniteMixture) {Q δ:ℝ}
    (hQ:0<Q) (hd:4 ≤ μ.minDegree) (hδ:δ ≤ pairRadius μ hQ hd)
    (K:Set (ℝ)) (hK:MeasurableSet K)
    (psi:Disorder (n+3) μ.maxDegree→Vector (n+3)×Vector (n+3)→ℝ≥0∞)
    (hpsi:Measurable (fun p:Disorder (n+3) μ.maxDegree×(Vector (n+3)×Vector (n+3))=>psi p.1 p.2)) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J,actualSpherePairCount (n+2) c (pairRadius μ hQ hd)
      (actualValuePairWindowMark c K δ psi) J ∂disorderLaw (n+3) μ.maxDegree)=
      ∫⁻ p,{p:Vector (n+3)×Vector (n+3) | |overlap p.1 p.2|<δ}.indicator
        (fun p=>intrinsicValuePairWindowIntensity c p.1 p.2 K (fun J=>psi J p)) p
        ∂(manuscriptRoundVolume (n+2)).prod (manuscriptRoundVolume (n+2)):=by
  dsimp only
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have hk:=actual_sphere_pair_marked_kacRice (n+2) (by omega) μ hQ hd
    (actualValuePairWindowMark c K δ psi) (actualValuePairWindowMark_measurable c K hK δ psi hpsi)
  refine hk.2.trans ?_
  have hA:MeasurableSet {p:Vector (n+3)×Vector (n+3) | |overlap p.1 p.2|<pairRadius μ hQ hd}:=
    measurableSet_lt (by unfold overlap;fun_prop) measurable_const
  rw [←lintegral_indicator hA]
  simp only [Set.indicator_apply,Set.mem_ofPred_eq]
  apply lintegral_congr
  intro p
  by_cases hp:|overlap p.1 p.2|<δ
  · have hpρ:|overlap p.1 p.2|<pairRadius μ hQ hd:=hp.trans_le hδ
    rw [ite_eq_left hpρ,ite_eq_left hp]
    simp only [actualValuePairWindowMark,ite_eq_left hp]
    rfl
  · rw [ite_eq_right hp]
    by_cases hpρ:|overlap p.1 p.2|<pairRadius μ hQ hd
    · rw [ite_eq_left hpρ]
      simp only [actualValuePairWindowMark,ite_eq_right hp,mul_zero,lintegral_zero]
    · rw [ite_eq_right hpρ]

end
end SlowEquilibration.PairConditionalDeterminantMoments

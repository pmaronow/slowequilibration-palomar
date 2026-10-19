-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCountRectangles
public import SlowEquilibration.SourcePhysicalOnePointJetIntensity

/-! Exact product physical-mark integrals in the pair coordinates. Their
normalizers are the actual expected one-point critical-window counts. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations SphericalForm
open SphericalMarkedWindows SphericalSequentialRegression
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem physical_mark_pair_window_product_integral {Z:Type*}
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
    [MeasurableSpace Z] [BorelSpace Z] (K:Set Z) (hK:MeasurableSet K)
    (f:Z→ℝ≥0∞) (hf:Measurable f) :
    (∫⁻ b in {b:WithLp 2 (Z×Z)|b.fst∈K ∧ b.snd∈K},f b.fst*f b.snd)=
      (∫⁻ z in K,f z)*(∫⁻ z in K,f z):=by
  let B:={b:WithLp 2 (Z×Z)|b.fst∈K ∧ b.snd∈K}
  have hB:MeasurableSet B:=(hK.preimage (WithLp.continuous_fst 2 Z Z).measurable).inter
    (hK.preimage (WithLp.continuous_snd 2 Z Z).measurable)
  have hF:Measurable (fun b:WithLp 2 (Z×Z)=>f b.fst*f b.snd):=
    (hf.comp (WithLp.continuous_fst 2 Z Z).measurable).mul (hf.comp (WithLp.continuous_snd 2 Z Z).measurable)
  have he:=(WithLp.volume_preserving_toLp Z Z).setLIntegral_comp_preimage hB hF
  change (∫⁻ p in K×ˢK,f p.1*f p.2 ∂(volume:Measure Z).prod volume)=
    (∫⁻ b in B,f b.fst*f b.snd) at he
  rw [←he,←Measure.prod_restrict]
  exact lintegral_prod_mul hf.aemeasurable hf.aemeasurable

lemma source_pure_critical_intensity_measurable (n:ℕ) (p:ℕ) (hp:2 ≤ p)
    (alpha:ℝ) (halpha:0<alpha) (Q:ℝ) :
    Measurable (pureCriticalIntensity n p hp alpha halpha Q):=by
  let μ:=FiniteMixture.pure p hp alpha halpha
  exact (measurable_const.mul (physicalValuePdf_measurable (n+2) μ Q)).mul
    (((physicalMean_measurable n (n+2) (Q^2*μ.xi2 Q)).comp
      (measurable_const.mul measurable_id)).ennreal_ofReal)

theorem source_mixed_mark_pair_count_normalizer (n:ℕ) (μ:FiniteMixture) {Q:ℝ}
    (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree)
    (K:Set (EuclideanSpace ℝ (Fin 2))) (hK:MeasurableSet K) :
    (∫⁻ b in {b:ScorePairSpace|b.fst∈K ∧ b.snd∈K},
      mixedCriticalIntensity (n+1) μ Q b.fst*mixedCriticalIntensity (n+1) μ Q b.snd)=
      (∫⁻ J,actualScoreWindowCount (n+2) (centerCoefficients (mixtureCoefficients μ) Q) K
        (fun _ _=>1) J ∂disorderLaw (n+3) μ.maxDegree)^2:=by
  rw [physical_mark_pair_window_product_integral K hK _ (mixedCriticalIntensity_measurable _ μ Q),
    actual_mixed_count_intensity (n+1) μ hQ hnp K hK,pow_two]

theorem source_pure_actual_value_count_intensity (n:ℕ) (p:ℕ) (hp:2 ≤ p)
    (alpha:ℝ) (halpha:0<alpha) {Q:ℝ} (hQ:0<Q) (I:Set ℝ) (hI:MeasurableSet I) :
    let μ:=FiniteMixture.pure p hp alpha halpha
    (∫⁻ J,actualValueWindowCount (n+2) (centerCoefficients (mixtureCoefficients μ) Q) I
      (fun _ _=>1) J ∂disorderLaw (n+3) μ.maxDegree)=
      ∫⁻ h in I,pureCriticalIntensity (n+1) p hp alpha halpha Q h:=by
  dsimp only
  let K:Set (EuclideanSpace ℝ (Fin 2)):={b|b 0∈I}
  have hK:MeasurableSet K:=hI.preimage (EuclideanSpace.proj (0:Fin 2)).continuous.measurable
  have hLine:pureScoreWindow p K=I:=by ext h;rfl
  have hc:=actual_pure_count_intensity (n+1) p hp alpha halpha hQ K hK
  rw [hLine] at hc
  refine (lintegral_congr (fun J=>?_)).trans hc
  simpa only [hLine] using (actual_pure_scoreWindowCount_eq_valueWindowCount (n+2) p hp alpha halpha Q K (fun _ _=>1) J).symm

theorem source_pure_mark_pair_count_normalizer (n:ℕ) (p:ℕ) (hp:2 ≤ p)
    (alpha:ℝ) (halpha:0<alpha) {Q:ℝ} (hQ:0<Q)
    (I:Set ℝ) (hI:MeasurableSet I) :
    let μ:=FiniteMixture.pure p hp alpha halpha
    (∫⁻ b in {b:ValuePairSpace|b.fst∈I ∧ b.snd∈I},
      pureCriticalIntensity (n+1) p hp alpha halpha Q b.fst*
        pureCriticalIntensity (n+1) p hp alpha halpha Q b.snd)=
      (∫⁻ J,actualValueWindowCount (n+2) (centerCoefficients (mixtureCoefficients μ) Q) I
        (fun _ _=>1) J ∂disorderLaw (n+3) μ.maxDegree)^2:=by
  dsimp only
  rw [physical_mark_pair_window_product_integral I hI _ (source_pure_critical_intensity_measurable _ p hp alpha halpha Q),
    source_pure_actual_value_count_intensity n p hp alpha halpha hQ I hI,pow_two]

end
end SlowEquilibration.PairConditionalDeterminantMoments

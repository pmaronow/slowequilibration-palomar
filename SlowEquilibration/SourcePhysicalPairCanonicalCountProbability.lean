-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairCanonicalVariance

/-! Chebyshev's inequality for the literal retained critical-point count.
The `L²` premise is discharged by the actual retained ordered-pair integral,
and the expectation is the first moment from the marked Kac--Rice formula. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity SphericalPairChartKacRice
open scoped ENNReal Topology ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 600000

/-- A lower-half event forces a deviation of at least half the positive
mean. This is the probability step used in source 11.14. -/
theorem source_below_half_probability_of_variance_bound
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (a v : ℝ)
    (hX : MemLp X 2 ν) (ha : 0 < a)
    (hMean : (∫ ω, X ω ∂ν) = a)
    (hVar : ProbabilityTheory.variance X ν ≤ v) :
    ν {ω | X ω < a/2} ≤ ENNReal.ofReal (v/(a/2)^2) := by
  have hsubset : {ω | X ω < a/2} ⊆
      {ω | a/2 ≤ |X ω-(∫ x, X x ∂ν)|} := by
    intro ω hw
    change X ω < a/2 at hw
    change a/2 ≤ |X ω-(∫ x, X x ∂ν)|
    rw [hMean]
    have hneg : X ω-a < 0 := by linarith
    rw [abs_of_neg hneg]
    linarith
  have hCheb := ProbabilityTheory.meas_ge_le_variance_div_sq hX (half_pos ha)
  have hDiv : ProbabilityTheory.variance X ν/(a/2)^2 ≤ v/(a/2)^2 :=
    div_le_div_of_nonneg_right hVar (sq_nonneg _)
  calc
    ν {ω | X ω < a/2} ≤
        ν {ω | a/2 ≤ |X ω-(∫ x, X x ∂ν)|} := measure_mono hsubset
    _ ≤ ENNReal.ofReal (ProbabilityTheory.variance X ν/(a/2)^2) := by
      simpa only using hCheb
    _ ≤ ENNReal.ofReal (v/(a/2)^2) := ENNReal.ofReal_le_ofReal hDiv

/-- Apply the abstract deviation inequality to the original mixed-model
retained count and its exact Kac--Rice expectation. -/
theorem source_actual_retained_score_window_below_half_probability
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K)
    (κ C ε η E G v : ℝ)
    (ha : 0 < sourceRetainedScoreWindowMean n μ Q K κ C ε η E G)
    (hLp : MemLp
      (fun J => (sourceRetainedScoreWindowCount n
        (centerCoefficients (mixtureCoefficients μ) Q) K κ C ε η E G J).toReal)
      2 (disorderLaw (n+1) μ.maxDegree))
    (hVar : ProbabilityTheory.variance
      (fun J => (sourceRetainedScoreWindowCount n
        (centerCoefficients (mixtureCoefficients μ) Q) K κ C ε η E G J).toReal)
      (disorderLaw (n+1) μ.maxDegree) ≤ v) :
    let a := sourceRetainedScoreWindowMean n μ Q K κ C ε η E G
    (disorderLaw (n+1) μ.maxDegree)
      {J | (sourceRetainedScoreWindowCount n
        (centerCoefficients (mixtureCoefficients μ) Q) K κ C ε η E G J).toReal < a/2} ≤
      ENNReal.ofReal (v/(a/2)^2) := by
  dsimp only
  exact source_below_half_probability_of_variance_bound
    (disorderLaw (n+1) μ.maxDegree)
    (fun J => (sourceRetainedScoreWindowCount n
      (centerCoefficients (mixtureCoefficients μ) Q) K κ C ε η E G J).toReal)
    (sourceRetainedScoreWindowMean n μ Q K κ C ε η E G) v
    hLp ha (source_actual_retained_count_expectation_eq_mean
      n hn μ hQ hnp K hK κ C ε η E G) hVar

end
end SlowEquilibration.PairConditionalDeterminantMoments

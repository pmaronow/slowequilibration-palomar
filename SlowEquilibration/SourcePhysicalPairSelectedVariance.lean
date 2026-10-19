-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairSelectedRealSecondMoment
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! Identify the finite real moments of the actual retained cardinality
with Mathlib's expectation and variance, then apply the actual pair bound. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalMorse
open SphericalPairCountGluing SphericalForm
open scoped ENNReal ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem source_variance_of_finite_ennreal_count {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (X : Ω → ℝ≥0∞)
    (hX : AEMeasurable X ν) (hXfinite : ∀ᵐ ω ∂ν, X ω < ⊤)
    (hSecondFinite : (∫⁻ ω, X ω ^ 2 ∂ν) < ⊤) :
    ProbabilityTheory.variance (fun ω => (X ω).toReal) ν =
      (∫⁻ ω, X ω ^ 2 ∂ν).toReal - (∫⁻ ω, X ω ∂ν).toReal ^ 2 := by
  have hRealMeas : AEStronglyMeasurable (fun ω => (X ω).toReal) ν :=
    hX.ennreal_toReal.aestronglyMeasurable
  have hSqMeas : AEStronglyMeasurable (fun ω => (X ω).toReal ^ 2) ν :=
    hRealMeas.pow 2
  have hSqNonneg : 0 ≤ᵐ[ν] (fun ω => (X ω).toReal ^ 2) :=
    ae_of_all ν (fun _ => sq_nonneg _)
  have hSqEq :
      (∫⁻ ω, ENNReal.ofReal ((X ω).toReal ^ 2) ∂ν) =
        ∫⁻ ω, X ω ^ 2 ∂ν := by
    apply lintegral_congr_ae
    filter_upwards [hXfinite] with ω hω
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hω.ne]
  have hSqInt : Integrable (fun ω => (X ω).toReal ^ 2) ν :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hSqMeas hSqNonneg).mp
      (by rw [hSqEq]; exact hSecondFinite.ne)
  have hMemLp : MemLp (fun ω => (X ω).toReal) 2 ν :=
    (memLp_two_iff_integrable_sq hRealMeas).mpr hSqInt
  have hFirstEq :
      (∫ ω, (X ω).toReal ∂ν) = (∫⁻ ω, X ω ∂ν).toReal :=
    integral_toReal hX hXfinite
  have hSecondEq :
      (∫ ω, (X ω).toReal ^ 2 ∂ν) = (∫⁻ ω, X ω ^ 2 ∂ν).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae hSqNonneg hSqMeas,hSqEq]
  rw [ProbabilityTheory.variance_eq_sub hMemLp]
  simp only [Pi.pow_apply]
  rw [hSecondEq,hFirstEq]

/-- The pair-integral finiteness used in the variance calculation also
gives the actual selected cardinality an `L²` representative. -/
theorem source_memLp_two_of_finite_ennreal_second_lintegral
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (X : Ω → ℝ≥0∞) (hX : AEMeasurable X ν)
    (hXfinite : ∀ᵐ ω ∂ν, X ω < ⊤)
    (hSecondFinite : (∫⁻ ω, X ω ^ 2 ∂ν) < ⊤) :
    MemLp (fun ω => (X ω).toReal) 2 ν := by
  have hRealMeas : AEStronglyMeasurable (fun ω => (X ω).toReal) ν :=
    hX.ennreal_toReal.aestronglyMeasurable
  have hSqMeas : AEStronglyMeasurable (fun ω => (X ω).toReal ^ 2) ν :=
    hRealMeas.pow 2
  have hSqNonneg : 0 ≤ᵐ[ν] (fun ω => (X ω).toReal ^ 2) :=
    ae_of_all ν (fun _ => sq_nonneg _)
  have hSqEq :
      (∫⁻ ω, ENNReal.ofReal ((X ω).toReal ^ 2) ∂ν) =
        ∫⁻ ω, X ω ^ 2 ∂ν := by
    apply lintegral_congr_ae
    filter_upwards [hXfinite] with ω hω
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hω.ne]
  have hSqInt : Integrable (fun ω => (X ω).toReal ^ 2) ν :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hSqMeas hSqNonneg).mp
      (by rw [hSqEq]; exact hSecondFinite.ne)
  exact (memLp_two_iff_integrable_sq hRealMeas).mpr hSqInt

/-- The printed retained normalizer is the ordinary real expectation of
the actual selected critical-point cardinality. -/
theorem source_actual_retained_count_expectation_eq_mean
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K)
    (κ C ε η E G : ℝ) :
    (∫ J, (sourceRetainedScoreWindowCount n
      (centerCoefficients (mixtureCoefficients μ) Q) K κ C ε η E G J).toReal
      ∂disorderLaw (n+1) μ.maxDegree) =
      sourceRetainedScoreWindowMean n μ Q K κ C ε η E G := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hMeas :=
    (sourceRetainedScoreWindowCount_kacRice n hn μ hQ hnp K hK κ C ε η E G).1
  have hCountFiniteAe : ∀ᵐ J ∂disorderLaw (n+1) μ.maxDegree,
      sourceRetainedScoreWindowCount n c K κ C ε η E G J < ⊤ := by
    filter_upwards [actual_sphere_criticalSet_finite_ae n hn μ hQ] with J hfinite
    rw [sourceRetainedScoreWindowCount_eq_selected_set_card
      c J K κ C ε η E G hfinite]
    simp
  simpa only [sourceRetainedScoreWindowMean] using
    (integral_toReal hMeas hCountFiniteAe)

theorem source_actual_retained_count_variance_eq_moments
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree)
    {κ C ε η E G ω δ ρ : ℝ} (hκ : 0 < κ) (hC : 0 < C)
    (hη : η ≤ sourceCriticalCollarOverlapLoss κ C) (hωG : ω < G/2)
    (hδ : 0 < δ) (hδOne : δ ≤ 1) (hε : ε < δ^2) (hδρ : δ ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K)
    (hwindow : ∀ z ∈ K, E-ω ≤ z 0)
    (hpairFinite :
      (∫⁻ J, sourceRetainedMixedPairCount n
        (centerCoefficients (mixtureCoefficients μ) Q) ρ δ K κ C ε η E G J
        ∂disorderLaw (n+1) μ.maxDegree) < ⊤) :
    ProbabilityTheory.variance
      (fun J => (sourceRetainedScoreWindowCount n
        (centerCoefficients (mixtureCoefficients μ) Q) K κ C ε η E G J).toReal)
      (disorderLaw (n+1) μ.maxDegree) =
      sourceRetainedScoreWindowSecondMoment n μ Q K κ C ε η E G -
        (sourceRetainedScoreWindowMean n μ Q K κ C ε η E G)^2 := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let k := 1+(1-ε)/(δ^2-ε)
  have hδSq : δ^2 ≤ 1 := by
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδOne)]
  have hnum : 0 ≤ 1-ε := by linarith
  have hden : 0 < δ^2-ε := sub_pos.mpr hε
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hMeas :=
    (sourceRetainedScoreWindowCount_kacRice n hn μ hQ hnp K hK κ C ε η E G).1
  have hCountFiniteAe : ∀ᵐ J ∂disorderLaw (n+1) μ.maxDegree,
      sourceRetainedScoreWindowCount n c K κ C ε η E G J < ⊤ := by
    filter_upwards [actual_sphere_criticalSet_finite_ae n hn μ hQ] with J hfinite
    rw [sourceRetainedScoreWindowCount_eq_selected_set_card
      c J K κ C ε η E G hfinite]
    simp
  have hUnfilteredFinite := bounded_scoreWindowCount_lintegral_lt_top
    n hn μ hQ K (fun _ _ => 1) 1 (by simp) (by simp)
  have hCountFinite :
      (∫⁻ J, sourceRetainedScoreWindowCount n c K κ C ε η E G J
        ∂disorderLaw (n+1) μ.maxDegree) < ⊤ := by
    apply lt_of_le_of_lt _ hUnfilteredFinite
    exact lintegral_mono (sourceRetainedScoreWindowCount_le_unfiltered
      n c K κ C ε η E G)
  have hLinearFinite : ENNReal.ofReal k *
      (∫⁻ J, sourceRetainedScoreWindowCount n c K κ C ε η E G J
        ∂disorderLaw (n+1) μ.maxDegree) < ⊤ :=
    lt_top_iff_ne_top.mpr
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCountFinite.ne)
  have hSecondFinite :
      (∫⁻ J, (sourceRetainedScoreWindowCount n c K κ C ε η E G J)^2
        ∂disorderLaw (n+1) μ.maxDegree) < ⊤ :=
    lt_of_le_of_lt
      (source_actual_retained_count_integrated_second_moment_bound
        n hn μ hQ hnp hκ hC hη hωG hδ hδOne hε hδρ K hK hwindow)
      (ENNReal.add_lt_top.mpr ⟨hpairFinite,hLinearFinite⟩)
  have hEq := source_variance_of_finite_ennreal_count
    (disorderLaw (n+1) μ.maxDegree)
    (sourceRetainedScoreWindowCount n c K κ C ε η E G)
    hMeas hCountFiniteAe hSecondFinite
  simpa only [sourceRetainedScoreWindowSecondMoment,
    sourceRetainedScoreWindowMean] using hEq

/-- Literal retained critical-point counts are square-integrable whenever
the genuine retained ordered-pair integral is finite. -/
theorem source_actual_retained_count_memLp_two_of_pair_finite
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree)
    {κ C ε η E G ω δ ρ : ℝ} (hκ : 0 < κ) (hC : 0 < C)
    (hη : η ≤ sourceCriticalCollarOverlapLoss κ C) (hωG : ω < G/2)
    (hδ : 0 < δ) (hδOne : δ ≤ 1) (hε : ε < δ^2) (hδρ : δ ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K)
    (hwindow : ∀ z ∈ K, E-ω ≤ z 0)
    (hpairFinite :
      (∫⁻ J, sourceRetainedMixedPairCount n
        (centerCoefficients (mixtureCoefficients μ) Q) ρ δ K κ C ε η E G J
        ∂disorderLaw (n+1) μ.maxDegree) < ⊤) :
    MemLp
      (fun J => (sourceRetainedScoreWindowCount n
        (centerCoefficients (mixtureCoefficients μ) Q) K κ C ε η E G J).toReal)
      2 (disorderLaw (n+1) μ.maxDegree) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let k := 1+(1-ε)/(δ^2-ε)
  have hδSq : δ^2 ≤ 1 := by
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδOne)]
  have hnum : 0 ≤ 1-ε := by linarith
  have hden : 0 < δ^2-ε := sub_pos.mpr hε
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hMeas :=
    (sourceRetainedScoreWindowCount_kacRice n hn μ hQ hnp K hK κ C ε η E G).1
  have hCountFiniteAe : ∀ᵐ J ∂disorderLaw (n+1) μ.maxDegree,
      sourceRetainedScoreWindowCount n c K κ C ε η E G J < ⊤ := by
    filter_upwards [actual_sphere_criticalSet_finite_ae n hn μ hQ] with J hfinite
    rw [sourceRetainedScoreWindowCount_eq_selected_set_card
      c J K κ C ε η E G hfinite]
    simp
  have hUnfilteredFinite := bounded_scoreWindowCount_lintegral_lt_top
    n hn μ hQ K (fun _ _ => 1) 1 (by simp) (by simp)
  have hCountFinite :
      (∫⁻ J, sourceRetainedScoreWindowCount n c K κ C ε η E G J
        ∂disorderLaw (n+1) μ.maxDegree) < ⊤ := by
    apply lt_of_le_of_lt _ hUnfilteredFinite
    exact lintegral_mono (sourceRetainedScoreWindowCount_le_unfiltered
      n c K κ C ε η E G)
  have hLinearFinite : ENNReal.ofReal k *
      (∫⁻ J, sourceRetainedScoreWindowCount n c K κ C ε η E G J
        ∂disorderLaw (n+1) μ.maxDegree) < ⊤ :=
    lt_top_iff_ne_top.mpr
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCountFinite.ne)
  have hSecondFinite :
      (∫⁻ J, (sourceRetainedScoreWindowCount n c K κ C ε η E G J)^2
        ∂disorderLaw (n+1) μ.maxDegree) < ⊤ :=
    lt_of_le_of_lt
      (source_actual_retained_count_integrated_second_moment_bound
        n hn μ hQ hnp hκ hC hη hωG hδ hδOne hε hδρ K hK hwindow)
      (ENNReal.add_lt_top.mpr ⟨hpairFinite,hLinearFinite⟩)
  exact source_memLp_two_of_finite_ennreal_second_lintegral
    (disorderLaw (n+1) μ.maxDegree)
    (sourceRetainedScoreWindowCount n c K κ C ε η E G)
    hMeas hCountFiniteAe hSecondFinite

theorem source_actual_retained_count_variance_of_pair_bound
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree)
    {κ C ε η E G ω δ ρ err : ℝ} (hκ : 0 < κ) (hC : 0 < C)
    (hη : η ≤ sourceCriticalCollarOverlapLoss κ C) (hωG : ω < G/2)
    (hδ : 0 < δ) (hδOne : δ ≤ 1) (hε : ε < δ^2) (hδρ : δ ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K)
    (hwindow : ∀ z ∈ K, E-ω ≤ z 0)
    (hpairFinite :
      (∫⁻ J, sourceRetainedMixedPairCount n
        (centerCoefficients (mixtureCoefficients μ) Q) ρ δ K κ C ε η E G J
        ∂disorderLaw (n+1) μ.maxDegree) < ⊤)
    (hpairBound : sourceRetainedMixedPairMean n μ Q ρ δ K κ C ε η E G ≤
      (1+err)*(sourceRetainedScoreWindowMean n μ Q K κ C ε η E G)^2) :
    let a := sourceRetainedScoreWindowMean n μ Q K κ C ε η E G
    ProbabilityTheory.variance
      (fun J => (sourceRetainedScoreWindowCount n
        (centerCoefficients (mixtureCoefficients μ) Q) K κ C ε η E G J).toReal)
      (disorderLaw (n+1) μ.maxDegree) ≤
      err*a^2+(1+(1-ε)/(δ^2-ε))*a := by
  dsimp only
  rw [source_actual_retained_count_variance_eq_moments
    n hn μ hQ hnp hκ hC hη hωG hδ hδOne hε hδρ K hK hwindow hpairFinite]
  exact (source_actual_retained_count_real_second_moment_of_pair_bound
    n hn μ hQ hnp hκ hC hη hωG hδ hδOne hε hδρ K hK hwindow
    hpairFinite hpairBound).2

end
end SlowEquilibration.PairConditionalDeterminantMoments

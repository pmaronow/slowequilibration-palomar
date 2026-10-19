-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairIntegratedSelectedSecondMoment

/-! Convert the literal integrated selected-count inequality to finite real
moments.  The pair integral is still the actual retained ordered-pair count;
the later sharp pair theorem supplies its quantitative upper bound. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Set
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalMorse
open SphericalPairCountGluing SphericalForm
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 700000

def sourceRetainedScoreWindowSecondMoment (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (κ C ε η E G : ℝ) : ℝ :=
  (∫⁻ J, (sourceRetainedScoreWindowCount n
    (centerCoefficients (mixtureCoefficients μ) Q) K κ C ε η E G J)^2
    ∂disorderLaw (n+1) μ.maxDegree).toReal

/-- Finiteness of the actual retained ordered-pair integral follows from
the source unfiltered pair bound, before converting its value to a real. -/
theorem source_retained_pair_lintegral_lt_top_of_unfiltered_bound
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (ρ cut : ℝ) (K : Set (EuclideanSpace ℝ (Fin 2)))
    (κ C ε η E G A : ℝ)
    (hpair : let c := centerCoefficients (mixtureCoefficients μ) Q
      (∫⁻ J, actualSpherePairCount n c ρ
        (actualMixedPairWindowMark c K cut (fun _ _ => 1)) J
        ∂disorderLaw (n+1) μ.maxDegree) ≤
        ENNReal.ofReal A *
          (∫⁻ J, actualScoreWindowCount n c K (fun _ _ => 1) J
            ∂disorderLaw (n+1) μ.maxDegree)^2) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, sourceRetainedMixedPairCount n c ρ cut K κ C ε η E G J
      ∂disorderLaw (n+1) μ.maxDegree) < ⊤ := by
  dsimp only at hpair ⊢
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hB := bounded_scoreWindowCount_lintegral_lt_top n hn μ hQ K
    (fun _ _ => 1) 1 (by simp) (by simp)
  have hR : ENNReal.ofReal A *
      (∫⁻ J, actualScoreWindowCount n c K (fun _ _ => 1) J
        ∂disorderLaw (n+1) μ.maxDegree)^2 < ⊤ :=
    lt_top_iff_ne_top.mpr
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hB.ne))
  calc
    _ ≤ ∫⁻ J, actualSpherePairCount n c ρ
        (actualMixedPairWindowMark c K cut (fun _ _ => 1)) J
        ∂disorderLaw (n+1) μ.maxDegree :=
      source_mixed_actual_pair_filter_count_le n c ρ cut K
        (sourceSelectionPairMark c κ C ε η E G)
        (sourceSelectionPairMark_le_one c κ C ε η E G)
    _ ≤ ENNReal.ofReal A *
        (∫⁻ J, actualScoreWindowCount n c K (fun _ _ => 1) J
          ∂disorderLaw (n+1) μ.maxDegree)^2 := hpair
    _ < ⊤ := hR

/-- The finite real second moment of the actual retained count is bounded
by the finite actual retained-pair mean and the simplex-cluster linear term. -/
theorem source_actual_retained_count_real_second_moment_bound
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
    sourceRetainedScoreWindowSecondMoment n μ Q K κ C ε η E G ≤
      sourceRetainedMixedPairMean n μ Q ρ δ K κ C ε η E G +
        (1+(1-ε)/(δ^2-ε))*
          sourceRetainedScoreWindowMean n μ Q K κ C ε η E G := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let k := 1+(1-ε)/(δ^2-ε)
  have hden : 0 < δ^2-ε := sub_pos.mpr hε
  have hδSq : δ^2 ≤ 1 := by
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδOne)]
  have hnum : 0 ≤ 1-ε := by linarith
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hUnfilteredFinite := bounded_scoreWindowCount_lintegral_lt_top
    n hn μ hQ K (fun _ _ => 1) 1 (by simp) (by simp)
  have hCountFinite :
      (∫⁻ J, sourceRetainedScoreWindowCount n c K κ C ε η E G J
        ∂disorderLaw (n+1) μ.maxDegree) < ⊤ := by
    apply lt_of_le_of_lt _ hUnfilteredFinite
    exact lintegral_mono (sourceRetainedScoreWindowCount_le_unfiltered
      n c K κ C ε η E G)
  have hLinearFinite :
      ENNReal.ofReal k *
        (∫⁻ J, sourceRetainedScoreWindowCount n c K κ C ε η E G J
          ∂disorderLaw (n+1) μ.maxDegree) < ⊤ :=
    lt_top_iff_ne_top.mpr
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCountFinite.ne)
  have hReal := ENNReal.toReal_mono
    (ENNReal.add_lt_top.mpr ⟨hpairFinite,hLinearFinite⟩).ne
    (source_actual_retained_count_integrated_second_moment_bound
      n hn μ hQ hnp hκ hC hη hωG hδ hδOne hε hδρ K hK hwindow)
  change sourceRetainedScoreWindowSecondMoment n μ Q K κ C ε η E G ≤
    sourceRetainedMixedPairMean n μ Q ρ δ K κ C ε η E G +
      k*sourceRetainedScoreWindowMean n μ Q K κ C ε η E G
  unfold sourceRetainedScoreWindowSecondMoment sourceRetainedMixedPairMean
    sourceRetainedScoreWindowMean
  change _ ≤ (_ + ENNReal.ofReal k * _).toReal at hReal
  rw [ENNReal.toReal_add hpairFinite.ne hLinearFinite.ne,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hk] at hReal
  exact hReal

/-- Apply an actual retained ordered-pair mean bound to the real square
moment.  Here `a` is the retained first moment, never the unfiltered mean. -/
theorem source_actual_retained_count_real_second_moment_of_pair_bound
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
    let second := sourceRetainedScoreWindowSecondMoment n μ Q K κ C ε η E G
    second ≤ (1+err)*a^2+(1+(1-ε)/(δ^2-ε))*a ∧
      second-a^2 ≤ err*a^2+(1+(1-ε)/(δ^2-ε))*a := by
  dsimp only
  have hs := source_actual_retained_count_real_second_moment_bound n hn μ hQ hnp
    hκ hC hη hωG hδ hδOne hε hδρ K hK hwindow hpairFinite
  constructor
  · exact hs.trans (add_le_add_left hpairBound _)
  · nlinarith [hs,hpairBound]

end
end SlowEquilibration.PairConditionalDeterminantMoments

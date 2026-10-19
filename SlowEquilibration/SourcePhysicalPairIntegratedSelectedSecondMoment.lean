-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairSelectedSquareToPairCount
public import SlowEquilibration.SourcePhysicalPairRetainedSharpBounds

/-! Integrate the actual selected finite-set square decomposition under the
original Gaussian tensor law. The pair term is the literal retained sphere
pair count, and the linear coefficient is the source simplex constant. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Set
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalMorse
open SphericalPairCountGluing SphericalForm
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 700000

theorem source_actual_retained_count_integrated_second_moment_bound
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree)
    {κ C ε η E G ω δ ρ : ℝ} (hκ : 0 < κ) (hC : 0 < C)
    (hη : η ≤ sourceCriticalCollarOverlapLoss κ C) (hωG : ω < G/2)
    (hδ : 0 < δ) (hδOne : δ ≤ 1) (hε : ε < δ^2) (hδρ : δ ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K)
    (hwindow : ∀ z ∈ K, E-ω ≤ z 0) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let k := 1+(1-ε)/(δ^2-ε)
    (∫⁻ J, (sourceRetainedScoreWindowCount n c K κ C ε η E G J)^2
      ∂disorderLaw (n+1) μ.maxDegree) ≤
      (∫⁻ J, sourceRetainedMixedPairCount n c ρ δ K κ C ε η E G J
        ∂disorderLaw (n+1) μ.maxDegree) +
      ENNReal.ofReal k *
        (∫⁻ J, sourceRetainedScoreWindowCount n c K κ C ε η E G J
          ∂disorderLaw (n+1) μ.maxDegree) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let k := 1+(1-ε)/(δ^2-ε)
  have hδsq : δ^2 ≤ 1 := by
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδOne)]
  have hnum : 0 ≤ 1-ε := by linarith
  have hden : 0 < δ^2-ε := sub_pos.mpr hε
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hpoint : ∀ᵐ J ∂disorderLaw (n+1) μ.maxDegree,
      (sourceRetainedScoreWindowCount n c K κ C ε η E G J)^2 ≤
        sourceRetainedMixedPairCount n c ρ δ K κ C ε η E G J +
          ENNReal.ofReal k * sourceRetainedScoreWindowCount n c K κ C ε η E G J := by
    filter_upwards [actual_sphere_criticalSet_finite_ae n hn μ hQ] with J hfinite
    let s := (sourceSelectedScoreWindowSet_finite c J K κ C ε η E G hfinite).toFinset
    let a := sourceRetainedScoreWindowCount n c K κ C ε η E G J
    let p := sourceRetainedMixedPairCount n c ρ δ K κ C ε η E G J
    have ha : a = (s.card:ℝ≥0∞) :=
      sourceRetainedScoreWindowCount_eq_selected_set_card c J K κ C ε η E G hfinite
    have hp : p < ⊤ := sourceRetainedMixedPairCount_lt_top_of_finite c J ρ δ K
      κ C ε η E G hfinite
    have hsquare := source_actual_selected_square_le_literal_retained_pair_count
      c J hκ hC hη hωG hδ hδOne hε hδρ K hwindow hfinite
    have hcast :
        ENNReal.ofReal ((s.card:ℝ)^2) = a^2 := by
      rw [ha]
      simp [ENNReal.ofReal_pow (Nat.cast_nonneg _) 2]
    have hright :
        ENNReal.ofReal (p.toReal+k*(s.card:ℝ)) = p+ENNReal.ofReal k*a := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg
        (mul_nonneg hk (Nat.cast_nonneg _)),ENNReal.ofReal_toReal hp.ne,
        ENNReal.ofReal_mul hk,ha]
      simp
    calc
      a^2 = ENNReal.ofReal ((s.card:ℝ)^2) := hcast.symm
      _ ≤ ENNReal.ofReal (p.toReal+k*(s.card:ℝ)) := ENNReal.ofReal_le_ofReal hsquare
      _ = p+ENNReal.ofReal k*a := hright
  have hcountMeas :=
    (sourceRetainedScoreWindowCount_kacRice n hn μ hQ hnp K hK κ C ε η E G).1
  calc
    (∫⁻ J, (sourceRetainedScoreWindowCount n c K κ C ε η E G J)^2
      ∂disorderLaw (n+1) μ.maxDegree) ≤
      ∫⁻ J, (sourceRetainedMixedPairCount n c ρ δ K κ C ε η E G J +
        ENNReal.ofReal k * sourceRetainedScoreWindowCount n c K κ C ε η E G J)
        ∂disorderLaw (n+1) μ.maxDegree := lintegral_mono_ae hpoint
    _ = (∫⁻ J, sourceRetainedMixedPairCount n c ρ δ K κ C ε η E G J
        ∂disorderLaw (n+1) μ.maxDegree) +
        ENNReal.ofReal k *
          (∫⁻ J, sourceRetainedScoreWindowCount n c K κ C ε η E G J
            ∂disorderLaw (n+1) μ.maxDegree) := by
      rw [lintegral_add_right' _ (hcountMeas.const_mul (ENNReal.ofReal k))]
      rw [lintegral_const_mul'' _ hcountMeas]

end
end SlowEquilibration.PairConditionalDeterminantMoments

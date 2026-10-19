-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairPureSelectedSquareToPairCount

/-! Integrate the actual pure value-window selected square inequality under
the original Gaussian tensor law. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Set
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalMorse
open SphericalPairCountGluing SphericalPairMarkedWindows SphericalForm
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 700000

theorem source_actual_retained_pure_count_integrated_second_moment_bound
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    {κ C ε η E G ω cut ρ : ℝ} (hκ : 0 < κ) (hC : 0 < C)
    (hη : η ≤ sourceCriticalCollarOverlapLoss κ C) (hωG : ω < G/2)
    (hcut : 0 < cut) (hcutOne : cut ≤ 1) (hε : ε < cut^2)
    (hcutρ : cut ≤ ρ)
    (I : Set ℝ) (hI : MeasurableSet I)
    (hwindow : ∀ z ∈ I, E-ω ≤ z) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let k := 1+(1-ε)/(cut^2-ε)
    (∫⁻ J, (sourceRetainedValueWindowCount n c I κ C ε η E G J)^2
      ∂disorderLaw (n+1) μ.maxDegree) ≤
      (∫⁻ J, sourceRetainedPurePairCount n c ρ cut I κ C ε η E G J
        ∂disorderLaw (n+1) μ.maxDegree) +
      ENNReal.ofReal k *
        (∫⁻ J, sourceRetainedValueWindowCount n c I κ C ε η E G J
          ∂disorderLaw (n+1) μ.maxDegree) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let k := 1+(1-ε)/(cut^2-ε)
  have hcutSq : cut^2 ≤ 1 := by
    nlinarith [mul_nonneg hcut.le (sub_nonneg.mpr hcutOne)]
  have hnum : 0 ≤ 1-ε := by linarith
  have hden : 0 < cut^2-ε := sub_pos.mpr hε
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hpoint : ∀ᵐ J ∂disorderLaw (n+1) μ.maxDegree,
      (sourceRetainedValueWindowCount n c I κ C ε η E G J)^2 ≤
        sourceRetainedPurePairCount n c ρ cut I κ C ε η E G J+
          ENNReal.ofReal k*sourceRetainedValueWindowCount n c I κ C ε η E G J := by
    filter_upwards [actual_sphere_criticalSet_finite_ae n hn μ hQ] with J hfinite
    let s := (sourceSelectedValueWindowSet_finite c J I κ C ε η E G hfinite).toFinset
    let count := sourceRetainedValueWindowCount n c I κ C ε η E G J
    let pair := sourceRetainedPurePairCount n c ρ cut I κ C ε η E G J
    have hCount : count = (s.card:ℝ≥0∞) :=
      sourceRetainedValueWindowCount_eq_selected_set_card c J I κ C ε η E G hfinite
    have hPairFinite : pair < ⊤ := sourceRetainedPurePairCount_lt_top_of_finite
      c J ρ cut I κ C ε η E G hfinite
    have hSquare := source_actual_selected_pure_square_le_literal_retained_pair_count
      c J hκ hC hη hωG hcut hcutOne hε hcutρ I hwindow hfinite
    have hCast : ENNReal.ofReal ((s.card:ℝ)^2) = count^2 := by
      rw [hCount]
      simp [ENNReal.ofReal_pow (Nat.cast_nonneg _) 2]
    have hRight : ENNReal.ofReal (pair.toReal+k*(s.card:ℝ)) =
        pair+ENNReal.ofReal k*count := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg
        (mul_nonneg hk (Nat.cast_nonneg _)),ENNReal.ofReal_toReal hPairFinite.ne,
        ENNReal.ofReal_mul hk,hCount]
      simp
    calc
      count^2 = ENNReal.ofReal ((s.card:ℝ)^2) := hCast.symm
      _ ≤ ENNReal.ofReal (pair.toReal+k*(s.card:ℝ)) := ENNReal.ofReal_le_ofReal hSquare
      _ = pair+ENNReal.ofReal k*count := hRight
  have hCountMeas :=
    (sourceRetainedValueWindowCount_kacRice n hn μ hQ I hI κ C ε η E G).1
  calc
    (∫⁻ J, (sourceRetainedValueWindowCount n c I κ C ε η E G J)^2
      ∂disorderLaw (n+1) μ.maxDegree) ≤
      ∫⁻ J, (sourceRetainedPurePairCount n c ρ cut I κ C ε η E G J+
        ENNReal.ofReal k*sourceRetainedValueWindowCount n c I κ C ε η E G J)
        ∂disorderLaw (n+1) μ.maxDegree := lintegral_mono_ae hpoint
    _ = (∫⁻ J, sourceRetainedPurePairCount n c ρ cut I κ C ε η E G J
        ∂disorderLaw (n+1) μ.maxDegree)+
        ENNReal.ofReal k*
          (∫⁻ J, sourceRetainedValueWindowCount n c I κ C ε η E G J
            ∂disorderLaw (n+1) μ.maxDegree) := by
      rw [lintegral_add_right' _ (hCountMeas.const_mul (ENNReal.ofReal k))]
      rw [lintegral_const_mul'' _ hCountMeas]

end
end SlowEquilibration.PairConditionalDeterminantMoments

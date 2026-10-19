-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureActualUpperTailAllCounts

/-! In a pure field the retained radial score upper tail is exactly the
same original-field count as the retained clipped value upper tail. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory SphericalModel SphericalGaussianJet
open SlowEquilibration.PairConditionalDeterminantMoments
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 450000

theorem sourcePureCenteredRawUpperTail_pureScoreWindow
    (n p : ℕ) (hp : 2 ≤ p) (E δ : ℝ) (m : ℕ → ℝ) (t : ℝ) :
    pureScoreWindow p
      {b : EuclideanSpace ℝ (Fin 2) |
        b 0 ∈ sourcePureCenteredRawUpperTailNormalizedWindow n m t ∧
        b 1 ∈ Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))} =
      sourcePureCenteredUpperTailNormalizedWindow n m E δ t := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  ext b
  simp only [pureScoreWindow,pureScoreLine,Set.mem_preimage,Set.mem_ofPred_eq,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  change (m (n+1)+t ≤ ((n+3 : ℕ) : ℝ)*b ∧
    (p : ℝ)*b ∈ Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))) ↔
    (m (n+1)+t ≤ ((n+3 : ℕ) : ℝ)*b ∧
      ((n+3 : ℕ) : ℝ)*b ∈
        Ioo (((n+3 : ℕ) : ℝ)*(E-δ)) (((n+3 : ℕ) : ℝ)*(E+δ)))
  have hN : (0 : ℝ) < (n+3 : ℕ) := by positivity
  constructor
  · intro hb
    exact ⟨hb.1,
      ⟨mul_lt_mul_of_pos_left (lt_of_mul_lt_mul_left hb.2.1 hp0.le) hN,
        mul_lt_mul_of_pos_left (lt_of_mul_lt_mul_left hb.2.2 hp0.le) hN⟩⟩
  · intro hb
    exact ⟨hb.1,
      ⟨mul_lt_mul_of_pos_left (lt_of_mul_lt_mul_left hb.2.1 hN.le) hp0,
        mul_lt_mul_of_pos_left (lt_of_mul_lt_mul_left hb.2.2 hN.le) hp0⟩⟩

theorem sourcePureRetainedRawScoreUpperTail_eq_clippedValueWindow
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (Q E δ : ℝ) (m : ℕ → ℝ) (t κ C ε η G : ℝ)
    (J : Disorder (n+3) (FiniteMixture.pure p hp a ha).maxDegree) :
    let c := centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp a ha)) Q
    sourceRetainedScoreWindowCount (n+2) c
      {b : EuclideanSpace ℝ (Fin 2) |
        b 0 ∈ sourcePureCenteredRawUpperTailNormalizedWindow n m t ∧
        b 1 ∈ Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))}
      κ C ε η E G J =
    sourceRetainedValueWindowCount (n+2) c
      (sourcePureCenteredUpperTailNormalizedWindow n m E δ t)
      κ C ε η E G J := by
  dsimp only
  unfold sourceRetainedScoreWindowCount sourceRetainedValueWindowCount
  rw [actual_pure_scoreWindowCount_eq_valueWindowCount (n+2) p hp a ha Q]
  rw [sourcePureCenteredRawUpperTail_pureScoreWindow n p hp E δ m t]

theorem sourcePureRetainedRawScoreUpperTail_mean_eq_clippedValueWindow
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (Q E δ : ℝ) (m : ℕ → ℝ) (t κ C ε η G : ℝ) :
    let μ := FiniteMixture.pure p hp a ha
    (∫⁻ J, sourceRetainedScoreWindowCount (n+2)
      (centerCoefficients (mixtureCoefficients μ) Q)
      {b : EuclideanSpace ℝ (Fin 2) |
        b 0 ∈ sourcePureCenteredRawUpperTailNormalizedWindow n m t ∧
        b 1 ∈ Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))}
      κ C ε η E G J ∂disorderLaw (n+3) μ.maxDegree).toReal =
    sourceRetainedValueWindowMean (n+2) μ Q
      (sourcePureCenteredUpperTailNormalizedWindow n m E δ t)
      κ C ε η E G := by
  dsimp only
  unfold sourceRetainedValueWindowMean
  congr 1
  apply lintegral_congr
  intro J
  exact sourcePureRetainedRawScoreUpperTail_eq_clippedValueWindow
    n p hp a ha Q E δ m t κ C ε η G J

end SlowEquilibration.SphericalMarkedWindows

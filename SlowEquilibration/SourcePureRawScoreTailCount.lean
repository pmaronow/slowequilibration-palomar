-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureCriticalActualTailBridge

/-! The pure Euler score-line identity transfers a physical upper-tail
critical count to the original raw energy and radial score marks. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory SphericalModel SphericalGaussianJet
open SlowEquilibration.PairConditionalDeterminantMoments
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 450000

def sourcePureCenteredRawUpperTailNormalizedWindow
    (n : ℕ) (m : ℕ → ℝ) (t : ℝ) : Set ℝ :=
  (fun b : ℝ => ((n+3 : ℕ) : ℝ)*b) ⁻¹' Ici (m (n+1)+t)

theorem sourcePureCenteredRawScoreUpperTail_eq_clippedValueWindow
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (Q E δ : ℝ) (m : ℕ → ℝ) (t : ℝ)
    (J : Disorder (n+3) (FiniteMixture.pure p hp a ha).maxDegree) :
    let c := centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp a ha)) Q
    let V := sourcePureCenteredRawUpperTailNormalizedWindow n m t
    let U := Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))
    actualScoreWindowCount (n+2) c
      {b : EuclideanSpace ℝ (Fin 2) | b 0 ∈ V ∧ b 1 ∈ U}
      (fun _ _ => 1) J =
    actualValueWindowCount (n+2) c
      (sourcePureCenteredUpperTailNormalizedWindow n m E δ t)
      (fun _ _ => 1) J := by
  classical
  dsimp only
  rw [actual_pure_scoreWindowCount_eq_valueWindowCount (n+2) p hp a ha Q]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hset : pureScoreWindow p
      {b : EuclideanSpace ℝ (Fin 2) |
        b 0 ∈ sourcePureCenteredRawUpperTailNormalizedWindow n m t ∧
        b 1 ∈ Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))} =
      sourcePureCenteredUpperTailNormalizedWindow n m E δ t := by
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
  rw [hset]

theorem sourcePureCenteredRawScoreUpperTail_mean_eq_criticalTail
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (Q E δ : ℝ) (m : ℕ → ℝ) (t : ℝ) :
    let μ := FiniteMixture.pure p hp a ha
    let U := Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))
    (∫⁻ J, actualScoreWindowCount (n+2)
      (centerCoefficients (mixtureCoefficients μ) Q)
      {b : EuclideanSpace ℝ (Fin 2) |
        b 0 ∈ sourcePureCenteredRawUpperTailNormalizedWindow n m t ∧ b 1 ∈ U}
      (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree).toReal =
    sourcePureTruncatedCriticalTailMean (n+1) p hp a ha Q
      (E-δ) (E+δ) (m (n+1)+t) := by
  dsimp only
  rw [← sourcePureCenteredUpperTailNormalizedWindow_critical_mean
    n p hp a ha Q E δ t m]
  unfold sourceUnfilteredValueWindowMean
  congr 1
  apply lintegral_congr
  intro J
  exact sourcePureCenteredRawScoreUpperTail_eq_clippedValueWindow
    n p hp a ha Q E δ m t J

end SlowEquilibration.SphericalMarkedWindows

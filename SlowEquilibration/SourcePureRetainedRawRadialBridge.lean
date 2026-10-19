-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureCriticalRawRadialGroundLimit

/-! Source §11.13 uses a selected count; the pure Euler identity transfers
that selected count from a raw value/radial window to the centered clipped
scalar window without changing the samplewise selection mark. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set SphericalModel SphericalGaussianJet
open SlowEquilibration.PairConditionalDeterminantMoments
open scoped ENNReal Topology
set_option autoImplicit false

theorem sourcePureCenteredRawScoreWindow_eq_clippedValueWindow_weighted
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (Q E δ : ℝ) (m : ℕ → ℝ) (L R : ℝ)
    (psi : Disorder (n+3) (FiniteMixture.pure p hp a ha).maxDegree →
      Vector (n+3) → ℝ≥0∞)
    (J : Disorder (n+3) (FiniteMixture.pure p hp a ha).maxDegree) :
    let c := centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp a ha)) Q
    let V := sourcePureCenteredRawNormalizedWindow n m L R
    let U := Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))
    actualScoreWindowCount (n+2) c
      {b : EuclideanSpace ℝ (Fin 2) | b 0 ∈ V ∧ b 1 ∈ U}
      psi J =
    actualValueWindowCount (n+2) c
      (sourcePureCenteredNormalizedWindow n m E δ L R) psi J := by
  classical
  dsimp only
  rw [actual_pure_scoreWindowCount_eq_valueWindowCount (n+2) p hp a ha Q]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hN : (0 : ℝ) < (n+3 : ℕ) := by positivity
  have hset : pureScoreWindow p
      {b : EuclideanSpace ℝ (Fin 2) |
        b 0 ∈ sourcePureCenteredRawNormalizedWindow n m L R ∧
        b 1 ∈ Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))} =
      sourcePureCenteredNormalizedWindow n m E δ L R := by
    ext b
    simp only [pureScoreWindow,pureScoreLine,Set.mem_preimage,Set.mem_ofPred_eq,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    change (((n+3 : ℕ) : ℝ)*b ∈ Icc (m (n+1)+L) (m (n+1)+R) ∧
      (p : ℝ)*b ∈ Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))) ↔
      (((n+3 : ℕ) : ℝ)*b ∈ Icc (m (n+1)+L) (m (n+1)+R) ∧
        ((n+3 : ℕ) : ℝ)*b ∈
          Ioo (((n+3 : ℕ) : ℝ)*(E-δ)) (((n+3 : ℕ) : ℝ)*(E+δ)))
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

theorem sourcePureRetainedRawScoreWindow_eq_clippedValueWindow
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (Q E δ : ℝ) (m : ℕ → ℝ) (L R κ C ε η G : ℝ)
    (J : Disorder (n+3) (FiniteMixture.pure p hp a ha).maxDegree) :
    let c := centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp a ha)) Q
    let V := sourcePureCenteredRawNormalizedWindow n m L R
    let U := Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))
    sourceRetainedScoreWindowCount (n+2) c
      {b : EuclideanSpace ℝ (Fin 2) | b 0 ∈ V ∧ b 1 ∈ U}
      κ C ε η E G J =
    sourceRetainedValueWindowCount (n+2) c
      (sourcePureCenteredNormalizedWindow n m E δ L R)
      κ C ε η E G J := by
  dsimp only [sourceRetainedScoreWindowCount,sourceRetainedValueWindowCount]
  exact sourcePureCenteredRawScoreWindow_eq_clippedValueWindow_weighted
    n p hp a ha Q E δ m L R _ J

end SlowEquilibration.SphericalMarkedWindows

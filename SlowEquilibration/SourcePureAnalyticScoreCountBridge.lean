-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureAnalyticCenterGeometry

/-! Pure Euler score-line monotonicity transfers deterministic energy-window
inclusions to the literal original-field unsigned critical counts, even when
the two radial mark sets differ. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory SphericalModel SphericalGaussianJet
open TwoAtomStationarity SphericalTAPCertificate SphericalKacRiceGluing
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 500000
attribute [local instance] Classical.propDecidable

theorem pure_actualScoreWindowCount_mono_of_line
    (N p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) (Q : ℝ)
    (K₁ K₂ : Set (EuclideanSpace ℝ (Fin 2)))
    (hsub : pureScoreWindow p K₁ ⊆ pureScoreWindow p K₂)
    (J : Disorder (N+1) (FiniteMixture.pure p hp a ha).maxDegree) :
    actualScoreWindowCount N
      (centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp a ha)) Q)
      K₁ (fun _ _ => 1) J ≤
    actualScoreWindowCount N
      (centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp a ha)) Q)
      K₂ (fun _ _ => 1) J := by
  rw [actual_pure_scoreWindowCount_eq_valueWindowCount,
    actual_pure_scoreWindowCount_eq_valueWindowCount]
  rw [actualValueWindowCount_eq_indicator,actualValueWindowCount_eq_indicator]
  unfold actualSphereCount
  apply ENNReal.tsum_le_tsum
  intro y
  by_cases hy : actualValue
      (centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp a ha)) Q) J y ∈
      pureScoreWindow p K₁
  · have hy₂ := hsub hy
    simp only [hy,hy₂,ite_true,le_refl]
  · simp only [hy,ite_false,zero_le]

theorem pure_analytic_score_window_subset_selected
    (n p : ℕ) (hp : 2 ≤ p) (E c δ L R : ℝ) (m : ℕ → ℝ)
    (U : Set ℝ)
    (hI : Icc (sourcePureAnalyticCenter (n+3) E c-L)
        (sourcePureAnalyticCenter (n+3) E c+L) ⊆
      Icc (m (n+1)-R) (m (n+1)+R) ∩
        Ioo (((n+3 : ℕ) : ℝ)*(E-δ)) (((n+3 : ℕ) : ℝ)*(E+δ))) :
    pureScoreWindow p
      (physicalEnergyWindow (n+3)
        (Icc (sourcePureAnalyticCenter (n+3) E c-L)
          (sourcePureAnalyticCenter (n+3) E c+L)) U) ⊆
    pureScoreWindow p
      {b : EuclideanSpace ℝ (Fin 2) |
        b 0 ∈ sourcePureCenteredRawNormalizedWindow n m (-R) R ∧
        b 1 ∈ Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))} := by
  intro z hz
  have hN : (0 : ℝ) < (n+3 : ℕ) := by positivity
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hzEnergy : ((n+3 : ℕ) : ℝ)*z ∈
      Icc (sourcePureAnalyticCenter (n+3) E c-L)
        (sourcePureAnalyticCenter (n+3) E c+L) := by
    simpa only [pureScoreWindow,pureScoreLine,physicalEnergyWindow,
      rectangularScoreWindow,Set.mem_preimage,Set.mem_ofPred_eq,
      Matrix.cons_val_zero] using hz.1
  have hSel := hI hzEnergy
  change ((n+3 : ℕ) : ℝ)*z ∈ Icc (m (n+1)-R) (m (n+1)+R) ∧
    (p : ℝ)*z ∈ Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))
  constructor
  · exact hSel.1
  · have hzBox : z ∈ Ioo (E-δ) (E+δ) := by
      constructor
      · exact lt_of_mul_lt_mul_left hSel.2.1 hN.le
      · exact lt_of_mul_lt_mul_left hSel.2.2 hN.le
    exact ⟨mul_lt_mul_of_pos_left hzBox.1 hp0,
      mul_lt_mul_of_pos_left hzBox.2 hp0⟩

end SlowEquilibration.SphericalMarkedWindows

-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureRawRadialUpperTailSameWitness
public import SlowEquilibration.SourcePhysicalPairRetainedCountPartition

/-! A measurable mark and exact first-moment partition for critical points
whose intrinsic Hessian is not strictly negative. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open SphericalPosteriorMaps SphericalForm SphereHessian NegativeDefiniteOperators
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 500000
attribute [local instance] Classical.propDecidable

def actualBadCriticalMark {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (J : Disorder (n+1) P) (x : Vector (n+1)) : ℝ≥0∞ :=
  if criticalNegative n c J x then 0 else 1

theorem actualBadCriticalMark_measurable {P : ℕ} (n : ℕ) (c : Degree P → ℝ) :
    Measurable (fun z : Disorder (n+1) P × Vector (n+1) =>
      actualBadCriticalMark n c z.1 z.2) :=
  Measurable.ite (criticalNegative_measurable n c) measurable_const measurable_const

theorem negativeMark_add_badMark {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (J : Disorder (n+1) P) (x : Vector (n+1)) :
    negativeHessianMark n c J x + actualBadCriticalMark n c J x = 1 := by
  unfold negativeHessianMark actualBadCriticalMark
  split_ifs <;> simp

def actualBadCriticalCount {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (J : Disorder (n+1) P) : ℝ≥0∞ :=
  actualScoreWindowCount n c K (actualBadCriticalMark n c) J

theorem negativeCount_add_badCount {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (J : Disorder (n+1) P) :
    actualNegativeCriticalCount n c K J + actualBadCriticalCount n c K J =
      actualScoreWindowCount n c K (fun _ _ => 1) J := by
  rw [actualNegativeCriticalCount_eq_mark]
  unfold actualBadCriticalCount actualScoreWindowCount
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro x
  exact negativeMark_add_badMark n c J x

theorem pure_negative_mean_add_bad_mean (n p : ℕ) (hp : 2 ≤ p)
    (a : ℝ) (ha : 0 < a) {Q : ℝ} (hQ : 0 < Q)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K) :
    let μ := FiniteMixture.pure p hp a ha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, actualNegativeCriticalCount (n+1) c K J ∂disorderLaw (n+2) μ.maxDegree) +
      (∫⁻ J, actualBadCriticalCount (n+1) c K J ∂disorderLaw (n+2) μ.maxDegree) =
        ∫⁻ J, actualScoreWindowCount (n+1) c K (fun _ _ => 1) J
          ∂disorderLaw (n+2) μ.maxDegree := by
  dsimp only
  rw [← lintegral_add_left' (actual_pure_negative_count_intensity n p hp a ha hQ K hK).1]
  exact lintegral_congr (fun J => negativeCount_add_badCount (n+1) _ K J)


/-- One original-field critical point with a nonnegative Hessian direction
forces the bad marked count to be at least one. -/
theorem pure_bad_critical_probability_le_bad_mean (n p : ℕ) (hp : 2 ≤ p)
    (a : ℝ) (ha : 0 < a) {Q : ℝ} (hQ : 0 < Q)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K) :
    let μ := FiniteMixture.pure p hp a ha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    disorderLaw (n+2) μ.maxDegree
      {J | ∃ x : Vector (n+2), ‖x‖^2=(n+2 : ℕ) ∧
        surfaceGradient (field c J) x=0 ∧ actualScore c J x ∈ K ∧
        ¬ NegativeDefinite (intrinsicHessian (field c J) x)} ≤
      ∫⁻ J, actualBadCriticalCount (n+1) c K J
        ∂disorderLaw (n+2) μ.maxDegree := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let C := actualBadCriticalCount (n+1) c K
  have hC : AEMeasurable C (disorderLaw (n+2) μ.maxDegree) :=
    (actual_pure_score_window_kacRice (n+1) (by omega) p hp a ha hQ K hK
      (actualBadCriticalMark (n+1) c)
      (actualBadCriticalMark_measurable (n+1) c)).1
  have hsub : {J : Disorder (n+2) μ.maxDegree |
      ∃ x : Vector (n+2), ‖x‖^2=(n+2 : ℕ) ∧
        surfaceGradient (field c J) x=0 ∧ actualScore c J x ∈ K ∧
        ¬ NegativeDefinite (intrinsicHessian (field c J) x)} ⊆
      {J | 1 ≤ C J} := by
    rintro J ⟨x,hx,hcrit,hKx,hbad⟩
    have hneg : ¬ criticalNegative (n+1) c J x :=
      (criticalNegative_iff (n+1) c J x hx hcrit).not.mpr hbad
    have ht := ENNReal.le_tsum
      (f := fun y : {y : Vector (n+2) | ‖y‖^2=(n+2 : ℕ) ∧
        surfaceGradient (field c J) y=0 ∧ actualScore c J y ∈ K} =>
        actualBadCriticalMark (n+1) c J y) ⟨x,hx,hcrit,hKx⟩
    simpa only [actualBadCriticalMark,ite_eq_right hneg,actualBadCriticalCount,
      actualScoreWindowCount,C,Set.mem_ofPred_eq] using ht
  apply (measure_mono hsub).trans
  simpa only [one_mul] using mul_meas_ge_le_lintegral₀ hC 1

end SlowEquilibration.SphericalMarkedWindows

-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureRawScoreTailCount
public import SlowEquilibration.SourcePureRetainedCenterNarrowRadial

/-! Source §11.13--11.14 expected upper-tail counts for the original
proper-pure field, centered at the exact unit-tail maximum threshold. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory TwoAtomStationarity SphericalTAPCertificate
open SphericalModel SphericalGaussianJet
open ExpectedTailCentering
open SlowEquilibration.PairConditionalDeterminantMoments
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem sourcePure_actual_critical_upper_tail_mean_limit_of_center
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {δ g : ℝ} (hδ : 0 < δ) (hg : 0 < g)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g ≤
      (p : ℝ)*(markE (FiniteMixture.pure p hp a ha) β x Q-δ))
    (m : ℕ → ℝ) {M : ℝ} (hM : 0 < M)
    (hcenter : ∀ᶠ n : ℕ in atTop,
      tail (pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2 : ℕ)*(markE (FiniteMixture.pure p hp a ha) β x Q-δ))
        ((n+2 : ℕ)*(markE (FiniteMixture.pure p hp a ha) β x Q+δ))) (m n)=1 ∧
      |m n-((n+2 : ℕ)*markE (FiniteMixture.pure p hp a ha) β x Q-
        Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M)
    (t : ℝ) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    Tendsto (fun n : ℕ =>
      sourceUnfilteredValueWindowMean (n+2) μ Q
        (sourcePureCenteredUpperTailNormalizedWindow n m E δ t))
      atTop (𝓝 (Real.exp (-(β*x)*t))) := by
  dsimp only
  let E := markE (FiniteMixture.pure p hp a ha) β x Q
  have hm : E ∈ Ioo (E-δ) (E+δ) := by constructor <;> dsimp [E] <;> linarith
  have ht := sourcePure_truncatedCritical_normalized_tail_limit_of_center
    p hp a ha h hm hg hLeft le_rfl m hM hcenter t
  have ht' := ht.comp (tendsto_add_atTop_nat 1)
  apply ht'.congr'
  exact Filter.Eventually.of_forall fun n => by
    change tail (sourcePureTruncatedCriticalDensity (n+1) p hp a ha Q
      ((n+1+2 : ℕ)*(E-δ)) ((n+1+2 : ℕ)*(E+δ))) (m (n+1)+t) = _
    rw [← sourcePureTruncatedCriticalTailMean_eq_tail (n+1) p hp a ha
      h.overlap_range.1 (E-δ) (E+δ) (m (n+1)+t)]
    exact (sourcePureCenteredUpperTailNormalizedWindow_critical_mean
      n p hp a ha Q E δ t m).symm

theorem sourcePure_actual_raw_score_upper_tail_mean_limit_of_center
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {δ g : ℝ} (hδ : 0 < δ) (hg : 0 < g)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g ≤
      (p : ℝ)*(markE (FiniteMixture.pure p hp a ha) β x Q-δ))
    (m : ℕ → ℝ) {M : ℝ} (hM : 0 < M)
    (hcenter : ∀ᶠ n : ℕ in atTop,
      tail (pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2 : ℕ)*(markE (FiniteMixture.pure p hp a ha) β x Q-δ))
        ((n+2 : ℕ)*(markE (FiniteMixture.pure p hp a ha) β x Q+δ))) (m n)=1 ∧
      |m n-((n+2 : ℕ)*markE (FiniteMixture.pure p hp a ha) β x Q-
        Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M)
    (t : ℝ) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let U := Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))
    Tendsto (fun n : ℕ =>
      (∫⁻ J, actualScoreWindowCount (n+2)
        (centerCoefficients (mixtureCoefficients μ) Q)
        {b : EuclideanSpace ℝ (Fin 2) |
          b 0 ∈ sourcePureCenteredRawUpperTailNormalizedWindow n m t ∧ b 1 ∈ U}
        (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree).toReal)
      atTop (𝓝 (Real.exp (-(β*x)*t))) := by
  dsimp only
  have ht := sourcePure_actual_critical_upper_tail_mean_limit_of_center
    p hp a ha h hδ hg hLeft m hM hcenter t
  apply ht.congr'
  exact Filter.Eventually.of_forall fun n => by
    change sourceUnfilteredValueWindowMean (n+2) (FiniteMixture.pure p hp a ha) Q
      (sourcePureCenteredUpperTailNormalizedWindow n m
        (markE (FiniteMixture.pure p hp a ha) β x Q) δ t) = _
    rw [sourcePureCenteredUpperTailNormalizedWindow_critical_mean]
    exact (sourcePureCenteredRawScoreUpperTail_mean_eq_criticalTail
      n p hp a ha Q (markE (FiniteMixture.pure p hp a ha) β x Q) δ m t).symm

end SlowEquilibration.SphericalMarkedWindows

-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureRetainedTailSqueeze

/-! The literal selected proper-pure original-field upper-tail first
moment has the source exponential limit at the same unit-tail center. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PairConditionalDeterminantMoments
open Set Filter MeasureTheory SphericalModel SphericalGaussianJet
open SphericalMarkedWindows TwoAtomStationarity SphericalTAPCertificate
open ExpectedTailCentering LatitudeGroundTrial
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem sourcePure_centered_window_subset_upper_tail
    (n : ℕ) (m : ℕ → ℝ) (E δ t R : ℝ) :
    sourcePureCenteredNormalizedWindow n m E δ t R ⊆
      sourcePureCenteredUpperTailNormalizedWindow n m E δ t := by
  intro e he
  exact ⟨he.1.1,he.2⟩

theorem source_pure_actual_retained_upper_tail_mean_limit_of_center
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
    (κ C ε η G : ℝ)
    (hwindow : ∀ L R : ℝ, L ≤ R → Tendsto (fun n : ℕ =>
      sourceRetainedValueWindowMean (n+2) (FiniteMixture.pure p hp a ha) Q
        (sourcePureCenteredNormalizedWindow n m
          (markE (FiniteMixture.pure p hp a ha) β x Q) δ L R)
        κ C ε η (markE (FiniteMixture.pure p hp a ha) β x Q) G)
      atTop (𝓝 (Real.exp (-(β*x)*L)-Real.exp (-(β*x)*R))))
    (t : ℝ) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    Tendsto (fun n : ℕ =>
      sourceRetainedValueWindowMean (n+2) μ Q
        (sourcePureCenteredUpperTailNormalizedWindow n m E δ t)
        κ C ε η E G) atTop (𝓝 (Real.exp (-(β*x)*t))) := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let A : ℕ → ℝ := fun n => sourceRetainedValueWindowMean (n+2) μ Q
    (sourcePureCenteredUpperTailNormalizedWindow n m E δ t) κ C ε η E G
  let B : ℕ → ℝ := fun n => sourceUnfilteredValueWindowMean (n+2) μ Q
    (sourcePureCenteredUpperTailNormalizedWindow n m E δ t)
  let W : ℝ → ℕ → ℝ := fun R n => sourceRetainedValueWindowMean (n+2) μ Q
    (sourcePureCenteredNormalizedWindow n m E δ t R) κ C ε η E G
  have hB : Tendsto B atTop (𝓝 (Real.exp (-(β*x)*t))) :=
    sourcePure_actual_critical_upper_tail_mean_limit_of_center
      p hp a ha h hδ hg hLeft m hM hcenter t
  have hW : ∀ R : ℝ, t ≤ R → Tendsto (W R) atTop
      (𝓝 (Real.exp (-(β*x)*t)-Real.exp (-(β*x)*R))) := by
    intro R hR
    exact hwindow t R hR
  have hbounds : ∀ n : ℕ, ∀ R : ℝ, t ≤ R → W R n ≤ A n ∧ A n ≤ B n := by
    intro n R _
    constructor
    · exact sourceRetainedValueWindowMean_mono (n+2) (by omega) μ
        h.overlap_range.1 _ _
        (sourcePure_centered_window_subset_upper_tail n m E δ t R) κ C ε η E G
    · exact sourceRetainedValueWindowMean_le_unfiltered (n+2) (by omega) μ
        h.overlap_range.1 _ κ C ε η E G
  have hb : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  exact retained_tail_tendsto_of_window_limits (β*x) t hb A B W hB hW hbounds

end SlowEquilibration.PairConditionalDeterminantMoments

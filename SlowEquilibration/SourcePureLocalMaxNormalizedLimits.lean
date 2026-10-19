-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureLocalMaxCenteredEnvelope
public import SlowEquilibration.ExpectedCompactNormalizedLimits

/-! The actual normalized pure local-maximum density and upper tail have
the source contact exponential after centering by their own tail-equals-one
threshold. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory TwoAtomStationarity SphericalTAPCertificate
open ExpectedTailCentering
open scoped Topology
set_option maxHeartbeats 400000

theorem sourcePure_truncatedLocalMax_normalized_limits_of_center
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {l r g Z : ℝ}
    (hm : markE (FiniteMixture.pure p hp a ha) β x Q ∈ Ioo l r)
    (hg : 0 < g)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g ≤ (p : ℝ)*l)
    (hRight : (p : ℝ)*r ≤ Z)
    (m : ℕ → ℝ) {M : ℝ} (hM : 0 < M)
    (hcenter : ∀ᶠ n : ℕ in atTop,
      tail (pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) (m n)=1 ∧
      |m n-((n+2 : ℕ)*markE (FiniteMixture.pure p hp a ha) β x Q-
        Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M) :
    let f := fun n : ℕ => pureTruncatedLocalMaxDensity n p hp a ha Q
      ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
    Tendsto (fun n : ℕ => f n (m n)) atTop (𝓝 (β*x)) ∧
    ∀ t : ℝ, Tendsto (fun n : ℕ => tail (f n) (m n+t))
      atTop (𝓝 (Real.exp (-(β*x)*t))) := by
  let f := fun n : ℕ => pureTruncatedLocalMaxDensity n p hp a ha Q
    ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
  have hc : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  have hBound : ∀ᶠ n : ℕ in atTop,
      |m n-((n+2 : ℕ)*markE (FiniteMixture.pure p hp a ha) β x Q-
        Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M := by
    filter_upwards [hcenter] with n hn
    exact hn.2
  obtain ⟨A,hA,hEnv⟩ := sourcePure_truncatedLocalMax_centered_global_ratio_envelope
    p hp a ha h hm hg hLeft hRight m hM hBound
  have hMeas : ∀ᶠ n : ℕ in atTop, Measurable (f n) :=
    Filter.Eventually.of_forall (fun n =>
      pureTruncatedLocalMaxDensity_measurable n p hp a ha Q _ _)
  have hNonneg : ∀ᶠ n : ℕ in atTop, ∀ H : ℝ, 0 ≤ f n H :=
    Filter.Eventually.of_forall (fun n H =>
      pureTruncatedLocalMaxDensity_nonneg n p hp a ha Q _ _ H)
  have hPos : ∀ᶠ n : ℕ in atTop, 0 < f n (m n) := by
    filter_upwards [hEnv] with n hn
    exact hn.1
  have hNorm : ∀ᶠ n : ℕ in atTop, tail (f n) (m n)=1 := by
    filter_upwards [hcenter] with n hn
    exact hn.1
  have hRatio (t : ℝ) : Tendsto (fun n : ℕ => f n (m n+t)/f n (m n))
      atTop (𝓝 (Real.exp (-(β*x)*t))) :=
    sourcePure_truncatedLocalMax_centered_ratio p hp a ha h hm m hM hBound t
  have hEnvelope : ∀ᶠ n : ℕ in atTop, ∀ v : ℝ,
      f n (m n+v)/f n (m n) ≤ A*Real.exp (-(β*x)*v) := by
    filter_upwards [hEnv] with n hn
    exact hn.2
  exact compact_normalized_density_and_tail_limits m hc hc
    hMeas hNonneg hPos hNorm hRatio hEnvelope

end SlowEquilibration.SphericalMarkedWindows

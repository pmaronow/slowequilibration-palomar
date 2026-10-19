-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureLocalMaxCenterSequence
public import SlowEquilibration.SourcePureLocalMaxNormalizedLimits

/-! A constructed proper-pure normalized local-maximum center together with
its true density and upper-tail limits. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter TwoAtomStationarity SphericalTAPCertificate
open ExpectedTailCentering
open scoped Topology

theorem sourcePure_truncatedLocalMax_center_and_limits
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {l r g Z : ℝ}
    (hm : markE (FiniteMixture.pure p hp a ha) β x Q ∈ Ioo l r)
    (hg : 0 < g)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g ≤ (p : ℝ)*l)
    (hRight : (p : ℝ)*r ≤ Z) :
    let E := markE (FiniteMixture.pure p hp a ha) β x Q
    let f := fun n : ℕ => pureTruncatedLocalMaxDensity n p hp a ha Q
      ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
    ∃ n₀ : ℕ, ∃ m : ℕ → ℝ, ∃ M : ℝ, 0 < M ∧
      (∀ n < n₀, m n=(n+2 : ℕ)*E) ∧
      (∀ n ≥ n₀, tail (f n) (m n)=1 ∧
        (∀ y : ℝ, tail (f n) y=1 → y=m n) ∧
        |m n-((n+2 : ℕ)*E-Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M) ∧
      Tendsto (fun n : ℕ => f n (m n)) atTop (𝓝 (β*x)) ∧
      ∀ t : ℝ, Tendsto (fun n : ℕ => tail (f n) (m n+t))
        atTop (𝓝 (Real.exp (-(β*x)*t))) := by
  obtain ⟨n₀,m,M,hM,hFallback,hCenter⟩ :=
    sourcePure_truncatedLocalMax_center_sequence p hp a ha h hm hg hLeft hRight
  have hEvent : ∀ᶠ n : ℕ in atTop,
      tail (pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) (m n)=1 ∧
      |m n-((n+2 : ℕ)*markE (FiniteMixture.pure p hp a ha) β x Q-
        Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M := by
    filter_upwards [eventually_ge_atTop n₀] with n hn
    exact ⟨(hCenter n hn).1,(hCenter n hn).2.2⟩
  obtain ⟨hDensity,hTail⟩ :=
    sourcePure_truncatedLocalMax_normalized_limits_of_center
      p hp a ha h hm hg hLeft hRight m hM hEvent
  exact ⟨n₀,m,M,hM,hFallback,hCenter,hDensity,hTail⟩

end SlowEquilibration.SphericalMarkedWindows

-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureCriticalWindowComparison

/-! The literal all-critical pure count has the same unit-tail center and
exact centered window limits as the original negative-Hessian maxima. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter TwoAtomStationarity SphericalTAPCertificate
open ExpectedTailCentering
open scoped Topology
set_option maxHeartbeats 400000

theorem sourcePure_truncatedCritical_center_count_limits
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
      (∀ L R : ℝ, L ≤ R → Tendsto (fun n : ℕ =>
        sourcePureTruncatedCriticalWindowMean n p hp a ha Q l r (m n+L) (m n+R))
        atTop (𝓝 (Real.exp (-(β*x)*L)-Real.exp (-(β*x)*R)))) := by
  obtain ⟨n₀,m,M,hM,hFallback,hCenter,hLocal⟩ :=
    sourcePure_truncatedLocalMax_center_count_limits p hp a ha h hm hg hLeft hRight
  obtain ⟨C,c,hC,hc,hCompare⟩ :=
    sourcePure_criticalWindowMean_relative_comparison p hp a ha h hm hg hLeft hRight
  refine ⟨n₀,m,M,hM,hFallback,hCenter,?_⟩
  intro L R hLR
  have hDim : Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hExp : Tendsto (fun n : ℕ => Real.exp (-c*(n+2 : ℕ))) atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_atBot.comp (hDim.const_mul_atTop_of_neg (neg_neg_of_pos hc))
  have hFactor : Tendsto (fun n : ℕ => 1+C*Real.exp (-c*(n+2 : ℕ)))
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds.add ((tendsto_const_nhds :
        Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).mul hExp))
  have hLow := hLocal L R hLR
  have hHigh : Tendsto (fun n : ℕ =>
      (1+C*Real.exp (-c*(n+2 : ℕ)))*
        sourcePureTruncatedLocalMaxWindowMean n p hp a ha Q l r (m n+L) (m n+R))
      atTop (𝓝 (Real.exp (-(β*x)*L)-Real.exp (-(β*x)*R))) := by
    simpa only [one_mul] using hFactor.mul hLow
  have hBounds : ∀ᶠ n : ℕ in atTop,
      sourcePureTruncatedLocalMaxWindowMean n p hp a ha Q l r (m n+L) (m n+R) ≤
        sourcePureTruncatedCriticalWindowMean n p hp a ha Q l r (m n+L) (m n+R) ∧
      sourcePureTruncatedCriticalWindowMean n p hp a ha Q l r (m n+L) (m n+R) ≤
        (1+C*Real.exp (-c*(n+2 : ℕ)))*
          sourcePureTruncatedLocalMaxWindowMean n p hp a ha Q l r (m n+L) (m n+R) := by
    filter_upwards [hCompare] with n hn
    exact hn (m n+L) (m n+R)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hLow hHigh
    (hBounds.mono fun _ hn => hn.1) (hBounds.mono fun _ hn => hn.2)

end SlowEquilibration.SphericalMarkedWindows

-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMaximumTailLogWindow
public import SlowEquilibration.ExpectedLogarithmicCentering

/-! The actual physical-energy Kac--Rice upper tail has a unique
normalized centering with the source logarithmic correction. No desired
centering, tail normalization or expected-count limit is an input. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity SphericalModel
open ExpectedTailCentering
open scoped Topology
set_option maxHeartbeats 300000

theorem sourceMaximum_normalized_center (μ : FiniteMixture) {β x Q L R δ : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) (hδ : 0 < δ)
    (hScore : ∀ e∈Icc (markE μ β x Q-δ) (markE μ β x Q+δ),∀ k∈Icc L R,
      (β*x)/2 ≤ sourceEnergySlope μ Q e k ∧ sourceEnergySlope μ Q e k ≤ (β*x+β)/2) :
    ∃ M : ℝ,0 < M ∧ ∀ᶠ n : ℕ in atTop,∃ m : ℝ,
      sourceMaximumEnergyTail n μ Q (Ioo L R) m=1 ∧
      (∀ y : ℝ,sourceMaximumEnergyTail n μ Q (Ioo L R) y=1 → y=m) ∧
      |m-((n+2 : ℕ)*markE μ β x Q-Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M := by
  have hc₀ : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  have hregular : ∀ᶠ n : ℕ in atTop,
      Integrable (sourceMaximumEnergyDensity n μ Q (Ioo L R)) ∧
      Continuous (sourceMaximumEnergyDensity n μ Q (Ioo L R)) ∧
      ∀ H : ℝ,0 < sourceMaximumEnergyDensity n μ Q (Ioo L R) H := by
    filter_upwards [sourceMaximumEnergyDensity_regular μ h hnp hL hm] with n hn
    exact ⟨hn.2.1,hn.1,hn.2.2⟩
  exact logarithmic_normalized_center hc₀ hregular
    (sourceMaximumEnergyTail_log_window μ h hnp hL hm hδ (half_pos hc₀)
      (half_pos (add_pos hc₀ h.beta_pos)).le hScore (by positivity))

/-- The finitely many dimensions before the true normalized center
exists are assigned the source fallback N E₀. -/
theorem sourceMaximum_centering_sequence (μ : FiniteMixture) {β x Q L R δ : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) (hδ : 0 < δ)
    (hScore : ∀ e∈Icc (markE μ β x Q-δ) (markE μ β x Q+δ),∀ k∈Icc L R,
      (β*x)/2 ≤ sourceEnergySlope μ Q e k ∧ sourceEnergySlope μ Q e k ≤ (β*x+β)/2) :
    ∃ n₀ : ℕ,∃ m : ℕ → ℝ,∃ M : ℝ,0 < M ∧
      (∀ n<n₀,m n=(n+2 : ℕ)*markE μ β x Q) ∧
      (∀ n≥n₀,sourceMaximumEnergyTail n μ Q (Ioo L R) (m n)=1 ∧
        (∀ y : ℝ,sourceMaximumEnergyTail n μ Q (Ioo L R) y=1 → y=m n) ∧
        |m n-((n+2 : ℕ)*markE μ β x Q-Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M) := by
  classical
  obtain ⟨M,hM,hEvent⟩ := sourceMaximum_normalized_center μ h hnp hL hm hδ hScore
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp hEvent
  let m : ℕ → ℝ := fun n => if hn : n₀ ≤ n then Classical.choose (hn₀ n hn)
    else (n+2 : ℕ)*markE μ β x Q
  refine ⟨n₀,m,M,hM,?_,?_⟩
  · intro n hn
    simp only [m,dite_eq_right (not_le.mpr hn)]
  · intro n hn
    simpa only [m,dite_eq_left hn] using Classical.choose_spec (hn₀ n hn)

end SlowEquilibration.SphericalMarkedWindows

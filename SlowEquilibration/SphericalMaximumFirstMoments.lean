-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMaximumWindowLimits

/-! Original-field source10.6(a–e): true centering, fixed-energy density
and tail limits, actual maximum/all-critical window means, and both
energy envelopes. The separate global-maximum localization clause(f)
is not included in this first-moment result. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity SphericalModel
open scoped Topology ENNReal
set_option maxHeartbeats 300000

structure SourceMaximumFirstMomentConclusions (μ : FiniteMixture) (β x Q L R : ℝ) where
  center : ℕ → ℝ
  dimension_cutoff : ℕ
  log_constant : ℝ
  log_constant_pos : 0 < log_constant
  finite_prefix : ∀ n < dimension_cutoff,center n=(n+2 : ℕ)*markE μ β x Q
  normalized_tail : ∀ᶠ n : ℕ in atTop,sourceMaximumEnergyTail n μ Q (Ioo L R) (center n)=1
  unique_center : ∀ᶠ n : ℕ in atTop,∀ y : ℝ,sourceMaximumEnergyTail n μ Q (Ioo L R) y=1 → y=center n
  logarithmic_correction : ∀ᶠ n : ℕ in atTop,
    |center n-((n+2 : ℕ)*markE μ β x Q-Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ log_constant
  density_limit : ∀ t : ℝ,Tendsto (fun n : ℕ => sourceMaximumEnergyDensity n μ Q (Ioo L R) (center n+t))
    atTop (𝓝 ((β*x)*Real.exp (-(β*x)*t)))
  tail_limit : ∀ t : ℝ,Tendsto (fun n : ℕ => sourceMaximumEnergyTail n μ Q (Ioo L R) (center n+t))
    atTop (𝓝 (Real.exp (-(β*x)*t)))
  maximum_window_limit : ∀ a b : ℝ,a < b →
    Tendsto (fun n : ℕ => sourceMaximumWindowMean n μ Q (Ioo L R) (center n+a) (center n+b))
      atTop (𝓝 (Real.exp (-(β*x)*a)-Real.exp (-(β*x)*b)))
  critical_window_limit : ∀ a b : ℝ,a < b →
    Tendsto (fun n : ℕ => sourceCriticalWindowMean n μ Q (Ioo L R) (center n+a) (center n+b))
      atTop (𝓝 (Real.exp (-(β*x)*a)-Real.exp (-(β*x)*b)))
  uniform_window_bound : ∀ a b : ℝ,a < b →∃ C : ℝ,0 < C ∧ ∀ n : ℕ,
    sourceMaximumWindowMean n μ Q (Ioo L R) (center n+a) (center n+b) ≤ C ∧
    sourceCriticalWindowMean n μ Q (Ioo L R) (center n+a) (center n+b) ≤ C
  window_mass_finite : ∀ n : ℕ,∀ a b : ℝ,
    sourceMaximumWindowMass n μ Q (Ioo L R) (center n+a) (center n+b) < ⊤ ∧
    sourceCriticalWindowMass n μ Q (Ioo L R) (center n+a) (center n+b) < ⊤
  upper_tail_envelope : ∀ᶠ n : ℕ in atTop,∀ v : ℝ,0 ≤ v →
    sourceMaximumEnergyTail n μ Q (Ioo L R) (center n+v) ≤ Real.exp (-((β*x)/2)*v)
  lower_density_envelope : ∀ᶠ n : ℕ in atTop,∀ v : ℝ,0 ≤ v →
    sourceMaximumEnergyDensity n μ Q (Ioo L R) (center n-v) ≤
      Real.exp ((β*x+β)/2)*Real.exp (((β*x+β)/2)*v)
  lower_density_rate_lt_beta : (β*x+β)/2 < β

/-- Five original-field source conclusions, with no desired count,
centering, tail, ratio, normalized radial law, or limit input. -/
theorem sourceMaximum_first_moments (μ : FiniteMixture) {β x Q L R δ : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) (hδ : 0 < δ)
    (hScore : ∀ e∈Icc (markE μ β x Q-δ) (markE μ β x Q+δ),∀ k∈Icc L R,
      (β*x)/2 ≤ sourceEnergySlope μ Q e k ∧ sourceEnergySlope μ Q e k ≤ (β*x+β)/2) :
    Nonempty (SourceMaximumFirstMomentConclusions μ β x Q L R) := by
  obtain ⟨n₀,m,M,hM,hprefix,hcp,hEvent,hLimits⟩ := sourceMaximum_centering_and_limits μ h hnp hL hm hδ hScore
  have hMax : ∀ a b : ℝ,a < b →
      Tendsto (fun n : ℕ => sourceMaximumWindowMean n μ Q (Ioo L R) (m n+a) (m n+b))
        atTop (𝓝 (Real.exp (-(β*x)*a)-Real.exp (-(β*x)*b))) := by
    intro a b hab
    exact sourceMaximumWindowMean_limit_of_tail_limits μ h hnp hL hm m (fun t => (hLimits t).2) hab.le
  have hAll : ∀ a b : ℝ,a < b →
      Tendsto (fun n : ℕ => sourceCriticalWindowMean n μ Q (Ioo L R) (m n+a) (m n+b))
        atTop (𝓝 (Real.exp (-(β*x)*a)-Real.exp (-(β*x)*b))) := by
    intro a b hab
    exact sourceCriticalWindowMean_limit_of_maximum_limit μ h.overlap_range.1 hnp hL
      (fun n => m n+a) (fun n => m n+b) (hMax a b hab)
  refine ⟨{
    center := m
    dimension_cutoff := n₀
    log_constant := M
    log_constant_pos := hM
    finite_prefix := hprefix
    normalized_tail := hEvent.mono (fun _ hn => hn.1)
    unique_center := hEvent.mono (fun _ hn => hn.2.1)
    logarithmic_correction := hEvent.mono (fun _ hn => hn.2.2.1)
    density_limit := fun t => (hLimits t).1
    tail_limit := fun t => (hLimits t).2
    maximum_window_limit := hMax
    critical_window_limit := hAll
    uniform_window_bound := ?_
    window_mass_finite := ?_
    upper_tail_envelope := hEvent.mono (fun _ hn v hv => (hn.2.2.2 v hv).1)
    lower_density_envelope := hEvent.mono (fun _ hn v hv => (hn.2.2.2 v hv).2)
    lower_density_rate_lt_beta := hcp }⟩
  · intro a b hab
    exact sourceWindowMeans_uniformly_bounded_of_limits _ _ (hMax a b hab) (hAll a b hab)
  · intro n a b
    exact ⟨sourceMaximumWindowMass_finite n μ h.overlap_range.1 (Ioo L R) _ _,
      sourceCriticalWindowMass_finite n μ h.overlap_range.1 (Ioo L R) _ _⟩

end SlowEquilibration.SphericalMarkedWindows

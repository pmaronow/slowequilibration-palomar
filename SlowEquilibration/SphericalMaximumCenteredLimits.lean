-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMaximumFixedEnergyRatio
public import SlowEquilibration.ExpectedTailNormalizedLimits

/-! Genuine density and tail limits at the actual tail-equals-one
centering, derived from the original-field intensity. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity SphericalModel ExpectedTailCentering
open scoped Topology
set_option maxHeartbeats 300000

theorem sourceMaximum_centered_limits_of_centering (μ : FiniteMixture) {β x Q L R δ M : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) (hδ : 0 < δ)
    (hScore : ∀ e∈Icc (markE μ β x Q-δ) (markE μ β x Q+δ),∀ k∈Icc L R,
      (β*x)/2 ≤ sourceEnergySlope μ Q e k ∧ sourceEnergySlope μ Q e k ≤ (β*x+β)/2)
    (hM : 0 ≤ M) (m : ℕ → ℝ)
    (hcenter : ∀ᶠ n : ℕ in atTop,|m n-((n+2 : ℕ)*markE μ β x Q-Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M)
    (hnorm : ∀ᶠ n : ℕ in atTop,sourceMaximumEnergyTail n μ Q (Ioo L R) (m n)=1) :
    ∀ t : ℝ,
      Tendsto (fun n : ℕ => sourceMaximumEnergyDensity n μ Q (Ioo L R) (m n+t))
        atTop (𝓝 ((β*x)*Real.exp (-(β*x)*t))) ∧
      Tendsto (fun n : ℕ => sourceMaximumEnergyTail n μ Q (Ioo L R) (m n+t))
        atTop (𝓝 (Real.exp (-(β*x)*t))) := by
  have hc₀ : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  let D := 1/(2*(β*x))+1
  let σ : ℕ → ℝ := fun n => m n-(n+2 : ℕ)*markE μ β x Q
  have hD : 0 ≤ D := by dsimp [D];positivity
  have hσ : ∀ᶠ n : ℕ in atTop,|σ n| ≤ D*Real.log (n+2 : ℕ) :=
    NatLogWindowScales.normalized_center_log_bounded hc₀ hM m hcenter
  have hcancel : ∀ n : ℕ,(n+2 : ℕ)*markE μ β x Q+σ n=m n := by
    intro n
    dsimp [σ]
    ring
  have hratio : ∀ t : ℝ,Tendsto (fun n : ℕ =>
      sourceMaximumEnergyDensity n μ Q (Ioo L R) (m n+t)/
        sourceMaximumEnergyDensity n μ Q (Ioo L R) (m n)) atTop (𝓝 (Real.exp (-(β*x)*t))) := by
    intro t
    have ht := sourceMaximumEnergyDensity_fixed_ratio μ h hnp hL hm hD σ hσ t
    simpa only [hcancel] using ht
  have hcontinuous : ∀ᶠ n : ℕ in atTop,Continuous (sourceMaximumEnergyDensity n μ Q (Ioo L R)) :=
    (sourceMaximumEnergyDensity_regular μ h hnp hL hm).mono (fun _ hn => hn.1)
  have hpositive : ∀ᶠ n : ℕ in atTop,∀ H : ℝ,0 < sourceMaximumEnergyDensity n μ Q (Ioo L R) H :=
    (sourceMaximumEnergyDensity_regular μ h hnp hL hm).mono (fun _ hn => hn.2.2)
  have henv : ∀ᶠ n : ℕ in atTop,
      (∀ v : ℝ,0 ≤ v → sourceMaximumEnergyDensity n μ Q (Ioo L R) (m n+v)/
        sourceMaximumEnergyDensity n μ Q (Ioo L R) (m n) ≤ Real.exp (-((β*x)/2)*v)) ∧
      (∀ v : ℝ,v ≤ 0 → sourceMaximumEnergyDensity n μ Q (Ioo L R) (m n+v)/
        sourceMaximumEnergyDensity n μ Q (Ioo L R) (m n) ≤ Real.exp (-((β*x+β)/2)*v)) := by
    filter_upwards [hσ,hpositive,NatLogWindowScales.log_window_inside_band_eventually D hδ,
      sourceMaximumEnergyDensity_envelopes μ h hnp hL hm hδ.le hScore]
      with n hσn hpn hband hen
    have habs := abs_le.mp hσn
    have hmb : m n∈Icc ((n+2 : ℕ)*(markE μ β x Q-δ)) ((n+2 : ℕ)*(markE μ β x Q+δ)) := by
      rw [←hcancel n]
      constructor <;> nlinarith [habs.1,habs.2]
    constructor
    · intro v hv
      apply (div_le_iff₀ (hpn _)).mpr
      exact (hen.1 (m n) hmb.1 v hv).trans_eq (mul_comm _ _)
    · intro v hv
      apply (div_le_iff₀ (hpn _)).mpr
      have he := hen.2 (m n) hmb (-v) (neg_nonneg.mpr hv)
      have harg : m n-(-v)=m n+v := by ring
      have hExp : ((β*x+β)/2)*(-v)=-((β*x+β)/2)*v := by ring
      rw [harg,hExp] at he
      exact he.trans_eq (mul_comm _ _)
  have hbase := normalized_density_limit m hc₀ (half_pos hc₀) hcontinuous hpositive hnorm hratio
    (henv.mono (fun _ hn => hn.1))
  intro t
  exact ⟨normalized_centered_density_limit m (hpositive.mono (fun _ hn => hn _)) hbase hratio t,
    normalized_centered_tail_limit m hc₀ (half_pos hc₀) (half_pos (add_pos hc₀ h.beta_pos)).le
      hcontinuous hpositive hbase hratio henv t⟩

/-- Original-field source centering and every fixed physical-energy
intensity/tail limit, with all desired normalization derived internally. -/
theorem sourceMaximum_centering_and_limits (μ : FiniteMixture) {β x Q L R δ : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) (hδ : 0 < δ)
    (hScore : ∀ e∈Icc (markE μ β x Q-δ) (markE μ β x Q+δ),∀ k∈Icc L R,
      (β*x)/2 ≤ sourceEnergySlope μ Q e k ∧ sourceEnergySlope μ Q e k ≤ (β*x+β)/2) :
    ∃ n₀ : ℕ,∃ m : ℕ → ℝ,∃ M : ℝ,0 < M ∧
      (∀ n<n₀,m n=(n+2 : ℕ)*markE μ β x Q) ∧
      ((β*x+β)/2 < β) ∧
      (∀ᶠ n : ℕ in atTop,
        sourceMaximumEnergyTail n μ Q (Ioo L R) (m n)=1 ∧
        (∀ y : ℝ,sourceMaximumEnergyTail n μ Q (Ioo L R) y=1 → y=m n) ∧
        |m n-((n+2 : ℕ)*markE μ β x Q-Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M ∧
        (∀ v : ℝ,0 ≤ v →
          sourceMaximumEnergyTail n μ Q (Ioo L R) (m n+v) ≤ Real.exp (-((β*x)/2)*v) ∧
          sourceMaximumEnergyDensity n μ Q (Ioo L R) (m n-v) ≤
            Real.exp ((β*x+β)/2)*Real.exp (((β*x+β)/2)*v))) ∧
      (∀ t : ℝ,
        Tendsto (fun n : ℕ => sourceMaximumEnergyDensity n μ Q (Ioo L R) (m n+t))
          atTop (𝓝 ((β*x)*Real.exp (-(β*x)*t))) ∧
        Tendsto (fun n : ℕ => sourceMaximumEnergyTail n μ Q (Ioo L R) (m n+t))
          atTop (𝓝 (Real.exp (-(β*x)*t)))) := by
  obtain ⟨n₀,m,M,hM,hprefix,hcp,hEvent⟩ := sourceMaximum_centering_and_envelopes μ h hnp hL hm hδ hScore
  refine ⟨n₀,m,M,hM,hprefix,hcp,hEvent,?_⟩
  exact sourceMaximum_centered_limits_of_centering μ h hnp hL hm hδ hScore hM.le m
    (hEvent.mono (fun _ hn => hn.2.2.1)) (hEvent.mono (fun _ hn => hn.1))

end SlowEquilibration.SphericalMarkedWindows

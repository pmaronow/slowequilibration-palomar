-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMaximumNormalizedEnvelopes

/-! Actual source centering and both normalized energy envelopes, all
constructed from the original field and primitive admissibility. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity SphericalModel
open scoped Topology
set_option maxHeartbeats 300000

theorem sourceMaximum_centering_and_envelopes (μ : FiniteMixture) {β x Q L R δ : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) (hδ : 0 < δ)
    (hScore : ∀ e∈Icc (markE μ β x Q-δ) (markE μ β x Q+δ),∀ k∈Icc L R,
      (β*x)/2 ≤ sourceEnergySlope μ Q e k ∧ sourceEnergySlope μ Q e k ≤ (β*x+β)/2) :
    ∃ n₀ : ℕ,∃ m : ℕ → ℝ,∃ M : ℝ,0 < M ∧
      (∀ n<n₀,m n=(n+2 : ℕ)*markE μ β x Q) ∧
      ((β*x+β)/2 < β) ∧ ∀ᶠ n : ℕ in atTop,
        sourceMaximumEnergyTail n μ Q (Ioo L R) (m n)=1 ∧
        (∀ y : ℝ,sourceMaximumEnergyTail n μ Q (Ioo L R) y=1 → y=m n) ∧
        |m n-((n+2 : ℕ)*markE μ β x Q-Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M ∧
        (∀ v : ℝ,0 ≤ v →
          sourceMaximumEnergyTail n μ Q (Ioo L R) (m n+v) ≤ Real.exp (-((β*x)/2)*v) ∧
          sourceMaximumEnergyDensity n μ Q (Ioo L R) (m n-v) ≤
            Real.exp ((β*x+β)/2)*Real.exp (((β*x+β)/2)*v)) := by
  obtain ⟨n₀,m,M,hM,hprefix,hcenter⟩ := sourceMaximum_centering_sequence μ h hnp hL hm hδ hScore
  have hc₀ : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  have hcp : 0 ≤ (β*x+β)/2 := (half_pos (add_pos hc₀ h.beta_pos)).le
  have hcpLt : (β*x+β)/2 < β := by
    have hx := mul_lt_mul_of_pos_left h.weight_range.2 h.beta_pos
    rw [mul_one] at hx
    linarith
  let D := 1/(2*(β*x))+1
  have hlogTop : Tendsto (fun n : ℕ => Real.log (n+2 : ℕ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  refine ⟨n₀,m,M,hM,hprefix,hcpLt,?_⟩
  filter_upwards [eventually_ge_atTop n₀,hlogTop.eventually (eventually_ge_atTop M),
    NatLogWindowScales.log_window_inside_band_eventually D hδ,
    sourceMaximum_normalized_envelopes μ h hnp hL hm hδ.le hcp hScore]
    with n hn hlogM hband henv
  have hc := hcenter n hn
  have habs := abs_le.mp hc.2.2
  have hlog : 0 ≤ Real.log (n+2 : ℕ) := hM.le.trans hlogM
  have ht : 0 ≤ Real.log (n+2 : ℕ)/(2*(β*x)) := by positivity
  have he : D*Real.log (n+2 : ℕ)=Real.log (n+2 : ℕ)/(2*(β*x))+Real.log (n+2 : ℕ) := by
    dsimp [D]
    ring
  rw [he] at hband
  have hmb : m n∈Icc ((n+2 : ℕ)*(markE μ β x Q-δ))
      ((n+2 : ℕ)*(markE μ β x Q+δ)-1) := by
    constructor <;> nlinarith [habs.1,habs.2]
  exact ⟨hc.1,hc.2.1,hc.2.2,henv (m n) hmb hc.1⟩

end SlowEquilibration.SphericalMarkedWindows

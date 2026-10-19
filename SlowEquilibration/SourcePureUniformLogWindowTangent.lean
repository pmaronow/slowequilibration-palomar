-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureLocalMaxLogWindowTangent

/-! Uniformization of source pure logarithmic-window intensity tangents.
The arbitrary-sequence theorem upgrades to a uniform error throughout each
whole logarithmic window. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Filter Set TwoAtomStationarity SphericalTAPCertificate
open scoped Topology
set_option maxHeartbeats 400000

private theorem uniform_small_of_all_bounded_sequences
    {R : ℕ → ℝ → ℝ} {B : ℕ → ℝ} (hB : ∀ n, 0 ≤ B n)
    (hseq : ∀ σ : ℕ → ℝ, (∀ᶠ n : ℕ in atTop, |σ n| ≤ B n) →
      Tendsto (fun n => R n (σ n)) atTop (𝓝 (0 : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, |t| ≤ B n → |R n t| < ε := by
  classical
  let bad : ℕ → Prop := fun n => ∃ t : ℝ, |t| ≤ B n ∧ ε ≤ |R n t|
  let σ : ℕ → ℝ := fun n => if h : bad n then Classical.choose h else 0
  have hσ (n : ℕ) : |σ n| ≤ B n := by
    dsimp [σ]
    split_ifs with h
    · exact (Classical.choose_spec h).1
    · simpa using hB n
  have hSeq := hseq σ (Filter.Eventually.of_forall hσ)
  have hEvent : ∀ᶠ n : ℕ in atTop, |R n (σ n)| < ε := by
    have hn := hSeq.eventually (Metric.ball_mem_nhds (0 : ℝ) hε)
    filter_upwards [hn] with n hn
    simpa [Metric.mem_ball, Real.dist_eq] using hn
  filter_upwards [hEvent] with n hn t ht
  by_contra hnot
  have hbad : bad n := ⟨t,ht,le_of_not_gt hnot⟩
  have hchosen : ε ≤ |R n (σ n)| := by
    have hh := (Classical.choose_spec hbad).2
    simpa [σ, hbad] using hh
  linarith

/-- For every fixed logarithmic window, the actual pure local-maximum
log-intensity has a uniform o(1) error around the contact tangent. -/
theorem sourcePure_localMaxPhysicalIntensity_uniform_log_window_tangent
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {D : ℝ} (hD : 0 ≤ D) {ε : ℝ} (hε : 0 < ε) :
    let E := markE (FiniteMixture.pure p hp a ha) β x Q
    ∀ᶠ n : ℕ in atTop, ∀ σ : ℝ,
      |σ| ≤ D*Real.log (n+2 : ℕ) →
      |Real.log (pureLocalMaxPhysicalIntensity n p hp a ha Q
          ((n+2 : ℕ)*E+σ)).toReal-
        Real.log (pureLocalMaxPhysicalIntensity n p hp a ha Q
          ((n+2 : ℕ)*E)).toReal+β*x*σ| < ε := by
  let E := markE (FiniteMixture.pure p hp a ha) β x Q
  let B : ℕ → ℝ := fun n => D*Real.log (n+2 : ℕ)
  let R : ℕ → ℝ → ℝ := fun n σ =>
    Real.log (pureLocalMaxPhysicalIntensity n p hp a ha Q
        ((n+2 : ℕ)*E+σ)).toReal-
      Real.log (pureLocalMaxPhysicalIntensity n p hp a ha Q
        ((n+2 : ℕ)*E)).toReal+β*x*σ
  have hB (n : ℕ) : 0 ≤ B n := by
    dsimp [B]
    apply mul_nonneg hD
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n+2 by omega))
  have hSeq (σ : ℕ → ℝ) (hσ : ∀ᶠ n : ℕ in atTop, |σ n| ≤ B n) :
      Tendsto (fun n => R n (σ n)) atTop (𝓝 (0 : ℝ)) := by
    exact sourcePure_localMaxPhysicalIntensity_log_window_tangent p hp a ha h hD σ hσ
  exact uniform_small_of_all_bounded_sequences hB hSeq hε

end SlowEquilibration.SphericalMarkedWindows

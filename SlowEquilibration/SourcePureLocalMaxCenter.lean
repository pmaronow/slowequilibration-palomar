-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureLocalMaxTailLogWindow
public import SlowEquilibration.ExpectedCompactLogarithmicCentering

/-! The exact tail-equals-one centering for the actual mark-truncated pure
negative-Hessian local-maximum intensity. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory TwoAtomStationarity SphericalTAPCertificate
open ExpectedTailCentering
open scoped Topology
set_option maxHeartbeats 500000

theorem sourcePure_truncatedLocalMax_normalized_center
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {l r g Z : ℝ}
    (hm : markE (FiniteMixture.pure p hp a ha) β x Q ∈ Ioo l r)
    (hg : 0 < g)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g ≤ (p : ℝ)*l)
    (hRight : (p : ℝ)*r ≤ Z) :
    let E := markE (FiniteMixture.pure p hp a ha) β x Q
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in atTop, ∃ m : ℝ,
      tail (pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) m=1 ∧
      (∀ y : ℝ, tail (pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) y=1 → y=m) ∧
      |m-((n+2 : ℕ)*E-Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M := by
  let E := markE (FiniteMixture.pure p hp a ha) β x Q
  let f := fun n : ℕ => pureTruncatedLocalMaxDensity n p hp a ha Q
    ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
  let δ := min (E-l) (r-E)
  have hc : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  have hδ : 0 < δ := lt_min (sub_pos.mpr hm.1) (sub_pos.mpr hm.2)
  have hregular : ∀ᶠ n : ℕ in atTop,
      Integrable (f n) ∧ ∀ H : ℝ, 0 ≤ f n H := by
    filter_upwards [pureTruncatedLocalMaxDensity_integrable_eventually
      p hp a ha h (hm.1.trans hm.2) hg hLeft hRight] with n hn
    exact ⟨hn,fun H => pureTruncatedLocalMaxDensity_nonneg n p hp a ha Q _ _ H⟩
  have hpositive : ∀ D : ℝ, 0 ≤ D → ∀ᶠ n : ℕ in atTop,
      ∀ H ∈ Ioo ((n+2 : ℕ)*E-D*Real.log (n+2 : ℕ))
        ((n+2 : ℕ)*E+D*Real.log (n+2 : ℕ)), 0 < f n H := by
    intro D hD
    filter_upwards [pureTruncatedLocalMaxDensity_pos_eventually
      p hp a ha h hg hLeft hRight,
      NatLogWindowScales.log_window_inside_band_eventually D hδ]
      with n hn hBand
    intro H hH
    have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
    have hδL : δ ≤ E-l := min_le_left _ _
    have hδR : δ ≤ r-E := min_le_right _ _
    have hδNL := mul_le_mul_of_nonneg_left hδL hN.le
    have hδNR := mul_le_mul_of_nonneg_left hδR hN.le
    apply hn H
    constructor <;> nlinarith [hH.1,hH.2,hBand,hδNL,hδNR]
  have hbound : ∀ D : ℝ, 0 ≤ D →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ σ : ℝ,
        |σ| ≤ D*Real.log (n+2 : ℕ) →
        c*Real.exp (-(β*x)*σ)/Real.sqrt (n+2 : ℕ) ≤
          tail (f n) ((n+2 : ℕ)*E+σ) ∧
        tail (f n) ((n+2 : ℕ)*E+σ) ≤
          C*Real.exp (-(β*x)*σ)/Real.sqrt (n+2 : ℕ) := by
    intro D hD
    exact sourcePure_truncatedLocalMax_tail_log_window
      p hp a ha h hm hg hLeft hRight hD
  exact compact_logarithmic_normalized_center hc hregular hpositive hbound

end SlowEquilibration.SphericalMarkedWindows

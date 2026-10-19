-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureLocalMaxCenterSequence
public import SlowEquilibration.SourcePureLocalMaxIntensityTransfer
public import SlowEquilibration.NatLogWindowBand

/-! The true pure local-maximum intensity ratio transfers to any physical
center with the source logarithmic correction, including the mark cutoff. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter TwoAtomStationarity SphericalTAPCertificate
open scoped Topology
set_option maxHeartbeats 400000

theorem sourcePure_center_log_shift_bound
    {E c₀ M : ℝ} (hc₀ : 0 < c₀) (hM : 0 < M) (m : ℕ → ℝ)
    (hcenter : ∀ᶠ n : ℕ in atTop,
      |m n-((n+2 : ℕ)*E-Real.log (n+2 : ℕ)/(2*c₀))| ≤ M) :
    let D := 1+1/(2*c₀)
    0 ≤ D ∧ ∀ᶠ n : ℕ in atTop,
      |m n-(n+2 : ℕ)*E| ≤ D*Real.log (n+2 : ℕ) := by
  let D := 1+1/(2*c₀)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hLogTop : Tendsto (fun n : ℕ => Real.log (n+2 : ℕ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  refine ⟨hD,?_⟩
  filter_upwards [hcenter,hLogTop.eventually (eventually_ge_atTop M)]
    with n hn hlog
  have hh := abs_le.mp hn
  apply abs_le.mpr
  have he : D*Real.log (n+2 : ℕ) =
      Real.log (n+2 : ℕ)+Real.log (n+2 : ℕ)/(2*c₀) := by
    dsimp [D]
    ring
  rw [he]
  have hlogDiv : 0 ≤ Real.log (n+2 : ℕ)/(2*c₀) :=
    div_nonneg (le_trans hM.le hlog) (by positivity)
  constructor <;> linarith [hh.1,hh.2,hlog,hlogDiv]

theorem sourcePure_truncatedLocalMax_centered_ratio
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {l r : ℝ} (hm : markE (FiniteMixture.pure p hp a ha) β x Q ∈ Ioo l r)
    (m : ℕ → ℝ) {M : ℝ} (hM : 0 < M)
    (hcenter : ∀ᶠ n : ℕ in atTop,
      |m n-((n+2 : ℕ)*markE (FiniteMixture.pure p hp a ha) β x Q-
        Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M) (t : ℝ) :
    Tendsto (fun n : ℕ =>
      pureTruncatedLocalMaxDensity n p hp a ha Q ((n+2 : ℕ)*l) ((n+2 : ℕ)*r) (m n+t) /
      pureTruncatedLocalMaxDensity n p hp a ha Q ((n+2 : ℕ)*l) ((n+2 : ℕ)*r) (m n))
      atTop (𝓝 (Real.exp (-(β*x)*t))) := by
  let E := markE (FiniteMixture.pure p hp a ha) β x Q
  let δ := min (E-l) (r-E)
  let σ : ℕ → ℝ := fun n => m n-(n+2 : ℕ)*E
  let D := 1+1/(2*(β*x))
  let D' := D+|t|+1
  have hc : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  have hδ : 0 < δ := lt_min (sub_pos.mpr hm.1) (sub_pos.mpr hm.2)
  obtain ⟨hD,hσ⟩ := sourcePure_center_log_shift_bound hc hM m hcenter
  have hD' : 0 ≤ D' := by dsimp [D']; positivity
  have hRatio := sourcePure_localMaxPhysicalIntensity_fixed_shift_ratio
    p hp a ha h hD σ hσ t
  have hLogTop : Tendsto (fun n : ℕ => Real.log (n+2 : ℕ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  have hEq : (fun n : ℕ =>
      (pureLocalMaxPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+σ n+t)).toReal/
      (pureLocalMaxPhysicalIntensity n p hp a ha Q ((n+2 : ℕ)*E+σ n)).toReal)
      =ᶠ[atTop] (fun n : ℕ =>
        pureTruncatedLocalMaxDensity n p hp a ha Q ((n+2 : ℕ)*l) ((n+2 : ℕ)*r) (m n+t) /
        pureTruncatedLocalMaxDensity n p hp a ha Q ((n+2 : ℕ)*l) ((n+2 : ℕ)*r) (m n)) := by
    filter_upwards [hσ,
      NatLogWindowScales.log_window_inside_band_eventually D' hδ,
      hLogTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hn hBand hLog
    have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
    have hσt : |σ n+t| ≤ D'*Real.log (n+2 : ℕ) := by
      calc
        |σ n+t| ≤ |σ n|+|t| := abs_add_le _ _
        _ ≤ D*Real.log (n+2 : ℕ)+|t| := by linarith [hn]
        _ ≤ D'*Real.log (n+2 : ℕ) := by
          dsimp [D']
          nlinarith [abs_nonneg t,hLog]
    have hδL : δ ≤ E-l := min_le_left _ _
    have hδR : δ ≤ r-E := min_le_right _ _
    have hδNL := mul_le_mul_of_nonneg_left hδL hN.le
    have hδNR := mul_le_mul_of_nonneg_left hδR hN.le
    have hDle : D ≤ D' := by dsimp [D']; linarith [abs_nonneg t]
    have hlog0 : 0 ≤ Real.log (n+2 : ℕ) := by linarith [hLog]
    have hDlog := mul_le_mul_of_nonneg_right hDle hlog0
    have hσBase : |σ n| ≤ D'*Real.log (n+2 : ℕ) := hn.trans hDlog
    have hBase : m n ∈ Ioo ((n+2 : ℕ)*l) ((n+2 : ℕ)*r) := by
      have hh := abs_le.mp hσBase
      constructor <;> nlinarith [hBand,hδNL,hδNR,hh.1,hh.2]
    have hShift : m n+t ∈ Ioo ((n+2 : ℕ)*l) ((n+2 : ℕ)*r) := by
      have hh := abs_le.mp hσt
      constructor <;> nlinarith [hBand,hδNL,hδNR,hh.1,hh.2]
    have he : (n+2 : ℕ)*E+σ n=m n := by dsimp [σ]; ring
    rw [he]
    change (pureLocalMaxPhysicalIntensity n p hp a ha Q (m n+t)).toReal /
      (pureLocalMaxPhysicalIntensity n p hp a ha Q (m n)).toReal =
      (Ioo ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)).indicator
        (fun H => (pureLocalMaxPhysicalIntensity n p hp a ha Q H).toReal) (m n+t) /
      (Ioo ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)).indicator
        (fun H => (pureLocalMaxPhysicalIntensity n p hp a ha Q H).toReal) (m n)
    rw [Set.indicator_of_mem hShift,Set.indicator_of_mem hBase]
  exact hRatio.congr' hEq

end SlowEquilibration.SphericalMarkedWindows

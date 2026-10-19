-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMaximumLogWindow
public import SlowEquilibration.SphericalMaximumEnergyEnvelopes
public import SlowEquilibration.ExpectedTailEnvelopes
public import SlowEquilibration.NatLogWindowBand

/-! Actual upper-tail normalization in logarithmic physical-energy
windows, with source admissibility stated as its literal score band. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity SphericalModel
open ExpectedTailCentering
open scoped Topology
set_option maxHeartbeats 300000

theorem sourceMaximumEnergyTail_log_window (μ : FiniteMixture) {β x Q L R δ cMinus cPlus : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R)
    (hδ : 0 < δ) (hcm : 0 < cMinus) (hcp : 0 ≤ cPlus)
    (hScore : ∀ e∈Icc (markE μ β x Q-δ) (markE μ β x Q+δ),∀ k∈Icc L R,
      cMinus ≤ sourceEnergySlope μ Q e k ∧ sourceEnergySlope μ Q e k ≤ cPlus)
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,∀ σ : ℝ,
      |σ| ≤ D*Real.log (n+2 : ℕ) →
      c*Real.exp (-(β*x)*σ)/Real.sqrt (n+2 : ℕ) ≤
        sourceMaximumEnergyTail n μ Q (Ioo L R) ((n+2 : ℕ)*markE μ β x Q+σ) ∧
      sourceMaximumEnergyTail n μ Q (Ioo L R) ((n+2 : ℕ)*markE μ β x Q+σ) ≤
        C*Real.exp (-(β*x)*σ)/Real.sqrt (n+2 : ℕ) := by
  obtain ⟨c,C,hc,hC,hDensity⟩ := sourceMaximumEnergyDensity_log_window μ h hnp hL hm hD
  refine ⟨Real.exp (-cPlus)*c,C/cMinus,mul_pos (Real.exp_pos _) hc,div_pos hC hcm,?_⟩
  filter_upwards [hDensity,sourceMaximumEnergyDensity_regular μ h hnp hL hm,
    sourceMaximumEnergyDensity_envelopes μ h hnp hL hm hδ.le hScore,
    NatLogWindowScales.log_window_inside_band_eventually D hδ] with n hn hregular henv hband
  intro σ hσ
  let H := (n+2 : ℕ)*markE μ β x Q+σ
  have hσabs := abs_le.mp hσ
  have hHlo : (n+2 : ℕ)*(markE μ β x Q-δ) ≤ H := by dsimp [H];nlinarith [hσabs.1]
  have hHband : ∀ v∈Icc (0 : ℝ) 1,H+v∈Icc
      ((n+2 : ℕ)*(markE μ β x Q-δ)) ((n+2 : ℕ)*(markE μ β x Q+δ)) := by
    intro v hv
    dsimp [H]
    constructor <;> nlinarith [hv.1,hv.2,hσabs.1,hσabs.2]
  have htupper := tail_upper_of_density_envelope hregular.2.1 hcm (henv.1 H hHlo)
  have htlower := tail_lower_of_unit_density_envelope hregular.2.1
    (fun y => (hregular.2.2 y).le) hcp (h := H) (by
      intro v hv
      have he := henv.2 (H+v) (hHband v hv) v hv.1
      rw [add_sub_cancel_right] at he
      have hExp : Real.exp (cPlus*v) ≤ Real.exp cPlus := Real.exp_le_exp.mpr (by nlinarith [hv.2])
      have he' := he.trans (mul_le_mul_of_nonneg_left hExp (hregular.2.2 (H+v)).le)
      have hh := mul_le_mul_of_nonneg_right he' (Real.exp_pos (-cPlus)).le
      calc
        Real.exp (-cPlus)*sourceMaximumEnergyDensity n μ Q (Ioo L R) H=
          sourceMaximumEnergyDensity n μ Q (Ioo L R) H*Real.exp (-cPlus) := mul_comm _ _
        _ ≤ sourceMaximumEnergyDensity n μ Q (Ioo L R) (H+v)*Real.exp cPlus*Real.exp (-cPlus) := hh
        _=sourceMaximumEnergyDensity n μ Q (Ioo L R) (H+v) := by
          rw [mul_assoc,←Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one])

  constructor
  · have hh := mul_le_mul_of_nonneg_left (hn σ hσ).1 (Real.exp_pos (-cPlus)).le
    refine le_trans ?_ (hh.trans htlower)
    apply le_of_eq
    ring
  · refine (htupper.trans (div_le_div_of_nonneg_right (hn σ hσ).2 hcm.le)).trans_eq ?_
    ring

end SlowEquilibration.SphericalMarkedWindows

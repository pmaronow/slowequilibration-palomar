-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMaximumCentering

/-! Exact upper and lower energy envelopes at the true normalized
maximum centering. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity SphericalModel ExpectedTailCentering
open scoped Topology
set_option maxHeartbeats 300000

theorem sourceMaximum_normalized_envelopes (μ : FiniteMixture) {β x Q L R δ cMinus cPlus : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R)
    (hδ : 0 ≤ δ) (hcp : 0 ≤ cPlus)
    (hScore : ∀ e∈Icc (markE μ β x Q-δ) (markE μ β x Q+δ),∀ k∈Icc L R,
      cMinus ≤ sourceEnergySlope μ Q e k ∧ sourceEnergySlope μ Q e k ≤ cPlus) :
    ∀ᶠ n : ℕ in atTop,∀ m∈Icc ((n+2 : ℕ)*(markE μ β x Q-δ))
        ((n+2 : ℕ)*(markE μ β x Q+δ)-1),
      sourceMaximumEnergyTail n μ Q (Ioo L R) m=1 → ∀ v : ℝ,0 ≤ v →
      sourceMaximumEnergyTail n μ Q (Ioo L R) (m+v) ≤ Real.exp (-cMinus*v) ∧
      sourceMaximumEnergyDensity n μ Q (Ioo L R) (m-v) ≤ Real.exp cPlus*Real.exp (cPlus*v) := by
  filter_upwards [sourceMaximumEnergyDensity_regular μ h hnp hL hm,
    sourceMaximumEnergyDensity_envelopes μ h hnp hL hm hδ hScore] with n hreg henv
  intro m hm hnorm
  have hunit : Real.exp (-cPlus)*sourceMaximumEnergyDensity n μ Q (Ioo L R) m ≤
      sourceMaximumEnergyTail n μ Q (Ioo L R) m :=
    tail_lower_of_unit_density_envelope hreg.2.1 (fun H => (hreg.2.2 H).le) hcp (by
      intro w hw
      have hband : m+w∈Icc ((n+2 : ℕ)*(markE μ β x Q-δ))
          ((n+2 : ℕ)*(markE μ β x Q+δ)) := by
        constructor <;> linarith [hm.1,hm.2,hw.1,hw.2]
      have he := henv.2 (m+w) hband w hw.1
      rw [add_sub_cancel_right] at he
      have he' : sourceMaximumEnergyDensity n μ Q (Ioo L R) m ≤
          sourceMaximumEnergyDensity n μ Q (Ioo L R) (m+w)*Real.exp cPlus :=
        he.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [hw.2]))
          (hreg.2.2 (m+w)).le)
      have hh := mul_le_mul_of_nonneg_right he' (Real.exp_pos (-cPlus)).le
      calc
        _=sourceMaximumEnergyDensity n μ Q (Ioo L R) m*Real.exp (-cPlus) := mul_comm _ _
        _ ≤ sourceMaximumEnergyDensity n μ Q (Ioo L R) (m+w)*Real.exp cPlus*Real.exp (-cPlus) := hh
        _=sourceMaximumEnergyDensity n μ Q (Ioo L R) (m+w) := by
          rw [mul_assoc,←Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one])
  have hDensity : sourceMaximumEnergyDensity n μ Q (Ioo L R) m ≤ Real.exp cPlus := by
    rw [hnorm] at hunit
    have hh := mul_le_mul_of_nonneg_left hunit (Real.exp_pos cPlus).le
    simpa only [←mul_assoc,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul,mul_one] using hh
  intro v hv
  constructor
  · have he := tail_decay_of_density_envelope hreg.2.1 hv (h := m) (c := cMinus)
      (by intro H hH;exact henv.1 H (hm.1.trans hH) v hv)
    change sourceMaximumEnergyTail n μ Q (Ioo L R) (m+v) ≤
      sourceMaximumEnergyTail n μ Q (Ioo L R) m*Real.exp (-cMinus*v) at he
    rw [hnorm,one_mul] at he
    exact he
  · exact (henv.2 m ⟨hm.1,by linarith [hm.2]⟩ v hv).trans
      (mul_le_mul_of_nonneg_right hDensity (Real.exp_pos _).le)

end SlowEquilibration.SphericalMarkedWindows

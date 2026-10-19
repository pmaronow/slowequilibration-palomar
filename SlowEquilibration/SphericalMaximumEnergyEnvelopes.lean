-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMaximumEnergyRegularity

/-! Source score-band admissibility gives actual energy density
envelopes, directly from the exact physical Gaussian score law. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity SphericalModel
open scoped Topology
set_option maxHeartbeats 300000

theorem physicalMaximumDensity_energy_tilt (n : ℕ) (μ : FiniteMixture) (Q H k t : ℝ) :
    (mixedLocalMaxPhysicalIntensity n μ Q (H+t) k).toReal=
      (mixedLocalMaxPhysicalIntensity n μ Q H k).toReal*
        Real.exp (-sourceEnergySlope μ Q (H/(n+2 : ℕ)) k*t-
          sourceEnergyCurvature μ Q*t^2/(2*(n+2 : ℕ))) := by
  have ht := mixedMaximumEnergyRadialIntensity_energy_tilt n μ Q H k t
  rw [mixedMaximumEnergyRadialIntensity_eq_physical,
    mixedMaximumEnergyRadialIntensity_eq_physical] at ht
  have he := congrArg ENNReal.toReal ht
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_pos _).le] at he
  exact he

theorem sourceMaximumEnergyDensity_envelopes (μ : FiniteMixture) {β x Q L R δ cMinus cPlus : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) (hδ : 0 ≤ δ)
    (hScore : ∀ e∈Icc (markE μ β x Q-δ) (markE μ β x Q+δ),∀ k∈Icc L R,
      cMinus ≤ sourceEnergySlope μ Q e k ∧ sourceEnergySlope μ Q e k ≤ cPlus) :
    ∀ᶠ n : ℕ in atTop,
      (∀ H : ℝ,(n+2 : ℕ)*(markE μ β x Q-δ) ≤ H → ∀ v : ℝ,0 ≤ v →
        sourceMaximumEnergyDensity n μ Q (Ioo L R) (H+v) ≤
          sourceMaximumEnergyDensity n μ Q (Ioo L R) H*Real.exp (-cMinus*v)) ∧
      (∀ H∈Icc ((n+2 : ℕ)*(markE μ β x Q-δ)) ((n+2 : ℕ)*(markE μ β x Q+δ)),
        ∀ v : ℝ,0 ≤ v →
        sourceMaximumEnergyDensity n μ Q (Ioo L R) (H-v) ≤
          sourceMaximumEnergyDensity n μ Q (Ioo L R) H*Real.exp (cPlus*v)) := by
  have hA := sourceEnergyCurvature_pos μ h.overlap_range.1 hnp
  filter_upwards [sourceMaximumRadialDensity_integrable μ h hnp hL hm] with n hn
  have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
  constructor
  · intro H hH v hv
    unfold sourceMaximumEnergyDensity
    have hi := (hn H).mul_const (Real.exp (-cMinus*v))
    have hh := integral_mono_ae (hn (H+v)) hi (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with k hk
      rw [physicalMaximumDensity_energy_tilt]
      have hs := (hScore (markE μ β x Q-δ) ⟨le_rfl,by linarith⟩ k ⟨hk.1.le,hk.2.le⟩).1
      have he : sourceEnergySlope μ Q (H/(n+2 : ℕ)) k=
          sourceEnergySlope μ Q (markE μ β x Q-δ) k+
            sourceEnergyCurvature μ Q*(H/(n+2 : ℕ)-(markE μ β x Q-δ)) := by
        unfold sourceEnergySlope
        ring
      have hnorm : markE μ β x Q-δ ≤ H/(n+2 : ℕ) := (le_div_iff₀ hN).mpr (by nlinarith)
      have hlo : cMinus ≤ sourceEnergySlope μ Q (H/(n+2 : ℕ)) k := by
        rw [he]
        exact hs.trans (le_add_of_nonneg_right (mul_nonneg hA.le (sub_nonneg.mpr hnorm)))
      have hq : 0 ≤ sourceEnergyCurvature μ Q*v^2/(2*(n+2 : ℕ)) := by positivity
      have hpow : -sourceEnergySlope μ Q (H/(n+2 : ℕ)) k*v-
          sourceEnergyCurvature μ Q*v^2/(2*(n+2 : ℕ)) ≤ -cMinus*v := by nlinarith
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hpow) ENNReal.toReal_nonneg)
    exact hh.trans_eq (integral_mul_const _ _)
  · intro H hH v hv
    unfold sourceMaximumEnergyDensity
    have hi := (hn H).mul_const (Real.exp (cPlus*v))
    have hh := integral_mono_ae (hn (H-v)) hi (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with k hk
      have hnorm : H/(n+2 : ℕ)∈Icc (markE μ β x Q-δ) (markE μ β x Q+δ) := by
        constructor
        · exact (le_div_iff₀ hN).mpr (by nlinarith [hH.1])
        · exact (div_le_iff₀ hN).mpr (by nlinarith [hH.2])
      have hs := (hScore (H/(n+2 : ℕ)) hnorm k ⟨hk.1.le,hk.2.le⟩).2
      have ht := physicalMaximumDensity_energy_tilt n μ Q H k (-v)
      rw [←sub_eq_add_neg] at ht
      rw [ht]
      have hq : 0 ≤ sourceEnergyCurvature μ Q*(-v)^2/(2*(n+2 : ℕ)) := by positivity
      have hpow : -sourceEnergySlope μ Q (H/(n+2 : ℕ)) k*(-v)-
          sourceEnergyCurvature μ Q*(-v)^2/(2*(n+2 : ℕ)) ≤ cPlus*v := by nlinarith
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hpow) ENNReal.toReal_nonneg)
    exact hh.trans_eq (integral_mul_const _ _)

end SlowEquilibration.SphericalMarkedWindows

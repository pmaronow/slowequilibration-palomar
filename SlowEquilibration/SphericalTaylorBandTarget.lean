-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTaylorNestedLatitude
public import SlowEquilibration.SphericalAuxiliaryBottomMaximum
public import SlowEquilibration.SphericalPlantedProfile

@[expose] public section

/-! Actual finite-mixture scalar constants for the planted thermal band.
An outward latitude makes the bottom strictly strong while preserving the
source core overlap and pressure to any fixed positive tolerance. -/

namespace SlowEquilibration.SphericalTaylorRemainder
noncomputable section
open Set Metric
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalLatitudeChartKacRice
open SlowEquilibration.SphericalGaussianJet
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def auxiliaryBandTrial (μ : FiniteMixture) (β Q q : ℝ) : ℝ :=
  β*Real.sqrt (latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) Q) q)+
    (β^2*(μ.xi 1-μ.xi Q)-Q)/2+β^2*μ.xi (bandOuterLatitude Q q)+Real.log (1-Q)/2

theorem auxiliaryBandTrial_continuous (μ : FiniteMixture) (β Q : ℝ) :
    Continuous (auxiliaryBandTrial μ β Q) := by
  unfold auxiliaryBandTrial latitudeDerivativeVariance bandOuterLatitude FiniteMixture.xi
  fun_prop

theorem qStar_auxiliaryBandTrial_eq (μ : FiniteMixture) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi<β) :
    let Q := Thresholds.qStar μ.xi β
    auxiliaryBandTrial μ β Q (Real.sqrt Q)=plantedProfileTrial μ β Q := by
  dsimp only
  let Q := Thresholds.qStar μ.xi β
  have hQ : Q∈Ioo (0 : ℝ) 1 := (μ.qStar_solves_plateau hβ).1
  have hp : β^2*μ.xi1 Q=Q/(1-Q) := by
    have hh := (μ.qStar_solves_plateau hβ).2
    change β^2*deriv μ.xi Q=Q/(1-Q) at hh
    rw [(μ.hasDerivAt_xi Q).deriv] at hh
    exact hh
  have henergy := auxiliary_bottom_energy μ hQ (μ.dynamicalThreshold_pos.trans hβ) hp
  have ho : bandOuterLatitude Q (Real.sqrt Q)=Q := by
    rw [bandOuterLatitude,← pow_two,Real.sq_sqrt hQ.1.le]
  change auxiliaryBandTrial μ β Q (Real.sqrt Q)=plantedProfileTrial μ β Q
  rw [auxiliaryBandTrial,henergy,ho,plantedProfileTrial]
  ring

/-- A strict exterior-Hessian latitude exists arbitrarily near the source
qStar bottom, including the marginal a=b case. Its exact physical energy,
planted shift and entropy approximate the literal source trial Ψ(qStar). -/
theorem exists_strong_qStar_band_trial (μ : FiniteMixture) {β δ ε : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi<β) (hδ : 0<δ) (hε : 0<ε) :
    let Q := Thresholds.qStar μ.xi β
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∃ q∈Ioo (Real.sqrt Q) 1,
      latitudeCurvatureVariance c q<latitudeDerivativeVariance c q ∧
      |bandOuterLatitude Q q-Q|<δ ∧
      plantedProfileTrial μ β Q-ε<auxiliaryBandTrial μ β Q q := by
  dsimp only
  let Q := Thresholds.qStar μ.xi β
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hQ : Q∈Ioo (0 : ℝ) 1 := (μ.qStar_solves_plateau hβ).1
  have hs0 : 0<Real.sqrt Q := Real.sqrt_pos.mpr hQ.1
  have hs1 : Real.sqrt Q<1 := by
    have hh := Real.sq_sqrt hQ.1.le
    nlinarith [hQ.2]
  have houter : Continuous (bandOuterLatitude Q) := by unfold bandOuterLatitude; fun_prop
  obtain ⟨d₁,hd₁,houterclose⟩ := Metric.continuousAt_iff.mp
    (houter.continuousAt (x := Real.sqrt Q)) δ hδ
  obtain ⟨d₂,hd₂,htrialclose⟩ := Metric.continuousAt_iff.mp
    ((auxiliaryBandTrial_continuous μ β Q).continuousAt (x := Real.sqrt Q)) ε hε
  let d := min (d₁/2) (min (d₂/2) ((1-Real.sqrt Q)/2))
  have hd : 0<d := lt_min (by positivity) (lt_min (by positivity) (by linarith))
  have hd₁' : d<d₁ := (min_le_left _ _).trans_lt (by linarith)
  have hd₂' : d<d₂ := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hdend : d<1-Real.sqrt Q := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith)
  let q := Real.sqrt Q+d
  have hqlo : Real.sqrt Q<q := by dsimp only [q]; linarith
  have hqhi : q<1 := by dsimp only [q]; linarith
  have hdist : dist q (Real.sqrt Q)=d := by
    rw [Real.dist_eq,show q-Real.sqrt Q=d by dsimp only [q]; ring,abs_of_pos hd]
  have hweak := auxiliary_bottom_weakStrongField μ hQ (μ.elasticity_qStar_le hβ)
  refine ⟨q,⟨hqlo,hqhi⟩,center_latitude_strong_of_gt μ hQ.1 hs0.le hqlo hqhi hweak,?_,?_⟩
  · have hh := houterclose (hdist.trans_lt hd₁')
    have ho : bandOuterLatitude Q (Real.sqrt Q)=Q := by
      rw [bandOuterLatitude,← pow_two,Real.sq_sqrt hQ.1.le]
    rw [Real.dist_eq,ho] at hh
    exact hh
  · have hh := htrialclose (hdist.trans_lt hd₂')
    rw [Real.dist_eq,qStar_auxiliaryBandTrial_eq μ hβ] at hh
    have hlt := (abs_lt.mp hh).1
    change plantedProfileTrial μ β Q-ε<auxiliaryBandTrial μ β Q q
    linarith

end
end SlowEquilibration.SphericalTaylorRemainder

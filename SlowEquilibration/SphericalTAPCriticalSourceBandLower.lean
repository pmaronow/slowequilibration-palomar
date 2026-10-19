-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalSourceGeometry
public import SlowEquilibration.SphericalTAPCriticalEnergyPalmIntensity

@[expose] public section

/-! The source Proposition 12.20 lower tail with a common band and energy
window selected from the actual one-step certificate. The Palm energy law is
the normalized original all-critical Kac--Rice intensity. -/

namespace SlowEquilibration.SphericalTAPCriticalSourceBandLower
noncomputable section
open MeasureTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows
open SphericalTAPCertificate SphericalTAPCriticalSourceGeometry
open SphericalTAPCriticalBandSectionBridge
open SphericalTAPCriticalFixedBandPalmLower
open SphericalTAPCriticalEnergyPalmAverage
open SphericalTAPCriticalEnergyPalmIntensity
open ConditionedDeterminantMoments PairConditionalDeterminantMoments
open scoped Topology
set_option autoImplicit false

/-- A mixed certificate selects an actual interval above the GOE edge and
one positive band/energy neighborhood. Every smaller fixed band enjoys the
source energy-Palm lower-tail estimate with the physical radial intensity. -/
theorem mixed_sourceEnergyPalm_common_band_and_energy_window
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    let E0 := TwoAtomStationarity.markE μ β x Q
    let K0 := TwoAtomStationarity.markK μ β Q
    ∃ L R ε0 b0 : ℝ,
      0 < ε0 ∧ 0 < b0 ∧ b0 < Real.sqrt Q ∧
      2*Real.sqrt (Q^2*μ.xi2 Q) < L ∧ L < K0 ∧ K0 < R ∧
      (∀ d : ℕ, ∀ a : ℝ,
        sourcePhysicalAllCriticalRadialLaw d μ Q (((d+2:ℕ):ℝ)*a) L R =
          sourceAllCriticalRadialLaw d μ Q a L R) ∧
      ∀ b : ℝ, 0 < b → b ≤ b0 →
        ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ᶠ d : ℕ in atTop,
          ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)),
          ∀ a : ℝ, |a-E0| ≤ ε0 →
          ∀ mN : ℝ,
          let scale := sourceCriticalBandScale (d+1) μ h.overlap_range β mN *
            Real.exp (β*(((d+2:ℕ):ℝ)*a-mN))
          mixedEnergyPalmEventProbability d μ Q u hu a L R
            {J | partitionOn β (field (mixtureCoefficients μ) J)
              (overlapRegion u (Icc (Real.sqrt Q-b) (Real.sqrt Q+b))) <
                δ*scale} ≤ ε := by
  dsimp only
  obtain ⟨M,r,L,R,ε0,b0,hM,hr0,hr1,hε0,hb0,hb0Q,hEdge,
    hLK,hKR,hU,hE,hband⟩ := mixed_fixedBand_source_geometry μ h
  refine ⟨L,R,ε0,b0,hε0,hb0,hb0Q,hEdge,hLK,hKR,?_,?_⟩
  · intro d a
    exact sourcePhysicalAllCriticalRadialLaw_eq_sourceAllCriticalRadialLaw
      d μ h.overlap_range.1 hnp a L R
  · intro b hb hbb ε hε
    exact mixed_sourceEnergyPalm_fixed_band_lower_tight μ h hnp
      hM hr0 hr1 hb (hband b hb hbb) hEdge (hLK.trans hKR) hU hE ε hε

/-- The proper-pure value posterior has a common positive energy window and
band width for the literal source determinant-weighted lower-tail event. -/
theorem pure_sourceEnergyPalm_common_band_and_energy_window
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let E0 := TwoAtomStationarity.markE μ β x Q
    ∃ ε0 b0 : ℝ,
      0 < ε0 ∧ 0 < b0 ∧ b0 < Real.sqrt Q ∧
      ∀ b : ℝ, 0 < b → b ≤ b0 →
        ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ᶠ d : ℕ in atTop,
          ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)),
          ∀ a : ℝ, |a-E0| ≤ ε0 →
          ∀ mN : ℝ,
          let ν := pureLaw p hp alpha halpha Q u hu a
          let D := intrinsicDet μ Q u
          let scale := sourceCriticalBandScale (d+1) μ h.overlap_range β mN *
            Real.exp (β*(((d+2:ℕ):ℝ)*a-mN))
          (∫ J in {J | partitionOn β (field (mixtureCoefficients μ) J)
            (overlapRegion u (Icc (Real.sqrt Q-b) (Real.sqrt Q+b))) <
              δ*scale}, D J ∂ν) /
            (∫ J, D J ∂ν) ≤ ε := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let E0 := TwoAtomStationarity.markE μ β x Q
  obtain ⟨M,r,L,R,εG,b0,hM,hr0,hr1,hεG,hb0,hb0Q,hEdge,
    hLK,hKR,hU,hE,hband⟩ := mixed_fixedBand_source_geometry μ h
  obtain ⟨εP,g,Z,hεP,hg,hShift⟩ :=
    pure_fixedBand_radial_window p hp alpha halpha h
  let ε0 := min εG εP
  have hε0 : 0 < ε0 := lt_min hεG hεP
  have hεG' : ε0 ≤ εG := min_le_left _ _
  have hεP' : ε0 ≤ εP := min_le_right _ _
  refine ⟨ε0,b0,hε0,hb0,hb0Q,?_⟩
  intro b hb hbb ε hε
  exact pure_sourceEnergyPalm_fixed_band_lower_tight p hp alpha halpha
    h hM hr0 hr1 hg hb (hband b hb hbb)
    (by linarith [hE])
    (fun a ha => (hShift a (ha.trans hεP')).1)
    (fun a ha => (hShift a (ha.trans hεP')).2) ε hε

end
end SlowEquilibration.SphericalTAPCriticalSourceBandLower

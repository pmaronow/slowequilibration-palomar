-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalEnergyPalmAverage
public import SlowEquilibration.NatLogWindowScales

@[expose] public section

/-! Source Proposition 12.20 for a fixed physical latitude band. The
microscopic interval needed by the symmetric latitude argument is eventually
contained in every fixed band of positive width. -/

namespace SlowEquilibration.SphericalTAPCriticalFixedBandPalmLower
noncomputable section
open MeasureTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows
open PairConditionalDeterminantMoments ConditionedDeterminantMoments
open SphericalTAPCriticalBand SphericalTAPCriticalBandSectionBridge
open SphericalTAPCriticalPalmBandLower
open SphericalTAPCriticalPurePalmBandLower
open SphericalTAPCriticalEnergyPalmAverage
open SphericalTAPCertificate
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- For fixed positive width, the central latitude interval of radius
`N⁻¹ᐟ²` is contained in the manuscript band at all large dimensions. -/
theorem microscopic_interval_eventually_in_fixed_band
    (Q : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ d : ℕ in atTop,
      Icc
        (Real.sqrt Q-1/Real.sqrt (((d+2:ℕ):ℝ)))
        (Real.sqrt Q+1/Real.sqrt (((d+2:ℕ):ℝ))) ⊆
      Icc (Real.sqrt Q-b) (Real.sqrt Q+b) := by
  have hwidth :=
    SlowEquilibration.NatLogWindowScales.inverse_sqrt_dimension_tendsto_zero.eventually
      (gt_mem_nhds hb)
  filter_upwards [hwidth] with d hd
  intro a ha
  constructor <;> linarith [ha.1, ha.2]

/-- The mixed-model clause of printed Proposition 12.20 at a fixed band
width, uniformly for energies in a fixed interval. The Palm law is the
all-critical radial average, with actual original-field band partition and
the exact source `D_N` normalization. -/
theorem mixed_sourceEnergyPalm_fixed_band_lower_tight
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree)
    {M r L R E0 ε0 b : ℝ} (hM : 0 ≤ M)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hb : 0 < b)
    (hI : Icc (Real.sqrt Q-b) (Real.sqrt Q+b) ⊆ Icc (-r) r)
    (hEdge : 2*Real.sqrt (Q^2*μ.xi2 Q) < L)
    (hLR : L < R)
    (hU : Icc L R ⊆ Icc (-M) M)
    (hE : |E0|+ε0 ≤ M) :
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
  have h0 :=
    mixed_sourceEnergyPalm_band_lower_tight μ h hnp hM hr0 hr1
      hEdge hLR hU _ measurableSet_Icc hI
  intro ε hε
  obtain ⟨δ,hδ,hTail⟩ := h0 ε hε
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hTail,microscopic_interval_eventually_in_fixed_band Q hb]
    with d hd hBand
  intro u hu a ha mN
  have haM : |a| ≤ M := by
    have := abs_add_le (a-E0) E0
    have heq : (a-E0)+E0=a := by ring
    rw [heq] at this
    linarith
  exact hd u hu a haM hBand mN

/-- The proper-pure clause of printed Proposition 12.20 at a fixed band.
Its radial mark is the deterministic Euler value `p e`, so no radial
disintegration is required. -/
theorem pure_sourceEnergyPalm_fixed_band_lower_tight
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q)
    {M r g Z E0 ε0 b : ℝ} (hM : 0 ≤ M)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hg : 0 < g)
    (hb : 0 < b)
    (hI : Icc (Real.sqrt Q-b) (Real.sqrt Q+b) ⊆ Icc (-r) r)
    (hE : |E0|+ε0 ≤ M)
    (hShiftLo : ∀ a, |a-E0| ≤ ε0 →
      2*Real.sqrt (Q^2*(FiniteMixture.pure p hp alpha halpha).xi2 Q)+g ≤
        (p:ℝ)*a)
    (hShiftHi : ∀ a, |a-E0| ≤ ε0 → (p:ℝ)*a ≤ Z) :
    let μ := FiniteMixture.pure p hp alpha halpha
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
  have h0 := pure_sourcePalm_band_lower_tight p hp alpha halpha
    h (Z := Z) hM hr0 hr1 hg _ measurableSet_Icc hI
  dsimp only at h0
  intro ε hε
  obtain ⟨δ,hδ,hTail⟩ := h0 ε hε
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hTail,microscopic_interval_eventually_in_fixed_band Q hb]
    with d hd hBand
  intro u hu a ha mN
  have haM : |a| ≤ M := by
    have := abs_add_le (a-E0) E0
    have heq : (a-E0)+E0=a := by ring
    rw [heq] at this
    linarith
  exact hd u hu a haM (hShiftLo a ha) (hShiftHi a ha) hBand mN

end
end SlowEquilibration.SphericalTAPCriticalFixedBandPalmLower

-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalWeightedTrialProfile
public import SlowEquilibration.SphericalPlateauAmplitudeScalars
public import SlowEquilibration.CompactAmplitudeEnvelope

@[expose] public section

/-! # Actual compact amplitude trial envelope and exact contact derivative -/
namespace SlowEquilibration.SphericalModel
noncomputable section
open Set Filter
open SphericalBarycenter SphericalPlateauAmplitudeScalars
open scoped Topology
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev WeightedTrialLatitude (ρ : ℝ) := Icc (-ρ) ρ

lemma weightedTrialLatitude_abs_le {ρ : ℝ} (r : WeightedTrialLatitude ρ) : |(r:ℝ)|≤ρ :=
  abs_le.mpr r.property

/-- The exact signed weighted trial is continuous on every compact
latitude interval strictly inside the physical poles. -/
theorem weightedAmplitudeTrialProfile_compact_continuous (μ : FiniteMixture)
    (β δ q₁ q₂ : ℝ) {ρ : ℝ} (hρ : ρ<1) :
    Continuous (fun r : WeightedTrialLatitude ρ => weightedAmplitudeTrialProfile μ β δ q₁ q₂ r) := by
  have hx : Continuous μ.xi := continuous_iff_continuousAt.mpr fun t => (μ.hasDerivAt_xi t).continuousAt
  have habs : Continuous (fun r : WeightedTrialLatitude ρ => |(r:ℝ)|) := continuous_subtype_val.abs
  have hlog : Continuous (fun r : WeightedTrialLatitude ρ => Real.log (1-|(r:ℝ)|)) :=
    (continuous_const.sub habs).log fun r => (by
      change 1-|(r:ℝ)|≠0
      have hh := weightedTrialLatitude_abs_le r
      linarith)
  have hp : Continuous (sourceProfile (plantedCoreCost μ β) δ q₁ q₂) :=
    (sourceProfile_contDiff _ _ _ _).continuous
  unfold weightedAmplitudeTrialProfile plantedProfileTrial
  fun_prop

/-- The source finite amplitude correction is an actual continuous scalar
on the same physical compact latitude carrier. -/
def weightedAmplitudeShift (μ : FiniteMixture) (β : ℝ) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (r : ℝ) : ℝ :=
  trialShiftCoefficient β (mixtureCoefficients μ p₀) p₀.val.val (k.val+1) r

lemma weightedAmplitudeShift_continuous (μ : FiniteMixture) (β : ℝ)
    (p₀ : Degree μ.maxDegree) (k : Fin 2) : Continuous (weightedAmplitudeShift μ β p₀ k) :=
  trialShiftCoefficient_continuous _ _ _ _

/-- The literal attained compact trial maximum, including τ(2+τ) from
the true Gaussian amplitude square. -/
def weightedAmplitudeTrialEnvelope (μ : FiniteMixture) (β δ q₁ q₂ : ℝ)
    (p₀ : Degree μ.maxDegree) (k : Fin 2) (ρ : ℝ) (hρ0 : 0≤ρ) (hρ : ρ<1) (τ : ℝ) : ℝ := by
  letI : Nonempty (WeightedTrialLatitude ρ) := ⟨⟨0,by constructor <;> linarith⟩⟩
  exact CompactAmplitudeEnvelope.envelope
    (fun r : WeightedTrialLatitude ρ => weightedAmplitudeTrialProfile μ β δ q₁ q₂ r)
    (fun r : WeightedTrialLatitude ρ => weightedAmplitudeShift μ β p₀ k r)
    (weightedAmplitudeTrialProfile_compact_continuous μ β δ q₁ q₂ hρ)
    ((weightedAmplitudeShift_continuous μ β p₀ k).comp continuous_subtype_val) τ

/-- The actual amplitude trial envelope has exactly the source contact
value and derivative, with uniqueness and no nondegeneracy derived internally. -/
theorem weightedAmplitudeTrialEnvelope_contact_derivative (μ : FiniteMixture)
    {β δ q₁ q₂ : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hβs : β<Thresholds.staticThreshold μ.xi) (hc : IsAdmissibleCollar μ β q₁ q₂)
    (hδ : 0≤δ) (p₀ : Degree μ.maxDegree) (k : Fin 2) {ρ : ℝ}
    (hqρ : Thresholds.qStar μ.xi β≤ρ) (hρ : ρ<1) :
    weightedAmplitudeTrialEnvelope μ β δ q₁ q₂ p₀ k ρ
      ((μ.qStar_solves_plateau hβ).1.1.le.trans hqρ) hρ 0=
      β^2*μ.xi 1/2-plantedCoreCost μ β ∧
    HasDerivAt (weightedAmplitudeTrialEnvelope μ β δ q₁ q₂ p₀ k ρ
      ((μ.qStar_solves_plateau hβ).1.1.le.trans hqρ) hρ)
      (β^2*amplitudeSq (mixtureCoefficients μ p₀) p₀.val.val (k.val+1) (Thresholds.qStar μ.xi β)*
        (1-(Thresholds.qStar μ.xi β/(1+Thresholds.qStar μ.xi β))^(k.val+1))) 0 := by
  have hq := (μ.qStar_solves_plateau hβ).1
  have hρ0 : 0≤ρ := hq.1.le.trans hqρ
  let : Nonempty (WeightedTrialLatitude ρ) := ⟨⟨0,by constructor <;> linarith⟩⟩
  let φ := fun r : WeightedTrialLatitude ρ => weightedAmplitudeTrialProfile μ β δ q₁ q₂ r
  let c := fun r : WeightedTrialLatitude ρ => weightedAmplitudeShift μ β p₀ k r
  let r₀ : WeightedTrialLatitude ρ := ⟨Thresholds.qStar μ.xi β,⟨by have hqp := hq.1; linarith,hqρ⟩⟩
  have hφ : Continuous φ := weightedAmplitudeTrialProfile_compact_continuous μ β δ q₁ q₂ hρ
  have hC : Continuous c := (weightedAmplitudeShift_continuous μ β p₀ k).comp continuous_subtype_val
  have hr01 (r : WeightedTrialLatitude ρ) : (r:ℝ)∈Ioo (-1:ℝ) 1 := by
    have hh := weightedTrialLatitude_abs_le r
    exact abs_lt.mp (hh.trans_lt hρ)
  have hmaximum : ∀ r, φ r≤φ r₀ := by
    intro r
    change weightedAmplitudeTrialProfile μ β δ q₁ q₂ r≤weightedAmplitudeTrialProfile μ β δ q₁ q₂ (Thresholds.qStar μ.xi β)
    rw [weightedAmplitudeTrialProfile_qStar μ hβ hc]
    exact weightedAmplitudeTrialProfile_le_contact μ hβ hβs hc hδ (hr01 r)
  have hunique : ∀ r, φ r₀≤φ r → r=r₀ := by
    intro r hh
    apply Subtype.ext
    apply weightedAmplitudeTrialProfile_unique_maximum μ hβ hβs hc hδ (hr01 r)
    change weightedAmplitudeTrialProfile μ β δ q₁ q₂ (Thresholds.qStar μ.xi β)≤_ at hh
    rwa [weightedAmplitudeTrialProfile_qStar μ hβ hc] at hh
  constructor
  · have hh := CompactAmplitudeEnvelope.envelope_zero φ c hφ hC r₀ hmaximum
    change weightedAmplitudeTrialEnvelope μ β δ q₁ q₂ p₀ k ρ hρ0 hρ 0=_
    change CompactAmplitudeEnvelope.envelope φ c hφ hC 0=_
    rw [hh]
    exact weightedAmplitudeTrialProfile_qStar μ hβ hc δ
  · have hh := CompactAmplitudeEnvelope.envelope_hasDerivAt φ c hφ hC r₀ hmaximum hunique
    convert hh using 1
    · rfl
    · exact (twice_trialShiftCoefficient_of_nonneg β (mixtureCoefficients μ p₀)
      p₀.val.val (k.val+1) hq.1.le).symm

end
end SlowEquilibration.SphericalModel

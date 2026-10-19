-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalWeightedTrialEnvelope
public import SlowEquilibration.SphericalPlateauAmplitudeDiracShift

@[expose] public section

/-! # Exact signed bank trial behind the source weighted envelope

The actual auxiliary bank Dirac trial, planted drift, latitude entropy,
and source penalty sum to the weighted envelope integrand. Both signs of
the reference overlap are retained.
-/
namespace SlowEquilibration.SphericalModel
noncomputable section
open Set
open SphericalBarycenter SphericalPlateauAmplitudeModel
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem weightedAmplitudeBankTrial_one (μ : FiniteMixture) (β δ q₁ q₂ : ℝ)
    (p₀ : Degree μ.maxDegree) {r : ℝ} (hr : |r|<1) :
    β^2*μ.xi r+amplitudeDiracTrial μ β p₀ (fun _ => 1) r+
        Real.log (1-r^2)/2-2*sourceProfile (plantedCoreCost μ β) δ q₁ q₂ r=
      weightedAmplitudeTrialProfile μ β δ q₁ q₂ r := by
  rw [amplitudeDiracTrial_one μ β p₀ hr]
  have htrial := plantedProfileTrial_eq μ β ⟨abs_nonneg r,hr⟩
  rw [sq_abs] at htrial
  unfold latitudePressureTrial weightedAmplitudeTrialProfile
  linarith

theorem weightedAmplitudeBankTrial_at (μ : FiniteMixture) (β δ q₁ q₂ : ℝ)
    (p₀ : Degree μ.maxDegree) (k : Fin 2) (τ : ℝ) {r : ℝ} (hr : |r|<1) :
    β^2*μ.xi r+amplitudeDiracTrial μ β p₀ (amplitudeAt k τ) r+
        Real.log (1-r^2)/2-2*sourceProfile (plantedCoreCost μ β) δ q₁ q₂ r=
      weightedAmplitudeTrialProfile μ β δ q₁ q₂ r+
        τ*(2+τ)*weightedAmplitudeShift μ β p₀ k r := by
  rw [amplitudeDiracTrial_at,amplitudeDiracShiftCoefficient_eq_source]
  have hh := weightedAmplitudeBankTrial_one μ β δ q₁ q₂ p₀ hr
  unfold weightedAmplitudeShift
  linarith

/-- Every actual signed bank latitude trial is below the attained compact
source envelope. -/
theorem weightedAmplitudeBankTrial_le_envelope (μ : FiniteMixture) (β δ q₁ q₂ : ℝ)
    (p₀ : Degree μ.maxDegree) (k : Fin 2) (τ : ℝ) {ρ r : ℝ}
    (hρ0 : 0≤ρ) (hρ : ρ<1) (hr : |r|≤ρ) :
    β^2*μ.xi r+amplitudeDiracTrial μ β p₀ (amplitudeAt k τ) r+
        Real.log (1-r^2)/2-2*sourceProfile (plantedCoreCost μ β) δ q₁ q₂ r≤
      weightedAmplitudeTrialEnvelope μ β δ q₁ q₂ p₀ k ρ hρ0 hρ τ := by
  rw [weightedAmplitudeBankTrial_at μ β δ q₁ q₂ p₀ k τ (hr.trans_lt hρ)]
  let : Nonempty (WeightedTrialLatitude ρ) := ⟨⟨0,by constructor <;> linarith⟩⟩
  exact CompactAmplitudeEnvelope.maximizer_property
    (fun t : WeightedTrialLatitude ρ => weightedAmplitudeTrialProfile μ β δ q₁ q₂ t)
    (fun t : WeightedTrialLatitude ρ => weightedAmplitudeShift μ β p₀ k t)
    (weightedAmplitudeTrialProfile_compact_continuous μ β δ q₁ q₂ hρ)
    ((weightedAmplitudeShift_continuous μ β p₀ k).comp continuous_subtype_val) τ
    ⟨r,abs_le.mp hr⟩

end
end SlowEquilibration.SphericalModel

-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourcePairSameReferenceHazard
public import SlowEquilibration.ConditionedEntranceFrozenTiltIntegrability

/-! A source reference resolved on a fixed spin law has the same physical
cap hazard for any jointly measurable representative equal almost everywhere
under the globally tilted law. The unresolved killing pairing is smaller. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
open SphericalAging.HardSphereDynamics SmoothKilled
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem source_pair_cap_hazard_congr_of_ae
    {N : ℕ} (hN : 1≤N) (β : ℝ) (H₀ : Vector N→ℝ)
    (hH₀ : Continuous H₀) (w : Vector N×Vector N→ℝ)
    (hw : Continuous w) (M : ℝ) (hM : 0<M)
    (α : ℝ) (Γ : Vector N→ℝ)
    (hΓ : Integrable Γ (gibbsLaw N β H₀))
    (F : Vector N×Vector N→ℝ)
    (hF : F=ᵐ[normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M]
      (fun z => Γ z.2)) :
    let ν := normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M
    Integrable (fun z => PhysicalHitting.capKilling α z.1 z.2*F z) ν ∧
    (∫ z,PhysicalHitting.capKilling α z.1 z.2*F z ∂ν)=
      (∫ z,PhysicalHitting.capKilling α z.1 z.2*Γ z.2 ∂ν) := by
  dsimp only
  let ν := normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M
  let κ : Vector N×Vector N→ℝ := fun z =>
    PhysicalHitting.capKilling α z.1 z.2
  have hκ : Continuous κ := capKilling_jointContinuous α
  have hΓκ : Integrable (fun z => κ z*Γ z.2) ν :=
    frozen_integrable_mul_under_normalizedTilt hN β H₀ hH₀ w κ hw hκ
      hM Γ hΓ
  have hFκ : (fun z => κ z*F z)=ᵐ[ν](fun z => κ z*Γ z.2) :=
    hF.mono (fun z hz => by
      change κ z*F z=κ z*Γ z.2
      rw [hz])
  exact ⟨hΓκ.congr hFκ.symm,integral_congr_ae hFκ⟩

theorem source_pair_unresolved_hazard_le
    {E : Type*} [MeasurableSpace E] (ν : Measure E)
    (κ F U : E→ℝ)
    (hκ : ∀ z,0≤κ z)
    (hFi : Integrable (fun z => κ z*F z) ν)
    (hBounds : ∀ᵐ z ∂ν,0≤F z ∧ 0≤U z ∧ U z≤1) :
    (∫ z,κ z*F z*(1-U z) ∂ν)≤(∫ z,κ z*F z ∂ν) := by
  have hnonneg : ∀ᵐ z ∂ν,0≤κ z*F z*(1-U z) := by
    filter_upwards [hBounds] with z hz
    exact mul_nonneg (mul_nonneg (hκ z) hz.1) (by linarith [hz.2.2])
  have hle : ∀ᵐ z ∂ν,κ z*F z*(1-U z)≤κ z*F z := by
    filter_upwards [hBounds] with z hz
    nlinarith [mul_nonneg (mul_nonneg (hκ z) hz.1) hz.2.1]
  exact integral_mono_of_nonneg hnonneg hFi hle

end SlowEquilibration.ConditionedEntrance

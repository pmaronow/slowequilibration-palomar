-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceFrozenTiltIntegrability
public import SlowEquilibration.ConditionedEntranceTiltCommutator

/-! A frozen positive reference resolvent of Gibbs mass two has tilted
mass at most six under the source's first axis moment. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 450000

theorem frozen_reference_tilt_mass_le_six_of_first_axis_moment
    {N : ℕ} (hN : 1≤N) (β : ℝ) (H : Vector N→ℝ)
    (hH : Continuous H) (w : Vector N×Vector N→ℝ) (hw : Continuous w)
    (M η : ℝ) (hη : 0≤η) (hηhalf : η≤1/2) (hM : 1-η≤M)
    (hAxisExp : ∀ᵐ x ∂gibbsLaw N β H,
      (∫ u, Real.exp (w (u,x)) ∂sphereLaw N) ≤ 1+η)
    (F : Vector N×Vector N→ℝ)
    (hFrozen : ∀ u v x, F (u,x)=F (v,x))
    (F₀ : sphericalSobolevGraph hN β H hH)
    (hFrep : (fun x => F (0,x)) =ᵐ[gibbsLaw N β H] F₀.val.fst)
    (hF₀lo : ∀ᵐ x ∂gibbsLaw N β H, 1≤F₀.val.fst x)
    (hFmass : (∫ x,F (0,x) ∂gibbsLaw N β H)=2) :
    (∫ z,F z ∂normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H)) w M) ≤ 6 := by
  let : IsProbabilityMeasure (sphereLaw N) := sphereLaw_probability N
  let : IsProbabilityMeasure (gibbsLaw N β H) := gibbsLaw_probability hN β hH
  let Γ : Vector N→ℝ := fun x => F (0,x)
  have hMp : 0<M := by linarith
  have hΓ : Integrable Γ (gibbsLaw N β H) :=
    ((Lp.memLp F₀.val.fst).integrable (by norm_num)).congr hFrep.symm
  have hΓpos : ∀ᵐ x ∂gibbsLaw N β H, 0≤Γ x := by
    filter_upwards [hFrep,hF₀lo] with x hf hlo
    dsimp only [Γ]
    rw [hf]
    linarith
  have hΓtilt : Integrable (fun z : Vector N×Vector N => Γ z.2)
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H)) w M) := by
    simpa only [one_mul] using frozen_integrable_mul_under_normalizedTilt
      hN β H hH w (fun _ => 1) hw continuous_const hMp Γ hΓ
  have hExpΓ : Integrable (fun z : Vector N×Vector N =>
      Real.exp (w z)*Γ z.2)
      ((sphereLaw N).prod (gibbsLaw N β H)) :=
    (integrable_normalizedTilt_iff _ w _ hw.measurable hMp).mp hΓtilt
  have hProj := exponential_tilt_frozen_projection (sphereLaw N)
    (gibbsLaw N β H) w hw.measurable hη hηhalf hM Γ hΓ hΓpos
      hExpΓ hAxisExp
  change (∫ z,Γ z.2 ∂normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H)) w M) ≤
        3*(∫ x,Γ x ∂gibbsLaw N β H) at hProj
  rw [hFmass] at hProj
  norm_num at hProj
  have hEq : (fun z : Vector N×Vector N => F z)=fun z => Γ z.2 := by
    funext z
    exact hFrozen z.1 0 z.2
  rw [hEq]
  exact hProj

end SlowEquilibration.ConditionedEntrance

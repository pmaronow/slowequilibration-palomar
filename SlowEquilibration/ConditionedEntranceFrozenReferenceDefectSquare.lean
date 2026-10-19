-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceFrozenTiltIntegrability
public import SlowEquilibration.ConditionedEntranceTiltCommutator

/-! The actual second axis moment controls the full frozen reference
commutator, whose unperturbed Gibbs mass is two. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 450000

theorem frozen_reference_defect_square_le_four_of_second_axis_moment
    {N : ℕ} (hN : 1≤N) (β : ℝ) (H : Vector N→ℝ)
    (hH : Continuous H) (w : Vector N×Vector N→ℝ) (hw : Continuous w)
    (M ε : ℝ) (hM : 1/2≤M) (hε : 0≤ε)
    (hAxis : ∀ᵐ x ∂gibbsLaw N β H,
      (∫ u, Real.exp (w (u,x))*(tiltDefect w (u,x))^2
        ∂sphereLaw N) ≤ ε)
    (F : Vector N×Vector N→ℝ)
    (hFrozen : ∀ u v x, F (u,x)=F (v,x))
    (F₀ : sphericalSobolevGraph hN β H hH)
    (hFrep : (fun x => F (0,x)) =ᵐ[gibbsLaw N β H] F₀.val.fst)
    (hF₀lo : ∀ᵐ x ∂gibbsLaw N β H, 1≤F₀.val.fst x)
    (hFmass : (∫ x,F (0,x) ∂gibbsLaw N β H)=2) :
    (∫ z,(tiltDefect w z)^2*F z ∂normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H)) w M) ≤ 4*ε := by
  let : IsProbabilityMeasure (sphereLaw N) := sphereLaw_probability N
  let : IsProbabilityMeasure (gibbsLaw N β H) := gibbsLaw_probability hN β hH
  let Γ : Vector N→ℝ := fun x => F (0,x)
  have hMp : 0<M := by linarith
  have hΓ : Integrable Γ (gibbsLaw N β H) :=
    ((Lp.memLp F₀.val.fst).integrable (by norm_num)).congr hFrep.symm
  have hΓpos : ∀ᵐ x ∂gibbsLaw N β H,0≤Γ x := by
    filter_upwards [hFrep,hF₀lo] with x hf hlo
    dsimp only [Γ]
    rw [hf]
    linarith
  let g : Vector N×Vector N→ℝ := fun z => (tiltDefect w z)^2
  have hg : Continuous g := by
    unfold g tiltDefect
    fun_prop
  have hTilt : Integrable (fun z => g z*Γ z.2)
      (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H)) w M) :=
    frozen_integrable_mul_under_normalizedTilt hN β H hH w g hw hg hMp Γ hΓ
  have hExp : Integrable (fun z => Real.exp (w z)*g z*Γ z.2)
      ((sphereLaw N).prod (gibbsLaw N β H)) := by
    simpa only [mul_assoc] using
      (integrable_normalizedTilt_iff _ w _ hw.measurable hMp).mp hTilt
  have hProj := tiltDefect_square_projection (sphereLaw N)
    (gibbsLaw N β H) w hw.measurable hM hε Γ hΓ hΓpos hExp hAxis
  change (∫ z,g z*Γ z.2 ∂normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H)) w M) ≤
        2*ε*(∫ x,Γ x ∂gibbsLaw N β H) at hProj
  rw [hFmass] at hProj
  have hBound : (∫ z,g z*Γ z.2 ∂normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H)) w M) ≤ 4*ε := by
    nlinarith
  have hEq : (fun z : Vector N×Vector N => g z*F z)=
      fun z => g z*Γ z.2 := by
    funext z
    rw [hFrozen z.1 0 z.2]
  change (∫ z,g z*F z ∂normalizedTilt
    ((sphereLaw N).prod (gibbsLaw N β H)) w M) ≤ 4*ε
  rw [hEq]
  exact hBound

end SlowEquilibration.ConditionedEntrance

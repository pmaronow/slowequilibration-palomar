-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceFrozenTiltIntegrability
public import SlowEquilibration.ConditionedEntranceTiltCommutator
public import SlowEquilibration.SphericalUniformStartEntropy

/-! Pointwise first- and second-axis projections for the positive
uniform-start forcing `1+f₀`, whose Gibbs mass is exactly two. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem positive_uniform_initial_tilt_mass_and_defect_bounds
    {N : ℕ} (hN : 1≤N) (β : ℝ) (H : Vector N→ℝ)
    (hH : Continuous H) (w : Vector N×Vector N→ℝ) (hw : Continuous w)
    (M η ε : ℝ) (hη : 0≤η) (hηhalf : η≤1/2)
    (hMlower : 1-η≤M) (hMhalf : 1/2≤M) (hε : 0≤ε)
    (hAxisExp : ∀ᵐ x ∂gibbsLaw N β H,
      (∫ u, Real.exp (w (u,x)) ∂sphereLaw N) ≤ 1+η)
    (hAxisDefect : ∀ᵐ x ∂gibbsLaw N β H,
      (∫ u, Real.exp (w (u,x))*(tiltDefect w (u,x))^2
        ∂sphereLaw N) ≤ ε) :
    let I : Vector N×Vector N→ℝ := fun z =>
      1+uniformInitialDensity N β H z.2
    let ν := normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H)) w M
    (∫ z,I z ∂ν) ≤ 6 ∧
    (∫ z,(tiltDefect w z)^2*I z ∂ν) ≤ 4*ε := by
  dsimp only
  let : IsProbabilityMeasure (sphereLaw N) := sphereLaw_probability N
  let : IsProbabilityMeasure (gibbsLaw N β H) := gibbsLaw_probability hN β hH
  let Γ : Vector N→ℝ := fun x => 1+uniformInitialDensity N β H x
  let I : Vector N×Vector N→ℝ := fun z => Γ z.2
  let ν := normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H)) w M
  have hMp : 0<M := by linarith
  have hΓc : Continuous Γ := continuous_const.add
    (uniformInitialDensity_continuous β H hH)
  have hΓ : Integrable Γ (gibbsLaw N β H) :=
    integrable_gibbs_of_continuous hN β hH hΓc
  have hΓpos : ∀ᵐ x ∂gibbsLaw N β H,0≤Γ x := .of_forall (fun x => by
    have hp := uniformInitialDensity_pos hN β H hH x
    dsimp only [Γ]
    linarith)
  have hΓmass : (∫ x,Γ x ∂gibbsLaw N β H)=2 := by
    dsimp only [Γ]
    rw [integral_add (integrable_const (1 : ℝ))
      (integrable_gibbs_of_continuous hN β hH
        (uniformInitialDensity_continuous β H hH))]
    simp only [integral_const,probReal_univ,one_smul,
      uniformInitialDensity_integral hN β H hH]
    norm_num
  have hTiltI : Integrable I ν := by
    simpa only [I,ν,one_mul] using frozen_integrable_mul_under_normalizedTilt
      hN β H hH w (fun _ => 1) hw continuous_const hMp Γ hΓ
  have hExpI : Integrable (fun z : Vector N×Vector N =>
      Real.exp (w z)*Γ z.2)
      ((sphereLaw N).prod (gibbsLaw N β H)) :=
    (integrable_normalizedTilt_iff _ w _ hw.measurable hMp).mp hTiltI
  have hMassProj := exponential_tilt_frozen_projection (sphereLaw N)
    (gibbsLaw N β H) w hw.measurable hη hηhalf hMlower Γ hΓ hΓpos
      hExpI hAxisExp
  rw [hΓmass] at hMassProj
  have hMass : (∫ z,I z ∂ν) ≤ 6 := by
    change (∫ z,Γ z.2 ∂normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H)) w M) ≤ 6
    nlinarith [hMassProj]
  let g : Vector N×Vector N→ℝ := fun z => (tiltDefect w z)^2
  have hg : Continuous g := by unfold g tiltDefect; fun_prop
  have hTiltKI : Integrable (fun z => g z*Γ z.2) ν :=
    frozen_integrable_mul_under_normalizedTilt hN β H hH w g hw hg hMp Γ hΓ
  have hExpKI : Integrable (fun z => Real.exp (w z)*g z*Γ z.2)
      ((sphereLaw N).prod (gibbsLaw N β H)) := by
    simpa only [mul_assoc] using
      (integrable_normalizedTilt_iff _ w _ hw.measurable hMp).mp hTiltKI
  have hDefectProj := tiltDefect_square_projection (sphereLaw N)
    (gibbsLaw N β H) w hw.measurable hMhalf hε Γ hΓ hΓpos
      hExpKI hAxisDefect
  rw [hΓmass] at hDefectProj
  have hDefect : (∫ z,g z*I z ∂ν) ≤ 4*ε := by
    change (∫ z,(tiltDefect w z)^2*Γ z.2 ∂normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H)) w M) ≤ 4*ε
    nlinarith [hDefectProj]
  exact ⟨hMass,hDefect⟩

end SlowEquilibration.ConditionedEntrance

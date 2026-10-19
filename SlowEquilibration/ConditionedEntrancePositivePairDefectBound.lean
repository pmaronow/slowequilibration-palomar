-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePositiveInitialTiltBounds
public import SlowEquilibration.ConditionedEntranceFrozenReferenceTiltMass
public import SlowEquilibration.ConditionedEntranceFrozenReferenceDefectSquare
public import SlowEquilibration.ConditionedEntrancePositiveDefectCauchy

/-! The actual source-pairing commutator is at most `10√ε`.
The only analytic inputs are the two axis moments, normalization,
and the physical frozen reference graph of Gibbs mass two. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 550000

theorem positive_pair_defect_le_ten_sqrt_of_axis_moments
    {N : ℕ} (hN : 1≤N) (β : ℝ) (H : Vector N→ℝ)
    (hH : Continuous H) (w : Vector N×Vector N→ℝ) (hw : Continuous w)
    (M η ε : ℝ) (hη : 0≤η) (hηhalf : η≤1/2)
    (hMlower : 1-η≤M) (hMhalf : 1/2≤M) (hε : 0≤ε)
    (hAxisExp : ∀ᵐ x ∂gibbsLaw N β H,
      (∫ u, Real.exp (w (u,x)) ∂sphereLaw N) ≤ 1+η)
    (hAxisDefect : ∀ᵐ x ∂gibbsLaw N β H,
      (∫ u, Real.exp (w (u,x))*(tiltDefect w (u,x))^2
        ∂sphereLaw N) ≤ ε)
    (F U : Vector N×Vector N→ℝ) (hFm : Measurable F) (hUm : Measurable U)
    (hFrozen : ∀ u v x,F (u,x)=F (v,x))
    (F₀ : sphericalSobolevGraph hN β H hH)
    (hFrep : (fun x => F (0,x)) =ᵐ[gibbsLaw N β H] F₀.val.fst)
    (hF₀lo : ∀ᵐ x ∂gibbsLaw N β H,1≤F₀.val.fst x)
    (hFmass : (∫ x,F (0,x) ∂gibbsLaw N β H)=2)
    (hFlo : ∀ᵐ z ∂normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H)) w M,1≤F z)
    (hUb : ∀ᵐ z ∂normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H)) w M,
      0≤U z ∧ U z≤1) :
    let I : Vector N×Vector N→ℝ := fun z =>
      1+uniformInitialDensity N β H z.2
    let ν := normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H)) w M
    |∫ z,tiltDefect w z*(I z-F z)*U z ∂ν| ≤ 10*Real.sqrt ε := by
  dsimp only
  let : IsProbabilityMeasure (gibbsLaw N β H) := gibbsLaw_probability hN β hH
  let I₀ : Vector N→ℝ := fun x => 1+uniformInitialDensity N β H x
  let I : Vector N×Vector N→ℝ := fun z => I₀ z.2
  let ν := normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H)) w M
  let k : Vector N×Vector N→ℝ := tiltDefect w
  have hMp : 0<M := by linarith
  have hIc : Continuous I₀ := continuous_const.add
    (uniformInitialDensity_continuous β H hH)
  have hI₀i : Integrable I₀ (gibbsLaw N β H) :=
    integrable_gibbs_of_continuous hN β hH hIc
  have hF₀i : Integrable (fun x => F (0,x)) (gibbsLaw N β H) :=
    ((Lp.memLp F₀.val.fst).integrable (by norm_num)).congr hFrep.symm
  have hkc : Continuous k := by unfold k tiltDefect; fun_prop
  have hg : Continuous (fun z : Vector N×Vector N => (k z)^2) := hkc.pow 2
  have hIi : Integrable I ν := by
    simpa only [I,ν,one_mul] using frozen_integrable_mul_under_normalizedTilt
      hN β H hH w (fun _ => 1) hw continuous_const hMp I₀ hI₀i
  have hFi : Integrable F ν := by
    have hf := frozen_integrable_mul_under_normalizedTilt hN β H hH
      w (fun _ => 1) hw continuous_const hMp (fun x => F (0,x)) hF₀i
    have heq : (fun z : Vector N×Vector N => F z)=
        fun z => F (0,z.2) := by
      funext z
      exact hFrozen z.1 0 z.2
    change Integrable (fun z => F z) ν
    rw [heq]
    simpa only [one_mul] using hf
  have hKIi : Integrable (fun z => (k z)^2*I z) ν :=
    frozen_integrable_mul_under_normalizedTilt hN β H hH w
      (fun z => (k z)^2) hw hg hMp I₀ hI₀i
  have hKFi : Integrable (fun z => (k z)^2*F z) ν := by
    have hf := frozen_integrable_mul_under_normalizedTilt hN β H hH
      w (fun z => (k z)^2) hw hg hMp (fun x => F (0,x)) hF₀i
    have heq : (fun z : Vector N×Vector N => (k z)^2*F z)=
        fun z => (k z)^2*F (0,z.2) := by
      funext z
      rw [hFrozen z.1 0 z.2]
    rw [heq]
    exact hf
  obtain ⟨hImass,hKImom⟩ := positive_uniform_initial_tilt_mass_and_defect_bounds
    hN β H hH w hw M η ε hη hηhalf hMlower hMhalf hε hAxisExp hAxisDefect
  have hFmassTilt := frozen_reference_tilt_mass_le_six_of_first_axis_moment
    hN β H hH w hw M η hη hηhalf hMlower hAxisExp F hFrozen
      F₀ hFrep hF₀lo hFmass
  have hKFmom := frozen_reference_defect_square_le_four_of_second_axis_moment
    hN β H hH w hw M ε hMhalf hε hAxisDefect F hFrozen
      F₀ hFrep hF₀lo hFmass
  have hIm : Measurable I := hIc.measurable.comp measurable_snd
  have hIpos : ∀ᵐ z ∂ν,1≤I z := .of_forall (fun z => by
    have hp := uniformInitialDensity_pos hN β H hH z.2
    dsimp only [I,I₀]
    linarith)
  have h := positive_initial_reference_defect_le_ten_sqrt ν k I F U
    hkc.measurable hIm hFm hUm hIpos hFlo hUb hIi hFi hKIi hKFi
    ε hε hImass hFmassTilt hKImom hKFmom
  simpa only [I,I₀,k,ν] using h

end SlowEquilibration.ConditionedEntrance

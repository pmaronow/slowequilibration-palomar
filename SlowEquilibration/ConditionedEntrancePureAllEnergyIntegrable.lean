-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureSquareReferenceGlobalIntegrable
public import SlowEquilibration.ConditionedEntrancePureGlobalBounds
public import SlowEquilibration.ConditionedEntranceZeroDefectIntegrable
public import SlowEquilibration.ConditionedEntranceGradientDefectIntegrable

/-! The physical source square, reference, and both signed commutator
densities are L¹ under the global tilt once the three square densities
from the same witnesses are L¹. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SphericalAging.HardSphereDynamics
open scoped NNReal BigOperators
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 700000

theorem pure_joint_all_energy_globalTilt_integrable
    {N : ℕ} (hN : 1 ≤ N) (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (α : ℝ) (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (J : Disorder N (FiniteMixture.pure d hd c hc).maxDegree) (e : ℝ)
    (F U : SourceParameters N (FiniteMixture.pure d hd c hc) × Vector N → ℝ)
    (GF G : (Fin N × Fin N) → SourceParameters N (FiniteMixture.pure d hd c hc) × Vector N → ℝ)
    (hF : StronglyMeasurable F) (hU : StronglyMeasurable U)
    (hGF : ∀ ij, StronglyMeasurable (GF ij))
    (hG : ∀ ij, StronglyMeasurable (G ij))
    (hphys : ∀ v : Vector N, OnSphere v →
      ∀ᵐ x ∂gibbsLaw N β
        (pureSourceSmoothCutoffField d hd c hc Q J v e α χ),
        1 ≤ F ((J,(v,(e,0))),x) ∧
        ‖F ((J,(v,(e,0))),x)‖ ≤
          1+Real.exp (2*β*derivativeConstant (mixtureCoefficients (FiniteMixture.pure d hd c hc))*(N : ℝ)) ∧
        0 ≤ U ((J,(v,(e,0))),x) ∧ U ((J,(v,(e,0))),x) ≤ 1)
    (M : ℝ) (hM : 0 < M) :
    let H₀ := fieldOfMixture (FiniteMixture.pure d hd c hc) J
    let H : Vector N → Vector N → ℝ := fun v x =>
      pureSourceSmoothCutoffField d hd c hc Q J v e α χ x
    let w : Vector N × Vector N → ℝ := fun z =>
      β*(H z.1 z.2-H₀ z.2)
    let ν := normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M
    let Fa : Vector N×Vector N → ℝ := fun z => F ((J,(z.1,(e,0))),z.2)
    let Ua : Vector N×Vector N → ℝ := fun z => U ((J,(z.1,(e,0))),z.2)
    let GFa : (Fin N×Fin N) → Vector N×Vector N → ℝ := fun ij z =>
      GF ij ((J,(z.1,(e,0))),z.2)
    let Ga : (Fin N×Fin N) → Vector N×Vector N → ℝ := fun ij z =>
      G ij ((J,(z.1,(e,0))),z.2)
    Integrable (fun z => Fa z*(∑ ij : Fin N×Fin N, (Ga ij z)^2)) ν →
    Integrable (fun z => (tiltDefect w z)^2*(Fa z-1)) ν →
    Integrable (fun z => (tiltDefect w z)^2*
      (∑ ij : Fin N×Fin N, (GFa ij z)^2/Fa z)) ν →
    Integrable (fun z => Fa z*Ua z^2) ν ∧
    Integrable (fun z => PhysicalHitting.capKilling α z.1 z.2*Fa z) ν ∧
    Integrable (fun z => tiltDefect w z*(Fa z-1)*Ua z^2) ν ∧
    Integrable (fun z => tiltDefect w z*Ua z*
      (∑ ij : Fin N×Fin N, GFa ij z*Ga ij z)) ν := by
  dsimp only
  let H₀ := fieldOfMixture (FiniteMixture.pure d hd c hc) J
  let H : Vector N → Vector N → ℝ := fun v x =>
    pureSourceSmoothCutoffField d hd c hc Q J v e α χ x
  let w : Vector N × Vector N → ℝ := fun z => β*(H z.1 z.2-H₀ z.2)
  let ν := normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M
  let Fa : Vector N×Vector N → ℝ := fun z => F ((J,(z.1,(e,0))),z.2)
  let Ua : Vector N×Vector N → ℝ := fun z => U ((J,(z.1,(e,0))),z.2)
  let GFa : (Fin N×Fin N) → Vector N×Vector N → ℝ := fun ij z =>
    GF ij ((J,(z.1,(e,0))),z.2)
  let Ga : (Fin N×Fin N) → Vector N×Vector N → ℝ := fun ij z =>
    G ij ((J,(z.1,(e,0))),z.2)
  intro hBi hKi hJi
  have hphys₀ (v : Vector N) (hv : OnSphere v) :
      ∀ᵐ x ∂gibbsLaw N β (H v),
      1 ≤ F ((J,(v,(e,0))),x) ∧
      0 ≤ U ((J,(v,(e,0))),x) ∧ U ((J,(v,(e,0))),x) ≤ 1 :=
    (hphys v hv).mono (fun _ hx => ⟨hx.1,hx.2.2⟩)
  have hglobal := pure_joint_reference_globalTilt_bounds hN d hd c hc Q
    α χ hχ β J e F U hF hU hphys₀ M
  have hphys₁ (v : Vector N) (hv : OnSphere v) :
      ∀ᵐ x ∂gibbsLaw N β (H v),
      ‖F ((J,(v,(e,0))),x)‖ ≤
        1+Real.exp (2*β*derivativeConstant (mixtureCoefficients (FiniteMixture.pure d hd c hc))*(N : ℝ)) ∧
      0 ≤ U ((J,(v,(e,0))),x) ∧ U ((J,(v,(e,0))),x) ≤ 1 :=
    (hphys v hv).mono (fun _ hx => ⟨hx.2.1,hx.2.2⟩)
  obtain ⟨hAi,hRi⟩ := pure_joint_square_reference_globalTilt_integrable
    hN d hd c hc Q α hα χ hχ β J e F U hF hU hphys₁ M hM
  have hpair : Measurable (fun z : Vector N × Vector N =>
      (((J,(z.1,(e,0))),z.2) : SourceParameters N (FiniteMixture.pure d hd c hc) × Vector N)) := by fun_prop
  have hFm : Measurable Fa := (hF.comp_measurable hpair).measurable
  have hUm : Measurable Ua := (hU.comp_measurable hpair).measurable
  have hGFm (ij : Fin N×Fin N) : Measurable (GFa ij) :=
    ((hGF ij).comp_measurable hpair).measurable
  have hGm (ij : Fin N×Fin N) : Measurable (Ga ij) :=
    ((hG ij).comp_measurable hpair).measurable
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff (FiniteMixture.pure d hd c hc) J).continuous
  have hH : Continuous (fun z : Vector N×Vector N => H z.1 z.2) :=
    (pure_axisJointHamiltonian_contDiff d hd c hc Q α χ hχ J e).continuous
  have hw : Continuous w := (hH.sub (hH₀.comp continuous_snd)).const_mul β
  have hkm : Measurable (tiltDefect w) := by
    unfold tiltDefect
    fun_prop
  have hFlo : ∀ᵐ z ∂ν, 1 ≤ Fa z := hglobal.mono (fun _ hx => hx.1)
  have hUb : ∀ᵐ z ∂ν, 0 ≤ Ua z ∧ Ua z ≤ 1 :=
    hglobal.mono (fun _ hx => hx.2)
  have hKsigned := weighted_zero_defect_commutator_integrable
    ν (tiltDefect w) Fa Ua hkm hFm hUm hFlo hUb hKi hAi
  have hUabs : ∀ᵐ z ∂ν, |Ua z| ≤ 1 := hUb.mono (fun z hx => by
    rw [abs_of_nonneg hx.1]
    exact hx.2)
  have hCsigned := weighted_gradient_defect_integrable ν (tiltDefect w) Fa Ua
    GFa Ga hkm hFm hUm hGFm hGm hFlo hUabs hJi hBi
  exact ⟨hAi,hRi,hKsigned,hCsigned⟩

end SlowEquilibration.ConditionedEntrance

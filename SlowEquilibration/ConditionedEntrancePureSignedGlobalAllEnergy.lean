-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureSignedGlobalAllMoments
public import SlowEquilibration.ConditionedEntrancePureAllEnergyIntegrable

/-! The actual joint source weighted energy with both commutator signs
retained through the fibre step. It uses the same physical representatives
and scalar bounds as the unsigned reduction. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SmoothKilledGeneral
open SphericalAging.HardSphereDynamics
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

set_option linter.unusedVariables false in
theorem pureJointReferenceSignedReducedEnergy_globalAllEnergyIntegrable (hN : 1≤N)
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (α : ℝ) (hα : 0<α) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (hβ : 0≤β) (θ : ℝ≥0) (hθ : 0<θ)
    (J : Disorder N (FiniteMixture.pure d hd c hc).maxDegree)
    (hJ : J∈regularDisorder) (e : ℝ)
    (M : ℝ) (hM : 0<M) :
    let μ := FiniteMixture.pure d hd c hc
    let H := pureSourceJointHamiltonian (N:=N) d hd c hc Q α χ
    let H₀ := fun z : SourceParameters N μ×Vector N => fieldOfMixture μ z.1.1 z.2
    let κ := sourceJointCapKilling (N:=N) μ α
    let w := fun z => β*H z-β*H₀ z
    ∃ F : SourceParameters N μ×Vector N→ℝ,
      ∃ GF : (Fin N×Fin N)→SourceParameters N μ×Vector N→ℝ,
      ∃ U : SourceParameters N μ×Vector N→ℝ,
      ∃ G : (Fin N×Fin N)→SourceParameters N μ×Vector N→ℝ,
        StronglyMeasurable F ∧ (∀ ij,StronglyMeasurable (GF ij)) ∧
        StronglyMeasurable U ∧ (∀ ij,StronglyMeasurable (G ij)) ∧
        (∀ p q x,p.1=q.1 → F (p,x)=F (q,x)) ∧
        (∀ ij p q x,p.1=q.1 → GF ij (p,x)=GF ij (q,x)) ∧
        Measurable (jointGibbsWeightedGradientSquare β H F G) ∧
        Measurable (jointGibbsWeightedSquare β H F U) ∧
        Measurable (jointGibbsZeroDefectSquare β H w F U) ∧
        Measurable (jointGibbsKilledReference β H κ F) ∧
        Measurable (jointGibbsTiltGradientCross β H w U GF G) ∧
        Measurable (jointGibbsFisher β H₀ F GF) ∧
        (∀ p : SourceParameters N μ,∀ hp : OnSphere p.2.1,∀ _hJ : p.1∈regularDisorder,
          let D := FieldData.ofPure hN d hd c hc Q p.1 p.2.1 p.2.2.1 α χ hχ
          let D₀ := FieldData.ofOriginal hN μ p.1
          let hκ := (PhysicalHitting.capKilling_contDiff α p.2.1).continuous
          let hκ0 := PhysicalHitting.capKilling_nonneg α p.2.1
          let h := rateLaplace D β (PhysicalHitting.capKilling α p.2.1) hκ hκ0 θ
            (killingVector D β (PhysicalHitting.capKilling α p.2.1) hκ)
          ((fun x => F (p,x))=ᵐ[gibbsLaw N β D.hamiltonian]
            referenceRate D₀ β θ (referenceInitialVector D₀ β)) ∧
          ((fun x => U (p,x))=ᵐ[gibbsLaw N β D.hamiltonian] h) ∧
          (∀ᵐ x ∂gibbsLaw N β D.hamiltonian,
            1≤F (p,x) ∧ ‖F (p,x)‖≤1+Real.exp (2*β*derivativeConstant (mixtureCoefficients μ)*(N : ℝ))) ∧
          (∀ᵐ x ∂gibbsLaw N β D.hamiltonian,0≤U (p,x) ∧ U (p,x)≤1) ∧
          jointGibbsFisher β H₀ F GF p≤
            (θ : ℝ)*(2*Real.log 2+4*β*derivativeConstant (mixtureCoefficients μ)*(N : ℝ)) ∧
          jointGibbsWeightedGradientSquare β H F G p+
            (θ : ℝ)/2*jointGibbsWeightedSquare β H F U p≤
              jointGibbsKilledReference β H κ F p-
              (θ : ℝ)/2*jointGibbsZeroDefectSquare β H w F U p-
              jointGibbsTiltGradientCross β H w U GF G p ∧
          ∃ F₀ : sphericalSobolevGraph hN β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous,
            ∃ F₁ u : sphericalSobolevGraph hN β D.hamiltonian D.hamiltonian_contDiff.continuous,
              sphericalEnergyL2Map hN β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous F₀=
                referenceRate D₀ β θ (referenceInitialVector D₀ β) ∧
              sphericalEnergyL2Map hN β D.hamiltonian D.hamiltonian_contDiff.continuous u=h ∧
              ((fun x => F (p,x))=ᵐ[gibbsLaw N β D₀.hamiltonian] F₀.val.fst) ∧
              (∀ ij : Fin N×Fin N,(fun x => GF ij (p,x))=ᵐ[gibbsLaw N β D₀.hamiltonian] F₀.val.snd ij) ∧
              ((fun x => F (p,x))=ᵐ[gibbsLaw N β D.hamiltonian] F₁.val.fst) ∧
              (∀ ij : Fin N×Fin N,(fun x => GF ij (p,x))=ᵐ[gibbsLaw N β D.hamiltonian] F₁.val.snd ij) ∧
              ((fun x => U (p,x))=ᵐ[gibbsLaw N β D.hamiltonian] u.val.fst) ∧
              ∀ ij : Fin N×Fin N,(fun x => G ij (p,x))=ᵐ[gibbsLaw N β D.hamiltonian] u.val.snd ij) ∧
        Integrable (fun z : Vector N×Vector N =>
          F ((J,(z.1,(e,0))),z.2)*
            (∑ ij : Fin N×Fin N,(G ij ((J,(z.1,(e,0))),z.2))^2))
          (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture μ J)))
            (fun z : Vector N×Vector N => β*(pureSourceSmoothCutoffField d hd c hc Q J z.1 e α χ z.2-
              fieldOfMixture μ J z.2)) M) ∧
        Integrable (fun z : Vector N×Vector N =>
          (tiltDefect (fun y : Vector N×Vector N => β*(pureSourceSmoothCutoffField d hd c hc Q J y.1 e α χ y.2-
            fieldOfMixture μ J y.2)) z)^2 *
            (F ((J,(z.1,(e,0))),z.2)-1))
          (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture μ J)))
            (fun z : Vector N×Vector N => β*(pureSourceSmoothCutoffField d hd c hc Q J z.1 e α χ z.2-
              fieldOfMixture μ J z.2)) M) ∧
        Integrable (fun z : Vector N×Vector N =>
          (tiltDefect (fun y : Vector N×Vector N => β*(pureSourceSmoothCutoffField d hd c hc Q J y.1 e α χ y.2-
            fieldOfMixture μ J y.2)) z)^2 *
            (∑ ij : Fin N×Fin N,
              (GF ij ((J,(z.1,(e,0))),z.2))^2 /
                F ((J,(z.1,(e,0))),z.2)))
          (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture μ J)))
            (fun z : Vector N×Vector N => β*(pureSourceSmoothCutoffField d hd c hc Q J z.1 e α χ z.2-
              fieldOfMixture μ J z.2)) M) ∧
        Integrable (fun z : Vector N×Vector N =>
          F ((J,(z.1,(e,0))),z.2)*U ((J,(z.1,(e,0))),z.2)^2)
          (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture μ J)))
            (fun z : Vector N×Vector N => β*(pureSourceSmoothCutoffField d hd c hc Q J z.1 e α χ z.2-
              fieldOfMixture μ J z.2)) M) ∧
        Integrable (fun z : Vector N×Vector N =>
          PhysicalHitting.capKilling α z.1 z.2*F ((J,(z.1,(e,0))),z.2))
          (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture μ J)))
            (fun z : Vector N×Vector N => β*(pureSourceSmoothCutoffField d hd c hc Q J z.1 e α χ z.2-
              fieldOfMixture μ J z.2)) M) ∧
        Integrable (fun z : Vector N×Vector N =>
          tiltDefect (fun y : Vector N×Vector N => β*(pureSourceSmoothCutoffField d hd c hc Q J y.1 e α χ y.2-
            fieldOfMixture μ J y.2)) z *
          (F ((J,(z.1,(e,0))),z.2)-1)*U ((J,(z.1,(e,0))),z.2)^2)
          (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture μ J)))
            (fun z : Vector N×Vector N => β*(pureSourceSmoothCutoffField d hd c hc Q J z.1 e α χ z.2-
              fieldOfMixture μ J z.2)) M) ∧
        Integrable (fun z : Vector N×Vector N =>
          tiltDefect (fun y : Vector N×Vector N => β*(pureSourceSmoothCutoffField d hd c hc Q J y.1 e α χ y.2-
            fieldOfMixture μ J y.2)) z *
          U ((J,(z.1,(e,0))),z.2) *
          (∑ ij : Fin N×Fin N,
            GF ij ((J,(z.1,(e,0))),z.2)*G ij ((J,(z.1,(e,0))),z.2)))
          (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture μ J)))
            (fun z : Vector N×Vector N => β*(pureSourceSmoothCutoffField d hd c hc Q J z.1 e α χ z.2-
              fieldOfMixture μ J z.2)) M) := by
  dsimp only
  let μ := FiniteMixture.pure d hd c hc
  obtain ⟨F,GF,U,G,hF,hGF,hU,hG,hFf,hGFf,hBm,hAm,hKm,hRm,hCm,hJm,hE,hBi,hKi,hJi⟩ :=
    pureJointReferenceSignedReducedEnergy_globalAllMomentsIntegrable hN d hd c hc Q α hα χ hχ β hβ θ hθ J hJ e M hM
  have hphys (v : Vector N) (hv : OnSphere v) :
      ∀ᵐ x ∂gibbsLaw N β (pureSourceSmoothCutoffField d hd c hc Q J v e α χ),
        1 ≤ F ((J,(v,(e,0))),x) ∧
        ‖F ((J,(v,(e,0))),x)‖ ≤
          1+Real.exp (2*β*derivativeConstant (mixtureCoefficients μ)*(N : ℝ)) ∧
        0 ≤ U ((J,(v,(e,0))),x) ∧ U ((J,(v,(e,0))),x) ≤ 1 := by
    let p : SourceParameters N μ := (J,(v,(e,0)))
    obtain ⟨hFs,hUs,hFb,hUb,hFisher,hEnergy,hGraph⟩ := hE p hv hJ
    simp only [FieldData.ofPure_hamiltonian] at hFb hUb
    filter_upwards [hFb,hUb] with x hf hu
    exact ⟨hf.1,hf.2,hu.1,hu.2⟩
  obtain ⟨hAi,hRi,hKsi,hCsi⟩ := pure_joint_all_energy_globalTilt_integrable
    hN d hd c hc Q α hα χ hχ β J e F U GF G hF hU hGF hG hphys M hM
      hBi hKi hJi
  exact ⟨F,GF,U,G,hF,hGF,hU,hG,hFf,hGFf,hBm,hAm,hKm,hRm,hCm,hJm,hE,
    hBi,hKi,hJi,hAi,hRi,hKsi,hCsi⟩

end SlowEquilibration.ConditionedEntrance

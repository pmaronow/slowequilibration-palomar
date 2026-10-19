-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceFrozenMomentIntegrability
public import SlowEquilibration.ConditionedEntranceSignedGlobalGradientEnergy
public import SlowEquilibration.ConditionedEntranceJointSignedReducedEnergy
public import SlowEquilibration.ConditionedEntranceJointEnergyPhysical
public import SlowEquilibration.ConditionedEntranceSourceReferenceBounds
public import SlowEquilibration.ConditionedEntranceSquareCommutatorReduction
public import SlowEquilibration.SphericalBoundedSquareIntegrability
public import SlowEquilibration.SphericalJointZeroDefectIntegral

/-! The actual joint source weighted energy with both commutator signs
retained through the fibre step. It uses the same physical representatives
and scalar bounds as the unsigned reduction. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SmoothKilled
open SphericalAging.HardSphereDynamics
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

theorem sourceJointReferenceSignedReducedEnergy_globalAllMomentsIntegrable (hN : 1≤N) (μ : FiniteMixture)
    (hnp : μ.minDegree<μ.maxDegree) (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≤1)
    (α : ℝ) (hα : 0<α) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (hβ : 0≤β) (θ : ℝ≥0) (hθ : 0<θ)
    (J : Disorder N μ.maxDegree) (hJ : J∈regularDisorder)
    (e k hbar kbar B R : ℝ) (hh : |e|≤hbar) (hk : |k|≤kbar)
    (hB : 0≤B) (hR : 0≤R)
    (hχB : ∀ s, |χ s| ≤ B) (hχR : ∀ s, R < |s| → χ s = 0)
    (M : ℝ) (hM : 0<M) :
    let H := sourceJointHamiltonian (N:=N) μ Q hQ hnp α χ
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
          let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp
          let hκ := (PhysicalHitting.capKilling_contDiff α p.2.1).continuous
          let hκ0 := PhysicalHitting.capKilling_nonneg α p.2.1
          let h := rateLaplace D β (PhysicalHitting.capKilling α p.2.1) hκ hκ0 θ
            (killingVector D β (PhysicalHitting.capKilling α p.2.1) hκ)
          ((fun x => F (p,x))=ᵐ[gibbsLaw N β D.hamiltonian]
            referenceRate D.baseData β θ (referenceInitialVector D.baseData β)) ∧
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
          ∃ F₀ : sphericalSobolevGraph hN β D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous,
            ∃ F₁ u : sphericalSobolevGraph hN β D.hamiltonian D.hamiltonian_contDiff.continuous,
              sphericalEnergyL2Map hN β D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous F₀=
                referenceRate D.baseData β θ (referenceInitialVector D.baseData β) ∧
              sphericalEnergyL2Map hN β D.hamiltonian D.hamiltonian_contDiff.continuous u=h ∧
              ((fun x => F (p,x))=ᵐ[gibbsLaw N β D.baseData.hamiltonian] F₀.val.fst) ∧
              (∀ ij : Fin N×Fin N,(fun x => GF ij (p,x))=ᵐ[gibbsLaw N β D.baseData.hamiltonian] F₀.val.snd ij) ∧
              ((fun x => F (p,x))=ᵐ[gibbsLaw N β D.hamiltonian] F₁.val.fst) ∧
              (∀ ij : Fin N×Fin N,(fun x => GF ij (p,x))=ᵐ[gibbsLaw N β D.hamiltonian] F₁.val.snd ij) ∧
              ((fun x => U (p,x))=ᵐ[gibbsLaw N β D.hamiltonian] u.val.fst) ∧
              ∀ ij : Fin N×Fin N,(fun x => G ij (p,x))=ᵐ[gibbsLaw N β D.hamiltonian] u.val.snd ij) ∧
        Integrable (fun z : Vector N×Vector N =>
          F ((J,(z.1,(e,k))),z.2)*
            (∑ ij : Fin N×Fin N,(G ij ((J,(z.1,(e,k))),z.2))^2))
          (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture μ J)))
            (fun z : Vector N×Vector N => β*(sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2-
              fieldOfMixture μ J z.2)) M) ∧
        Integrable (fun z : Vector N×Vector N =>
          (tiltDefect (fun y : Vector N×Vector N => β*(sourceSmoothCutoffField μ Q hQ hnp J y.1 e k α χ y.2-
            fieldOfMixture μ J y.2)) z)^2 *
            (F ((J,(z.1,(e,k))),z.2)-1))
          (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture μ J)))
            (fun z : Vector N×Vector N => β*(sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2-
              fieldOfMixture μ J z.2)) M) ∧
        Integrable (fun z : Vector N×Vector N =>
          (tiltDefect (fun y : Vector N×Vector N => β*(sourceSmoothCutoffField μ Q hQ hnp J y.1 e k α χ y.2-
            fieldOfMixture μ J y.2)) z)^2 *
            (∑ ij : Fin N×Fin N,
              (GF ij ((J,(z.1,(e,k))),z.2))^2 /
                F ((J,(z.1,(e,k))),z.2)))
          (normalizedTilt ((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture μ J)))
            (fun z : Vector N×Vector N => β*(sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2-
              fieldOfMixture μ J z.2)) M) := by
  dsimp only
  obtain ⟨F,GF,U,G,hF,hGF,hU,hG,hFf,hGFf,hBm,hAm,hKm,hRm,hCm,hJm,hE,hBi⟩ :=
    sourceJointReferenceSignedReducedEnergy_globalGradientIntegrable hN μ hnp Q hQ hQ1
      α hα χ hχ β hβ θ hθ J hJ e k hbar kbar B R hh hk hB hR hχB hχR M hM
  let : IsProbabilityMeasure (sphereLaw N) := sphereLaw_probability N
  obtain ⟨v₀,hv₀s⟩ := (sphereLaw_support hN).exists
  have hv₀ : OnSphere v₀ := (onSphere_iff_norm_sq v₀).mpr hv₀s
  let p₀ : SourceParameters N μ := (J,(v₀,(e,k)))
  let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p₀ hv₀
  obtain ⟨hFs,hUs,hFb,hUb,hFisher,hEnergy,hGraph⟩ := hE p₀ hv₀ hJ
  obtain ⟨F₀,F₁,u,hF₀,hu,hFF₀,hGF₀,hFF₁,hGF₁,hUv,hGv⟩ := hGraph
  let H₀ := fieldOfMixture μ J
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff μ J).continuous
  obtain ⟨F₀',hFval,hFgrad⟩ := sphericalSobolevGraph_changeGibbs hN β β
    D.baseData.hamiltonian H₀ D.baseData.hamiltonian_contDiff.continuous hH₀ F₀
  have hπ : gibbsLaw N β D.baseData.hamiltonian = gibbsLaw N β H₀ := by
    rw [D.baseData_hamiltonian]
    rfl
  have hAC : ae (gibbsLaw N β D.baseData.hamiltonian) ≤
      ae (gibbsLaw N β D.hamiltonian) :=
    (gibbsLaw_absolutelyContinuous_gibbsLaw hN β β D.hamiltonian
      D.baseData.hamiltonian D.hamiltonian_contDiff.continuous).ae_le
  have hFb₀ : ∀ᵐ x ∂gibbsLaw N β H₀, 1 ≤ F (p₀,x) := by
    simpa only [hπ] using (hFb.filter_mono hAC).mono (fun _ hx => hx.1)
  have hFF₀' : (fun x => F (p₀,x)) =ᵐ[gibbsLaw N β H₀] F₀.val.fst := by
    have hD : (fun x => F (p₀,x)) =ᵐ[gibbsLaw N β D.baseData.hamiltonian]
        F₀.val.fst := hFF₀
    simpa only [hπ] using hD
  have hFlo : ∀ᵐ x ∂gibbsLaw N β H₀, 1 ≤ F₀'.val.fst x := by
    filter_upwards [hFb₀,hFF₀',hFval] with x hb hff hf
    rw [hff] at hb
    rw [hf]
    exact hb
  have hFrep : (fun x => F ((J,(v₀,(e,k))),x)) =ᵐ[
      gibbsLaw N β H₀] F₀'.val.fst := hFF₀'.trans hFval.symm
  have hGFrep (ij : Fin N×Fin N) :
      (fun x => GF ij ((J,(v₀,(e,k))),x)) =ᵐ[
        gibbsLaw N β H₀] F₀'.val.snd ij := by
    have hgf : (fun x => GF ij (p₀,x)) =ᵐ[gibbsLaw N β H₀] F₀.val.snd ij := by
      have hD : (fun x => GF ij (p₀,x)) =ᵐ[gibbsLaw N β D.baseData.hamiltonian]
          F₀.val.snd ij := hGF₀ ij
      simpa only [hπ] using hD
    exact hgf.trans (hFgrad ij).symm
  obtain ⟨hKi,hJi⟩ := source_frozen_reference_defect_moments_integrable
    hN μ hnp Q hQ α χ hχ.continuous β J e k F GF hFf hGFf
      F₀' v₀ hFrep hGFrep hFlo M hM
  exact ⟨F,GF,U,G,hF,hGF,hU,hG,hFf,hGFf,hBm,hAm,hKm,hRm,hCm,hJm,hE,hBi,hKi,hJi⟩

end SlowEquilibration.ConditionedEntrance

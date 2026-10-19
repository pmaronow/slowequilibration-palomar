-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourcePhysicalGraphRawPairWitness
public import SlowEquilibration.ConditionedEntranceSourceJointPairFibre
public import SlowEquilibration.ConditionedEntranceSourceJointPairIntegrability
public import SlowEquilibration.ConditionedEntranceAxisMomentEnergyAbsorption

/-! The exact globally averaged source-pairing identity for the actual
mixed source and its physical killed resolvent. All four terms are L¹
for the same joint representatives used by the weighted-energy argument. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace BigOperators
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SmoothKilled
open SphericalAging.HardSphereDynamics
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem source_joint_positive_pair_absorbed_global_witness
    {N : ℕ} (hN : 1≤N) (μ : FiniteMixture)
    (hnp : μ.minDegree<μ.maxDegree) (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≤1)
    (α : ℝ) (hα : 0<α) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (hβ : 0≤β) (θ : ℝ≥0) (hθ : 0<θ)
    (J : Disorder N μ.maxDegree) (hJ : J∈regularDisorder)
    (e k hbar kbar B R : ℝ) (hh : |e|≤hbar) (hk : |k|≤kbar)
    (hB : 0≤B) (hR : 0≤R)
    (hχB : ∀ s, |χ s|≤B) (hχR : ∀ s, R < |s| → χ s=0)
    (M : ℝ) (hM : 1/2≤M)
    (hMphys : M=∫ z : Vector N×Vector N,
      Real.exp (β*(sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2-
        fieldOfMixture μ J z.2))
        ∂((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture μ J))))
    (ε : ℝ) (hε : 0≤ε)
    (hεaxis : ∀ᵐ x ∂gibbsLaw N β (fieldOfMixture μ J),
      (∫ v, Real.exp (β*(sourceSmoothCutoffField μ Q hQ hnp
          J v e k α χ x-fieldOfMixture μ J x))*
        (tiltDefect (fun z : Vector N×Vector N =>
          β*(sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2-
            fieldOfMixture μ J z.2)) (v,x))^2
        ∂sphereLaw N) ≤ ε) :
    let H₀ := fieldOfMixture μ J
    let w : Vector N×Vector N→ℝ := fun z =>
      β*(sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2-H₀ z.2)
    let ν := normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M
    let Hf := 2*Real.log 2+
      4*β*derivativeConstant (mixtureCoefficients μ)*(N : ℝ)
    ∃ F : SourceParameters N μ×Vector N→ℝ,
    ∃ GF : (Fin N×Fin N)→SourceParameters N μ×Vector N→ℝ,
    ∃ U : SourceParameters N μ×Vector N→ℝ,
    ∃ G : (Fin N×Fin N)→SourceParameters N μ×Vector N→ℝ,
    ∃ F₀ : sphericalSobolevGraph hN β H₀
      (fieldOfMixture_contDiff μ J).continuous,
      let Fa : Vector N×Vector N→ℝ := fun z => F ((J,(z.1,(e,k))),z.2)
      let Ua : Vector N×Vector N→ℝ := fun z => U ((J,(z.1,(e,k))),z.2)
      let GFa : (Fin N×Fin N)→Vector N×Vector N→ℝ := fun ij z =>
        GF ij ((J,(z.1,(e,k))),z.2)
      let Ga : (Fin N×Fin N)→Vector N×Vector N→ℝ := fun ij z =>
        G ij ((J,(z.1,(e,k))),z.2)
      let I : Vector N×Vector N→ℝ := fun z =>
        1+uniformInitialDensity N β H₀ z.2
      StronglyMeasurable F ∧ (∀ ij,StronglyMeasurable (GF ij)) ∧
      StronglyMeasurable U ∧ (∀ ij,StronglyMeasurable (G ij)) ∧
      (fun x => F ((J,((0 : Vector N),(e,k))),x)) =ᵐ[
        gibbsLaw N β H₀] F₀.val.fst ∧
      (∀ ij : Fin N×Fin N,
        (fun x => GF ij ((J,((0 : Vector N),(e,k))),x)) =ᵐ[
          gibbsLaw N β H₀] F₀.val.snd ij) ∧
      (∀ᵐ x ∂gibbsLaw N β H₀,1≤F₀.val.fst x) ∧
      (∫ x,F ((J,((0 : Vector N),(e,k))),x) ∂gibbsLaw N β H₀)=2 ∧
      sphericalFisher hN β H₀ (fieldOfMixture_contDiff μ J).continuous F₀ ≤
        (θ : ℝ)*Hf ∧
      (∀ u v x,Fa (u,x)=Fa (v,x)) ∧
      (∀ ij u v x,GFa ij (u,x)=GFa ij (v,x)) ∧
      (∀ᵐ z ∂ν,1≤Fa z ∧ 0≤Ua z ∧ Ua z≤1) ∧
      (∀ v : Vector N,∀ hv : OnSphere v,
        let p : SourceParameters N μ := (J,(v,(e,k)))
        let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1
          α hα χ hχ p hv
        ((fun x => F (p,x))=ᵐ[gibbsLaw N β D.hamiltonian]
          referenceRate D.baseData β θ (referenceInitialVector D.baseData β)) ∧
        ((fun x => U (p,x))=ᵐ[gibbsLaw N β D.hamiltonian]
          rateLaplace D β (PhysicalHitting.capKilling α v)
            (PhysicalHitting.capKilling_contDiff α v).continuous
            (PhysicalHitting.capKilling_nonneg α v) θ
            (killingVector D β (PhysicalHitting.capKilling α v)
              (PhysicalHitting.capKilling_contDiff α v).continuous))) ∧
      Integrable (fun z => Fa z*(∑ ij : Fin N×Fin N,(Ga ij z)^2)) ν ∧
      Integrable (fun z => (tiltDefect w z)^2*
        (∑ ij : Fin N×Fin N,(GFa ij z)^2/Fa z)) ν ∧
      Integrable (fun z => I z*Ua z) ν ∧
      Integrable (fun z => PhysicalHitting.capKilling α z.1 z.2*Fa z*(1-Ua z)) ν ∧
      Integrable (fun z => tiltDefect w z*(I z-Fa z)*Ua z) ν ∧
      Integrable (fun z => tiltDefect w z*
        (∑ ij : Fin N×Fin N,GFa ij z*Ga ij z)) ν ∧
      ((θ : ℝ)*(∫ z,I z*Ua z ∂ν)=
        (∫ z,PhysicalHitting.capKilling α z.1 z.2*Fa z*(1-Ua z) ∂ν)+
        (θ : ℝ)*(∫ z,tiltDefect w z*(I z-Fa z)*Ua z ∂ν)-
        (∫ z,tiltDefect w z*
          (∑ ij : Fin N×Fin N,GFa ij z*Ga ij z) ∂ν)) ∧
      (∫ z,Fa z*(∑ ij : Fin N×Fin N,(Ga ij z)^2) ∂ν)/(θ : ℝ) ≤
        2*((∫ z,PhysicalHitting.capKilling α z.1 z.2*Fa z ∂ν)/(θ : ℝ))+
        ε+2*ε*Hf := by
  dsimp only
  have hMpos : 0<M := by linarith
  obtain ⟨F,GF,U,G,F₀,hFrep,hGFrep,hF₀lo,hFmass,hJF,hPhysical,hPairGraph,
    hPhysBound,hF,hGF,hU,hG,hFf,hGFf,hglobal,hBi,hKi,hJi,hAi,hRi,hKsi,hCsi,hraw⟩ :=
    source_joint_signed_global_raw_energy_physical_graph_pair_witness
      hN μ hnp Q hQ hQ1 α hα χ hχ β hβ θ hθ J hJ
      e k hbar kbar B R hh hk hB hR hχB hχR M hMpos hMphys
  let H₀ := fieldOfMixture μ J
  let H : Vector N→Vector N→ℝ := fun v x =>
    sourceSmoothCutoffField μ Q hQ hnp J v e k α χ x
  let w : Vector N×Vector N→ℝ := fun z => β*(H z.1 z.2-H₀ z.2)
  let ν := normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M
  let Hf := 2*Real.log 2+
    4*β*derivativeConstant (mixtureCoefficients μ)*(N : ℝ)
  let Fa : Vector N×Vector N→ℝ := fun z => F ((J,(z.1,(e,k))),z.2)
  let Ua : Vector N×Vector N→ℝ := fun z => U ((J,(z.1,(e,k))),z.2)
  let GFa : (Fin N×Fin N)→Vector N×Vector N→ℝ := fun ij z =>
    GF ij ((J,(z.1,(e,k))),z.2)
  let Ga : (Fin N×Fin N)→Vector N×Vector N→ℝ := fun ij z =>
    G ij ((J,(z.1,(e,k))),z.2)
  let I : Vector N×Vector N→ℝ := fun z =>
    1+uniformInitialDensity N β H₀ z.2
  obtain ⟨hIi,hRUi,hDUi,hCi⟩ :=
    source_joint_positive_pair_four_integrable hN μ hnp Q hQ α χ hχ
      β hβ J hJ e k M hMpos hMphys F U GF G hF hU hGF hG
      hPhysBound hRi hJi hBi
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff μ J).continuous
  have hH : Continuous (fun z : Vector N×Vector N => H z.1 z.2) :=
    (sourceSmoothCutoffField_jointContinuous μ Q hQ hnp α χ hχ.continuous).comp
      (show Continuous (fun z : Vector N×Vector N =>
        (((J,(z.1,(e,k))),z.2) : SourceParameters N μ×Vector N)) by fun_prop)
  have hw : Continuous w := (hH.sub (hH₀.comp continuous_snd)).const_mul β
  let fI : Vector N×Vector N→ℝ := fun z => I z*Ua z
  let fR : Vector N×Vector N→ℝ := fun z =>
    PhysicalHitting.capKilling α z.1 z.2*Fa z*(1-Ua z)
  let fD : Vector N×Vector N→ℝ := fun z =>
    tiltDefect w z*(I z-Fa z)*Ua z
  let fC : Vector N×Vector N→ℝ := fun z =>
    tiltDefect w z*(∑ ij : Fin N×Fin N,GFa ij z*Ga ij z)
  have hpoint (v : Vector N) (hv : OnSphere v) :
      (θ : ℝ)*(∫ x,fI (v,x) ∂gibbsLaw N β (H v))=
        (∫ x,fR (v,x) ∂gibbsLaw N β (H v))+
        (θ : ℝ)*(∫ x,fD (v,x) ∂gibbsLaw N β (H v))-
        (∫ x,fC (v,x) ∂gibbsLaw N β (H v)) := by
    let p : SourceParameters N μ := (J,(v,(e,k)))
    let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1
      α hα χ hχ p hv
    let κ := PhysicalHitting.capKilling α v
    have hκ := (PhysicalHitting.capKilling_contDiff α v).continuous
    have hκ0 := PhysicalHitting.capKilling_nonneg α v
    have hκ1 : ∀ x,‖κ x‖≤(1 : ℝ≥0) := by
      intro x
      rw [Real.norm_eq_abs,abs_of_nonneg (hκ0 x)]
      exact PhysicalHitting.capKilling_le_one hα v x
    obtain ⟨hFs,_hUs⟩ := hPhysical v hv
    obtain ⟨Fb,u,hFb,hu,_hFFb,hGFb,hUv,hGv⟩ := hPairGraph v hv
    have hAC := (gibbsLaw_absolutelyContinuous_gibbsLaw hN β β
      D.baseData.hamiltonian D.hamiltonian
      D.baseData.hamiltonian_contDiff.continuous).ae_le
    have hGFπ (ij : Fin N×Fin N) :
        (fun x => GF ij (p,x))=ᵐ[gibbsLaw N β D.hamiltonian]
          Fb.val.snd ij := (hGFb ij).filter_mono hAC
    have hreg : D.disorder∈regularDisorder := by
      change p.1∈regularDisorder
      exact hJ
    have hp := rateLaplace_reference_positive_source_identity_representatives
      D β hβ κ hκ hκ0 1 hκ1 θ hθ hreg
      (fun x => F (p,x)) (fun x => U (p,x))
      (fun ij x => GF ij (p,x)) (fun ij x => G ij (p,x))
      Fb u hFb hu hFs hUv hGFπ hGv
    have hDham : D.hamiltonian=H v := rfl
    have hDbase : D.baseData.hamiltonian=H₀ :=
      SourceData.baseData_hamiltonian D
    have hweq (x : Vector N) :
        gibbsEnergyDifference β β D.baseData.hamiltonian D.hamiltonian x=
          w (v,x) := by
      change β*D.hamiltonian x-β*D.baseData.hamiltonian x=
        β*(H v x-H₀ x)
      rw [hDham,hDbase]
      ring
    have hkeq (x : Vector N) :
        tiltDefect (gibbsEnergyDifference β β D.baseData.hamiltonian
          D.hamiltonian) x=tiltDefect w (v,x) := by
      unfold tiltDefect
      rw [hweq]
    have hkeq' (x : Vector N) :
        tiltDefect (gibbsEnergyDifference β β H₀ (H v)) x=
          tiltDefect w (v,x) := by
      simpa only [hDham,hDbase] using hkeq x
    rw [hDham,hDbase] at hp
    simpa only [fI,fR,fD,fC,I,Fa,Ua,GFa,Ga,κ,p,H,H₀,w,hkeq'] using hp
  have hM' : 0<∫ z : Vector N×Vector N,
      Real.exp (β*(H z.1 z.2-H₀ z.2))
        ∂((sphereLaw N).prod (gibbsLaw N β H₀)) := by
    simpa only [H,H₀] using hMphys ▸ hMpos
  have hIi' : Integrable fI (normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H₀)) w
      (∫ z, Real.exp (w z) ∂((sphereLaw N).prod (gibbsLaw N β H₀)))) := by
    simpa only [fI,ν,w,H,H₀,← hMphys] using hIi
  have hRUi' : Integrable fR (normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H₀)) w
      (∫ z, Real.exp (w z) ∂((sphereLaw N).prod (gibbsLaw N β H₀)))) := by
    simpa only [fR,ν,w,H,H₀,← hMphys] using hRUi
  have hDUi' : Integrable fD (normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H₀)) w
      (∫ z, Real.exp (w z) ∂((sphereLaw N).prod (gibbsLaw N β H₀)))) := by
    simpa only [fD,ν,w,H,H₀,← hMphys] using hDUi
  have hCi' : Integrable fC (normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H₀)) w
      (∫ z, Real.exp (w z) ∂((sphereLaw N).prod (gibbsLaw N β H₀)))) := by
    simpa only [fC,ν,w,H,H₀,← hMphys] using hCi
  have hPairGlobal := axisGibbs_source_pair_global hN β H₀ hH₀ H hH
    fI fR fD fC (θ : ℝ) hM' hIi' hRUi' hDUi' hCi' hpoint
  have hpair : Measurable (fun z : Vector N×Vector N =>
      (((J,(z.1,(e,k))),z.2) : SourceParameters N μ×Vector N)) := by fun_prop
  have hFm : Measurable Fa := (hF.comp_measurable hpair).measurable
  have hUm : Measurable Ua := (hU.comp_measurable hpair).measurable
  have hGFm (ij : Fin N×Fin N) : Measurable (GFa ij) :=
    ((hGF ij).comp_measurable hpair).measurable
  have hGm (ij : Fin N×Fin N) : Measurable (Ga ij) :=
    ((hG ij).comp_measurable hpair).measurable
  have hFrozenF (u v x : Vector N) : Fa (u,x)=Fa (v,x) :=
    hFf (J,(u,(e,k))) (J,(v,(e,k))) x rfl
  have hFrozenGF (ij : Fin N×Fin N) (u v x : Vector N) :
      GFa ij (u,x)=GFa ij (v,x) :=
    hGFf ij (J,(u,(e,k))) (J,(v,(e,k))) x rfl
  have hFlo : ∀ᵐ z ∂ν,1≤Fa z := hglobal.mono (fun _ hz => hz.1)
  have hUb : ∀ᵐ z ∂ν,0≤Ua z ∧ Ua z≤1 :=
    hglobal.mono (fun _ hz => hz.2)
  have hθpos : 0<(θ : ℝ) := by exact_mod_cast hθ
  have hJFpos : 0 ≤ sphericalFisher hN β H₀ hH₀ F₀ :=
    sphericalFisher_nonnegative hN β H₀ hH₀ F₀ hF₀lo
  have hHf : 0≤Hf := by
    dsimp only [Hf] at *
    nlinarith [hJF]
  let Rrate := (∫ z,PhysicalHitting.capKilling α z.1 z.2*Fa z ∂ν)/(θ : ℝ)
  have hRident : (θ : ℝ)*Rrate =
      ∫ z,PhysicalHitting.capKilling α z.1 z.2*Fa z ∂ν := by
    exact mul_div_cancel₀ _ hθpos.ne'
  have hraw' :
      (∫ z,Fa z*(∑ ij : Fin N×Fin N,(Ga ij z)^2) ∂ν)+
        (θ : ℝ)/2*(∫ z,Fa z*Ua z^2 ∂ν) ≤
        (θ : ℝ)*Rrate+
        (θ : ℝ)/2*|∫ z,tiltDefect w z*(Fa z-1)*Ua z^2 ∂ν|+
        |∫ z,tiltDefect w z*Ua z*
          (∑ ij : Fin N×Fin N,GFa ij z*Ga ij z) ∂ν| := by
    rw [hRident]
    exact hraw
  have hAbs := axisGibbs_weighted_energy_absorption_of_second_moment
    hN β H₀ hH₀ w hw M hM Fa Ua GFa Ga hFm hUm hGFm hGm
    hFrozenF hFrozenGF F₀ hFrep hGFrep hF₀lo hFmass
    ν rfl hFlo hUb hKi hJi hAi hBi
    (θ : ℝ) ε Hf Rrate hθpos hε hHf hεaxis hJF hraw'
  refine ⟨F,GF,U,G,F₀,hF,hGF,hU,hG,hFrep,hGFrep,hF₀lo,hFmass,hJF,
    hFrozenF,hFrozenGF,hglobal,hPhysical,?_,?_,hIi,hRUi,hDUi,hCi,?_,?_⟩
  · simpa only [Fa,Ga,ν,w,H,H₀] using hBi
  · simpa only [Fa,GFa,ν,w,H,H₀] using hJi
  · simpa only [fI,fR,fD,fC,I,Fa,Ua,GFa,Ga,ν,w,H,H₀,← hMphys] using hPairGlobal
  · simpa only [Fa,Ga,ν,w,H,H₀,Hf,Rrate] using hAbs

end SlowEquilibration.ConditionedEntrance

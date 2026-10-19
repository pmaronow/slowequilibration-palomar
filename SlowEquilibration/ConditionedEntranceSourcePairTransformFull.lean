-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourcePairTransformMeasurable
public import SlowEquilibration.ConditionedEntrancePositivePairDefectBound
public import SlowEquilibration.ConditionedEntrancePositivePairTransformNumeric
public import SlowEquilibration.ConditionedEntranceFisherDefectAnyRepresentatives
public import SlowEquilibration.ConditionedEntranceWeightedGradientDefectCauchy

/-! Quantitative source-pair transform with a measurable physical resolvent for the actual mixed-source
resolvent. All terms arise from one physical joint representative. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace BigOperators
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SmoothKilled
open SphericalAging.HardSphereDynamics
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem source_joint_positive_pair_transform_global_full_witness
    {N : ℕ} (hN : 1≤N) (μ : FiniteMixture)
    (hnp : μ.minDegree<μ.maxDegree) (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≤1)
    (α : ℝ) (hα : 0<α) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (hβ : 0≤β) (θ : ℝ≥0) (hθ : 0<θ)
    (J : Disorder N μ.maxDegree) (hJ : J∈regularDisorder)
    (e k hbar kbar B R : ℝ) (hh : |e|≤hbar) (hk : |k|≤kbar)
    (hB : 0≤B) (hR : 0≤R)
    (hχB : ∀ s, |χ s|≤B) (hχR : ∀ s, R < |s| → χ s=0)
    (M η ε : ℝ) (hM : 1/2≤M) (hη : 0≤η) (hηhalf : η≤1/2)
    (hMlower : 1-η≤M) (hε : 0≤ε)
    (hMphys : M=∫ z : Vector N×Vector N,
      Real.exp (β*(sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2-
        fieldOfMixture μ J z.2))
        ∂((sphereLaw N).prod (gibbsLaw N β (fieldOfMixture μ J))))
    (hAxisExp : ∀ᵐ x ∂gibbsLaw N β (fieldOfMixture μ J),
      (∫ v,Real.exp (β*(sourceSmoothCutoffField μ Q hQ hnp
        J v e k α χ x-fieldOfMixture μ J x)) ∂sphereLaw N)≤1+η)
    (hAxisDefect : ∀ᵐ x ∂gibbsLaw N β (fieldOfMixture μ J),
      (∫ v,Real.exp (β*(sourceSmoothCutoffField μ Q hQ hnp
        J v e k α χ x-fieldOfMixture μ J x))*
        (tiltDefect (fun z : Vector N×Vector N =>
          β*(sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2-
            fieldOfMixture μ J z.2)) (v,x))^2 ∂sphereLaw N)≤ε) :
    let H₀ := fieldOfMixture μ J
    let w : Vector N×Vector N→ℝ := fun z =>
      β*(sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2-H₀ z.2)
    let ν := normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M
    let Hf := 2*Real.log 2+
      4*β*derivativeConstant (mixtureCoefficients μ)*(N : ℝ)
    ∃ F : SourceParameters N μ×Vector N→ℝ,
    ∃ U : SourceParameters N μ×Vector N→ℝ,
      let Fa : Vector N×Vector N→ℝ := fun z => F ((J,(z.1,(e,k))),z.2)
      let Ua : Vector N×Vector N→ℝ := fun z => U ((J,(z.1,(e,k))),z.2)
      let I : Vector N×Vector N→ℝ := fun z =>
        1+uniformInitialDensity N β H₀ z.2
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
      StronglyMeasurable F ∧ StronglyMeasurable U ∧
      (∀ᵐ z ∂ν,1≤Fa z ∧ 0≤Ua z ∧ Ua z≤1) ∧
      (∀ u v x,Fa (u,x)=Fa (v,x)) ∧
      (∫ z,I z*Ua z ∂ν) ≤
        (∫ z,PhysicalHitting.capKilling α z.1 z.2*Fa z*(1-Ua z) ∂ν)/(θ : ℝ)+
        10*Real.sqrt ε+
        2*Real.sqrt (ε*Hf*
          ((∫ z,PhysicalHitting.capKilling α z.1 z.2*Fa z ∂ν)/(θ : ℝ)+
            ε*(1+Hf))) := by
  dsimp only
  obtain ⟨F,GF,U,G,F₀,hFsm,hGFsm,hUsm,hGsm,hFrep,hGFrep,hF₀lo,hFmass,hJF,
    hFrozenF,hFrozenGF,hglobal,hPhysical,hBi,hJi,hIi,hRUi,hDUi,hCi,hPair,hAbs⟩ :=
    source_joint_positive_pair_absorbed_global_witness hN μ hnp Q hQ hQ1
      α hα χ hχ β hβ θ hθ J hJ e k hbar kbar B R hh hk hB hR
      hχB hχR M hM hMphys ε hε hAxisDefect
  let H₀ := fieldOfMixture μ J
  let w : Vector N×Vector N→ℝ := fun z =>
    β*(sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2-H₀ z.2)
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
  let Benergy := ∫ z,Fa z*(∑ ij : Fin N×Fin N,(Ga ij z)^2) ∂ν
  let Jenergy := ∫ z,(tiltDefect w z)^2*
    (∑ ij : Fin N×Fin N,(GFa ij z)^2/Fa z) ∂ν
  let Rrate := (∫ z,PhysicalHitting.capKilling α z.1 z.2*Fa z ∂ν)/(θ : ℝ)
  let Kpair := ∫ z,PhysicalHitting.capKilling α z.1 z.2*Fa z*(1-Ua z) ∂ν
  let Dpair := ∫ z,tiltDefect w z*(I z-Fa z)*Ua z ∂ν
  let Cpair := ∫ z,tiltDefect w z*
    (∑ ij : Fin N×Fin N,GFa ij z*Ga ij z) ∂ν
  let Lpair := ∫ z,I z*Ua z ∂ν
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff μ J).continuous
  have hH : Continuous (fun z : Vector N×Vector N =>
      sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2) :=
    (sourceSmoothCutoffField_jointContinuous μ Q hQ hnp α χ hχ.continuous).comp
      (show Continuous (fun z : Vector N×Vector N =>
        (((J,(z.1,(e,k))),z.2) : SourceParameters N μ×Vector N)) by fun_prop)
  have hw : Continuous w := (hH.sub (hH₀.comp continuous_snd)).const_mul β
  have hpairmap : Measurable (fun z : Vector N×Vector N =>
      (((J,(z.1,(e,k))),z.2) : SourceParameters N μ×Vector N)) := by fun_prop
  have hFm : Measurable Fa := (hFsm.comp_measurable hpairmap).measurable
  have hUm : Measurable Ua := (hUsm.comp_measurable hpairmap).measurable
  have hGFm (ij : Fin N×Fin N) : Measurable (GFa ij) :=
    ((hGFsm ij).comp_measurable hpairmap).measurable
  have hGm (ij : Fin N×Fin N) : Measurable (Ga ij) :=
    ((hGsm ij).comp_measurable hpairmap).measurable
  have hFlo : ∀ᵐ z ∂ν,1≤Fa z := hglobal.mono (fun _ hz => hz.1)
  have hUb : ∀ᵐ z ∂ν,0≤Ua z ∧ Ua z≤1 :=
    hglobal.mono (fun _ hz => hz.2)
  have hθpos : 0<(θ : ℝ) := by exact_mod_cast hθ
  have hHf : 0≤Hf := by
    have hJFpos := sphericalFisher_nonnegative hN β H₀ hH₀ F₀ hF₀lo
    dsimp only [Hf] at *
    nlinarith [hJF]
  have hBpos : 0≤Benergy := by
    apply integral_nonneg_of_ae
    filter_upwards [hFlo] with z hz
    exact mul_nonneg (by linarith) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hJpos : 0≤Jenergy := by
    apply integral_nonneg_of_ae
    filter_upwards [hFlo] with z hz
    exact mul_nonneg (sq_nonneg _)
      (Finset.sum_nonneg fun ij _ => div_nonneg (sq_nonneg _) (by linarith))
  have hRpos : 0≤Rrate := by
    dsimp only [Rrate]
    apply div_nonneg _ hθpos.le
    apply integral_nonneg_of_ae
    filter_upwards [hFlo] with z hz
    exact mul_nonneg (PhysicalHitting.capKilling_nonneg α z.1 z.2) (by linarith)
  have hD := positive_pair_defect_le_ten_sqrt_of_axis_moments
    hN β H₀ hH₀ w hw M η ε hη hηhalf hMlower hM hε
    hAxisExp hAxisDefect Fa Ua hFm hUm hFrozenF F₀
    hFrep hF₀lo hFmass hFlo hUb
  have hkm : Measurable (tiltDefect w) := by unfold tiltDefect; fun_prop
  have hCross₀ := weighted_gradient_defect_cauchy ν (tiltDefect w)
    Fa (fun _ => 1) GFa Ga hkm hFm measurable_const hGFm hGm
    hFlo (.of_forall (fun _ => by norm_num)) hJi hBi
  have hCross : |Cpair|≤Real.sqrt (Jenergy*Benergy) := by
    simpa only [Cpair,Jenergy,Benergy,one_mul,mul_one] using hCross₀
  have hJproj := fisher_defect_projection_any_frozen_representatives
    hN β H₀ hH₀ w hw M hM Fa GFa hFrozenF hFrozenGF F₀
    hFrep hGFrep hF₀lo hε hAxisDefect
  have hJsmall : Jenergy≤2*ε*(θ : ℝ)*Hf := by
    have hh := mul_le_mul_of_nonneg_left hJF (by positivity : 0≤2*ε)
    dsimp only [Jenergy,Hf] at *
    nlinarith [hJproj,hh]
  have hTransform := positive_pair_transform_of_absorbed_energy
    hθpos hBpos hJpos hε hHf hRpos hPair hD hCross hJsmall hAbs
  exact ⟨F,U,hPhysical,hFsm,hUsm,hglobal,hFrozenF,by
    simpa only [Lpair,Kpair,Rrate,I,Fa,Ua,ν,H₀,w,Hf] using hTransform⟩

end SlowEquilibration.ConditionedEntrance

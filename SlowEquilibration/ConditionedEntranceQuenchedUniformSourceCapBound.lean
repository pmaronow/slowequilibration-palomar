-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceQuenchedUniformSourceFullTransform
public import SlowEquilibration.ConditionedEntranceSourcePairHazardComparison

/-! The literal uniform-start source resolvent transform uses the same
reference witness as the exponentially small physical cap hazard. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SphericalAging.HardSphereDynamics
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
open SmoothKilled
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_mixedSource_uniform_positive_pair_cap_eventually_le
    (μ : FiniteMixture) (hd : 4≤μ.minDegree)
    {Q B β : ℝ} (hQ : 0<Q) (hQ1 : Q≤1)
    (hnp : μ.minDegree<μ.maxDegree) (hB : 0≤B) (hβ : 0≤β)
    {α : ℝ} (hα : 0<α)
    (hαmoment : α≤EntranceLatitudeTangentObservable.sourceCutoffMomentScale μ Q B (2*β))
    (hαenergy : α≤1/(128*(1+β*
      PhysicalHitting.uniformCutoffEnergyConstant μ Q B B 1 2))) :
    ∃ Cε Cη Ccap : ℝ,0<Cε ∧ 0<Cη ∧ 0<Ccap ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) μ.maxDegree), J∈
        EntranceLatitudeTangentObservable.originalLatitudeMeanGood n μ →
      ∀ (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ),
        (∀ s,|χ s|≤1) → (∀ s,2 < |s| → χ s=0) →
      ∀ (e k : ℝ), |e|≤B → |k|≤B →
      ∀ (θ : ℝ≥0),0<θ →
      let H₀ := fieldOfMixture μ J
      let w : Vector (n+1)×Vector (n+1)→ℝ := fun z =>
        β*(sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2-H₀ z.2)
      let M := ∫ z,Real.exp (w z)
        ∂((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀))
      let ν := normalizedTilt ((sphereLaw (n+1)).prod
        (gibbsLaw (n+1) β H₀)) w M
      let ε := Cε*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ))
      let η := Cη*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)
      let Hf := 2*Real.log 2+
        4*β*derivativeConstant (mixtureCoefficients μ)*((n+1 : ℕ) : ℝ)
      ∃ F : SourceParameters (n+1) μ×Vector (n+1)→ℝ,
      ∃ U : SourceParameters (n+1) μ×Vector (n+1)→ℝ,
        let Fa : Vector (n+1)×Vector (n+1)→ℝ := fun z =>
          F ((J,(z.1,(e,k))),z.2)
        let Ua : Vector (n+1)×Vector (n+1)→ℝ := fun z =>
          U ((J,(z.1,(e,k))),z.2)
        (∀ v : Vector (n+1),∀ hv : OnSphere v,
          let p : SourceParameters (n+1) μ := (J,(v,(e,k)))
          let D := SourceData.atSourceParameters (by omega : 1≤n+1)
            μ hnp Q hQ hQ1 α hα χ hχ p hv
          ((fun x => F (p,x))=ᵐ[gibbsLaw (n+1) β D.hamiltonian]
            referenceRate D.baseData β θ (referenceInitialVector D.baseData β)) ∧
          ((fun x => U (p,x))=ᵐ[gibbsLaw (n+1) β D.hamiltonian]
            rateLaplace D β (PhysicalHitting.capKilling α v)
              (PhysicalHitting.capKilling_contDiff α v).continuous
              (PhysicalHitting.capKilling_nonneg α v) θ
              (killingVector D β (PhysicalHitting.capKilling α v)
                (PhysicalHitting.capKilling_contDiff α v).continuous))) ∧
        StronglyMeasurable F ∧ StronglyMeasurable U ∧
        (∀ᵐ z ∂ν,1≤Fa z ∧ 0≤Ua z ∧ Ua z≤1) ∧
        (∀ u v x,Fa (u,x)=Fa (v,x)) ∧
        let Rrate := (∫ z,PhysicalHitting.capKilling α z.1 z.2*Fa z ∂ν)/(θ : ℝ)
        ((∫ u, ∫ x, Ua (u,x) ∂sphereLaw (n+1) ∂sphereLaw (n+1)) ≤
          Rrate+10*Real.sqrt ε+
          2*Real.sqrt (ε*Hf*(Rrate+ε*(1+Hf)))+4*η) ∧
        Rrate≤4*Ccap*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/128)/(θ : ℝ) := by
  obtain ⟨Cε,Cη,hCε,hCη,hFull⟩ :=
    actual_mixedSource_uniform_positive_pair_transform_full_eventually_le
      μ hd hQ hQ1 hnp hB hβ
  obtain ⟨Ccap,hCcap,hCap⟩ :=
    quenchedMixedSource_reference_normalized_capKilling_mean_eventually_le
      μ hd hQ hQ1 hnp hB hβ hα hαmoment hαenergy
  obtain ⟨Cm,hCm,hMass⟩ :=
    actual_mixedSource_globalTilt_mass_close_one μ hd hQ hnp hB hβ
  have hSmall := sourceTilt_eta_eventually_half μ.minDegree hd Cm
  refine ⟨Cε,Cη,Ccap,hCε,hCη,hCcap,?_⟩
  filter_upwards [hFull,hCap,hMass,hSmall] with n hf hc hm hs
  intro J hJ χ hχ hχb hχR e k he hk θ hθ
  dsimp only
  obtain ⟨F,U,hPhysical,hFsm,hUsm,hBounds,hFrozen,hUniform⟩ :=
    hf J hJ α hα hαmoment χ hχ hχb hχR e k he hk θ hθ
  let H₀ := fieldOfMixture μ J
  let w : Vector (n+1)×Vector (n+1)→ℝ := fun z =>
    β*(sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2-H₀ z.2)
  let M := ∫ z,Real.exp (w z)
    ∂((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀))
  let ν := normalizedTilt ((sphereLaw (n+1)).prod
    (gibbsLaw (n+1) β H₀)) w M
  let Fa : Vector (n+1)×Vector (n+1)→ℝ := fun z =>
    F ((J,(z.1,(e,k))),z.2)
  let Ua : Vector (n+1)×Vector (n+1)→ℝ := fun z =>
    U ((J,(z.1,(e,k))),z.2)
  let κ : Vector (n+1)×Vector (n+1)→ℝ := fun z =>
    PhysicalHitting.capKilling α z.1 z.2
  have hN : 1≤n+1 := by omega
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff μ J).continuous
  have hH : Continuous (fun z : Vector (n+1)×Vector (n+1) =>
      sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2) :=
    (sourceSmoothCutoffField_jointContinuous μ Q hQ hnp α χ hχ.continuous).comp
      (show Continuous (fun z : Vector (n+1)×Vector (n+1) =>
        (((J,(z.1,(e,k))),z.2) : SourceParameters (n+1) μ×Vector (n+1))) by fun_prop)
  have hw : Continuous w := (hH.sub (hH₀.comp continuous_snd)).const_mul β
  have hMclose : |M-1|≤Cm*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) :=
    (hm J hJ α hα hαmoment χ hχ hχb hχR e k he hk).1
  have hMpos : 0<M := by
    have hl := (abs_le.mp hMclose).1
    linarith
  let : IsProbabilityMeasure (sphereLaw (n+1)) := sphereLaw_probability (n+1)
  obtain ⟨u₀,hu₀s⟩ := (sphereLaw_support hN).exists
  have hu₀ : OnSphere u₀ := (onSphere_iff_norm_sq u₀).mpr hu₀s
  let D₀ := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ
    (J,(u₀,(e,k))) hu₀
  have hAe : Fa=ᵐ[ν] (fun z => sourceReferencePositivePart D₀ β θ z.2) := by
    simpa only [Fa,ν,w,H₀,D₀] using
      source_joint_frozen_reference_ae_canonical hN μ hnp Q hQ hQ1
        α hα χ hχ β θ J e k M F hFsm hFrozen
        (fun v hv => (hPhysical v hv).1) u₀ hu₀
  have hDbase : D₀.baseData.hamiltonian=H₀ :=
    SourceData.baseData_hamiltonian D₀
  have hΓi : Integrable (sourceReferencePositivePart D₀ β θ)
      (gibbsLaw (n+1) β H₀) := by
    simpa only [hDbase] using sourceReferencePositivePart_integrable D₀ β θ
  obtain ⟨hRi,hReq⟩ := source_pair_cap_hazard_congr_of_ae hN β H₀ hH₀
    w hw M hMpos α (sourceReferencePositivePart D₀ β θ) hΓi Fa hAe
  have hHazCan := hc J hJ χ hχ hχb hχR e k he hk u₀ hu₀ θ hθ
  have hHazF : (∫ z,κ z*Fa z ∂ν)≤
      4*Ccap*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/128) := by
    rw [hReq]
    simpa only [κ,ν,w,M,H₀,D₀] using hHazCan
  have hKle : (∫ z,κ z*Fa z*(1-Ua z) ∂ν)≤
      (∫ z,κ z*Fa z ∂ν) :=
    source_pair_unresolved_hazard_le ν κ Fa Ua
      (fun z => PhysicalHitting.capKilling_nonneg α z.1 z.2)
      hRi (hBounds.mono (fun z hz => ⟨by linarith [hz.1],hz.2⟩))
  have hθpos : 0<(θ : ℝ) := by exact_mod_cast hθ
  have hKrate : (∫ z,κ z*Fa z*(1-Ua z) ∂ν)/(θ : ℝ)≤
      (∫ z,κ z*Fa z ∂ν)/(θ : ℝ) :=
    (div_le_div_iff_of_pos_right hθpos).2 hKle
  have hRrate : (∫ z,κ z*Fa z ∂ν)/(θ : ℝ)≤
      4*Ccap*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/128)/(θ : ℝ) :=
    (div_le_div_iff_of_pos_right hθpos).2 hHazF
  refine ⟨F,U,hPhysical,hFsm,hUsm,hBounds,hFrozen,?_⟩
  dsimp only at hUniform ⊢
  constructor
  · dsimp only [κ,Fa,Ua,ν,w,H₀,M] at hKrate
    linarith [hUniform]
  · simpa only [κ,Fa,ν,w,H₀,M] using hRrate

end SlowEquilibration.ConditionedEntrance

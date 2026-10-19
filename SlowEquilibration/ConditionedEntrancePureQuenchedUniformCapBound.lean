-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureQuenchedUniformFullTransform
public import SlowEquilibration.ConditionedEntranceSourcePairHazardComparison
public import SlowEquilibration.ConditionedEntrancePurePairSameReferenceHazard

/-! The literal uniform-start source resolvent transform uses the same
reference witness as the exponentially small physical cap hazard. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SphericalAging.HardSphereDynamics
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
open SmoothKilledGeneral
set_option autoImplicit false
set_option maxHeartbeats 1000000

set_option linter.unusedVariables false in
theorem actual_pureSource_uniform_positive_pair_cap_eventually_le
    (d : ℕ) (hd : 4 ≤ d) (c : ℝ) (hc : 0 < c)
    {Q B β : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) (hβ : 0 ≤ β)
    {α : ℝ} (hα : 0<α)
    (hαmoment : α≤EntranceLatitudeTangentObservable.sourceCutoffMomentScale (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) Q B (2*β))
    (hαenergy : α≤1/(128*(1+β*
      pureCutoffEnergyConstant d (by omega) c hc Q B))) :
    ∃ Cε Cη Ccap : ℝ,0<Cε ∧ 0<Cη ∧ 0<Ccap ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) (FiniteMixture.pure d (by omega : 2 ≤ d) c hc).maxDegree), J∈
        EntranceLatitudeTangentObservable.originalLatitudeMeanGood n (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) →
      ∀ (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ),
        (∀ s,|χ s|≤1) → (∀ s,2 < |s| → χ s=0) →
      ∀ (e : ℝ), |e|≤B →
      ∀ (θ : ℝ≥0),0<θ →
      let H₀ := fieldOfMixture (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) J
      let w : Vector (n+1)×Vector (n+1)→ℝ := fun z =>
        β*(pureSourceSmoothCutoffField d (by omega) c hc Q J z.1 e α χ z.2-H₀ z.2)
      let M := ∫ z,Real.exp (w z)
        ∂((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀))
      let ν := normalizedTilt ((sphereLaw (n+1)).prod
        (gibbsLaw (n+1) β H₀)) w M
      let ε := Cε*((n+1 : ℕ) : ℝ)^(2-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ))
      let η := Cη*((n+1 : ℕ) : ℝ)^(1-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ)/2)
      let Hf := 2*Real.log 2+
        4*β*derivativeConstant (mixtureCoefficients (FiniteMixture.pure d (by omega : 2 ≤ d) c hc))*((n+1 : ℕ) : ℝ)
      ∃ F : SourceParameters (n+1) (FiniteMixture.pure d (by omega : 2 ≤ d) c hc)×Vector (n+1)→ℝ,
      ∃ U : SourceParameters (n+1) (FiniteMixture.pure d (by omega : 2 ≤ d) c hc)×Vector (n+1)→ℝ,
        let Fa : Vector (n+1)×Vector (n+1)→ℝ := fun z =>
          F ((J,(z.1,(e,0))),z.2)
        let Ua : Vector (n+1)×Vector (n+1)→ℝ := fun z =>
          U ((J,(z.1,(e,0))),z.2)
        (∀ v : Vector (n+1),∀ hv : OnSphere v,
          let p : SourceParameters (n+1) (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) := (J,(v,(e,0)))
          let D := FieldData.ofPure (by omega : 1 ≤ n+1)
            d (by omega) c hc Q p.1 p.2.1 p.2.2.1 α χ hχ
          let Dbase := FieldData.ofOriginal (by omega : 1 ≤ n+1) (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) p.1
          ((fun x => F (p,x))=ᵐ[gibbsLaw (n+1) β D.hamiltonian]
            referenceRate Dbase β θ (referenceInitialVector Dbase β)) ∧
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
    actual_pureSource_uniform_positive_pair_transform_full_eventually_le
      d hd c hc hQ hB hβ
  obtain ⟨Ccap,hCcap,hCap⟩ :=
    quenchedPureSource_reference_normalized_capKilling_mean_eventually_le
      d hd c hc hQ hB hβ hα hαmoment hαenergy
  obtain ⟨Cm,hCm,hMass⟩ :=
    actual_pureSource_globalTilt_mass_close_one d hd c hc hQ hB hβ
  have hdμ : (FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree = d := (CSPureModels.pure_degrees d (by omega) c hc).1
  have hμd : 4 ≤ (FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree := by rw [hdμ]; exact hd
  have hSmall := sourceTilt_eta_eventually_half (FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree hμd Cm
  refine ⟨Cε,Cη,Ccap,hCε,hCη,hCcap,?_⟩
  filter_upwards [hFull,hCap,hMass,hSmall] with n hf hcap hm hs
  intro J hJ χ hχ hχb hχR e he θ hθ
  dsimp only
  obtain ⟨F,U,hPhysical,hFsm,hUsm,hBounds,hFrozen,hUniform⟩ :=
    hf J hJ α hα hαmoment χ hχ hχb hχR e he θ hθ
  let H₀ := fieldOfMixture (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) J
  let w : Vector (n+1)×Vector (n+1)→ℝ := fun z =>
    β*(pureSourceSmoothCutoffField d (by omega) c hc Q J z.1 e α χ z.2-H₀ z.2)
  let M := ∫ z,Real.exp (w z)
    ∂((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀))
  let ν := normalizedTilt ((sphereLaw (n+1)).prod
    (gibbsLaw (n+1) β H₀)) w M
  let Fa : Vector (n+1)×Vector (n+1)→ℝ := fun z =>
    F ((J,(z.1,(e,0))),z.2)
  let Ua : Vector (n+1)×Vector (n+1)→ℝ := fun z =>
    U ((J,(z.1,(e,0))),z.2)
  let κ : Vector (n+1)×Vector (n+1)→ℝ := fun z =>
    PhysicalHitting.capKilling α z.1 z.2
  have hN : 1≤n+1 := by omega
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) J).continuous
  have hH : Continuous (fun z : Vector (n+1)×Vector (n+1) =>
      pureSourceSmoothCutoffField d (by omega) c hc Q J z.1 e α χ z.2) :=
    (pure_axisJointHamiltonian_contDiff d (by omega) c hc Q α χ hχ J e).continuous
  have hw : Continuous w := (hH.sub (hH₀.comp continuous_snd)).const_mul β
  have hMclose : |M-1|≤Cm*((n+1 : ℕ) : ℝ)^(1-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ)/2) :=
    (hm J hJ α hα hαmoment χ hχ hχb hχR e he).1
  have hMpos : 0<M := by
    have hl := (abs_le.mp hMclose).1
    linarith
  let : IsProbabilityMeasure (sphereLaw (n+1)) := sphereLaw_probability (n+1)
  obtain ⟨u₀,hu₀s⟩ := (sphereLaw_support hN).exists
  have hu₀ : OnSphere u₀ := (onSphere_iff_norm_sq u₀).mpr hu₀s
  let D₀ := FieldData.ofOriginal hN (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) J
  have hAe : Fa=ᵐ[ν] (fun z => fieldReferencePositivePart D₀ β θ z.2) := by
    simpa only [Fa,ν,w,H₀,D₀] using
      pure_joint_frozen_reference_ae_canonical hN d (by omega) c hc Q
        α hα χ hχ β θ J e M F hFsm hFrozen
        (fun v hv => (hPhysical v hv).1) u₀ hu₀
  have hDbase : D₀.hamiltonian=H₀ :=
    rfl
  have hΓi : Integrable (fieldReferencePositivePart D₀ β θ)
      (gibbsLaw (n+1) β H₀) := by
    simpa only [hDbase] using fieldReferencePositivePart_integrable D₀ β θ
  obtain ⟨hRi,hReq⟩ := source_pair_cap_hazard_congr_of_ae hN β H₀ hH₀
    w hw M hMpos α (fieldReferencePositivePart D₀ β θ) hΓi Fa hAe
  have hHazCan := hcap J hJ χ hχ hχb hχR e he θ hθ
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

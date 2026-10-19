-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureQuenchedUniformCapBound
public import SlowEquilibration.ConditionedEntrancePositivePairFixedScaleNumeric

/-! At any reference rate above the reciprocal exponential horizon, the
literal uniform-start proper-pure source killed resolvent is polynomially plus
exponentially small on the original latitude-good event. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SphericalAging.HardSphereDynamics
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
open SmoothKilledGeneral
set_option autoImplicit false
set_option maxHeartbeats 900000

set_option linter.unusedVariables false in
theorem actual_pureSource_uniform_positive_pair_fixed_rate_eventually_le
    (d : ℕ) (hd : 4 ≤ d) (c : ℝ) (hc : 0 < c)
    {Q B β : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) (hβ : 0 ≤ β)
    {α : ℝ} (hα : 0<α)
    (hαmoment : α≤EntranceLatitudeTangentObservable.sourceCutoffMomentScale (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) Q B (2*β))
    (hαenergy : α≤1/(128*(1+β*
      pureCutoffEnergyConstant d (by omega) c hc Q B)))
    {γ : ℝ} (hγ : γ≤α^2/256) :
    ∃ Cε Cη Ccap : ℝ,0<Cε ∧ 0<Cη ∧ 0<Ccap ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) (FiniteMixture.pure d (by omega : 2 ≤ d) c hc).maxDegree), J∈
        EntranceLatitudeTangentObservable.originalLatitudeMeanGood n (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) →
      ∀ (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ),
        (∀ s,|χ s|≤1) → (∀ s,2 < |s| → χ s=0) →
      ∀ (e : ℝ), |e|≤B →
      ∀ (θ : ℝ≥0),0<θ →
        Real.exp (-γ*((n+1 : ℕ) : ℝ))≤(θ : ℝ) →
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
        (∫ u, ∫ x, Ua (u,x) ∂sphereLaw (n+1) ∂sphereLaw (n+1))≤
          4*η+10*Real.sqrt ε+3*ε*(1+Hf)+
            8*Ccap*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/256) := by
  obtain ⟨Cε,Cη,Ccap,hCε,hCη,hCcap,hCap⟩ :=
    actual_pureSource_uniform_positive_pair_cap_eventually_le
      d hd c hc hQ hB hβ hα hαmoment hαenergy
  refine ⟨Cε,Cη,Ccap,hCε,hCη,hCcap,?_⟩
  filter_upwards [hCap] with n hn
  intro J hJ χ hχ hχb hχR e he θ hθ hrate
  dsimp only
  obtain ⟨F,U,hPhysical,hFsm,hUsm,hBounds,hFrozen,hPair,hRcap⟩ :=
    hn J hJ χ hχ hχb hχR e he θ hθ
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
  let ε := Cε*((n+1 : ℕ) : ℝ)^(2-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ))
  let η := Cη*((n+1 : ℕ) : ℝ)^(1-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ)/2)
  let Hf := 2*Real.log 2+
    4*β*derivativeConstant (mixtureCoefficients (FiniteMixture.pure d (by omega : 2 ≤ d) c hc))*((n+1 : ℕ) : ℝ)
  let Rrate := (∫ z,PhysicalHitting.capKilling α z.1 z.2*Fa z ∂ν)/(θ : ℝ)
  have hθreal : 0<(θ : ℝ) := by exact_mod_cast hθ
  have hε : 0≤ε := by dsimp only [ε]; positivity
  have hHf : 0≤Hf := by
    have hdpos := (derivativeConstant_pos (mixtureCoefficients (FiniteMixture.pure d (by omega : 2 ≤ d) c hc))).le
    have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
    dsimp only [Hf]
    positivity
  have hRrate : 0≤Rrate := by
    dsimp only [Rrate]
    apply div_nonneg _ hθreal.le
    apply integral_nonneg_of_ae
    filter_upwards [hBounds] with z hz
    exact mul_nonneg (PhysicalHitting.capKilling_nonneg α z.1 z.2)
      (by linarith [hz.1])
  have hNreal : 0≤((n+1 : ℕ) : ℝ) := by positivity
  have hSimple := positive_pair_cap_horizon_bound hNreal hCcap.le hγ
    hθreal hrate hε hHf hRrate hPair hRcap
  exact ⟨F,U,hPhysical,hFsm,hUsm,hBounds,hFrozen,by
    simpa only [Rrate,Hf,η,ε,Ua,Fa,ν,w,H₀,M] using hSimple⟩

end SlowEquilibration.ConditionedEntrance

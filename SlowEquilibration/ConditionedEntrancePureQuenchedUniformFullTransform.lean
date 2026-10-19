-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureQuenchedPairTransformFull
public import SlowEquilibration.ConditionedEntrancePureUniformResolventTransferAny
public import SlowEquilibration.ConditionedEntranceFrozenTiltIntegrability

/-! The physical source-pair transform is combined with the actual uniform
initial law using exactly the same measurable killed resolvent. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SphericalAging.HardSphereDynamics
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
open SmoothKilledGeneral
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem pair_exp_integrable_uniform {N : ℕ} (hN : 1≤N)
    (β : ℝ) (H : Vector N→ℝ) (hH : Continuous H)
    {f : Vector N×Vector N→ℝ} (hf : Continuous f) :
    Integrable f ((sphereLaw N).prod (gibbsLaw N β H)) := by
  let : IsProbabilityMeasure (sphereLaw N) := sphereLaw_probability N
  let : IsProbabilityMeasure (gibbsLaw N β H) := gibbsLaw_probability hN β hH
  have hs : ∀ᵐ z : Vector N×Vector N ∂(sphereLaw N).prod (gibbsLaw N β H),
      ‖z.1‖^2=(N : ℝ) ∧ ‖z.2‖^2=(N : ℝ) := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [sphereLaw_support hN] with u hu
    filter_upwards [gibbsLaw_support hN β H] with x hx
    exact ⟨hu,hx⟩
  obtain ⟨C,hC⟩ := ((isCompact_closedBall (0 : Vector N) (Real.sqrt N)).prod
    (isCompact_closedBall (0 : Vector N) (Real.sqrt N))).exists_bound_of_continuousOn
      hf.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [hs] with z hz
  apply hC
  constructor
  · simp only [mem_closedBall,dist_zero_right]
    rw [← hz.1,Real.sqrt_sq (norm_nonneg z.1)]
  · simp only [mem_closedBall,dist_zero_right]
    rw [← hz.2,Real.sqrt_sq (norm_nonneg z.2)]

private theorem inv_gibbsDensity_eq_uniformInitialDensity
    {N : ℕ} (β : ℝ) (H : Vector N→ℝ) (x : Vector N) :
    (gibbsDensity N β H x)⁻¹=uniformInitialDensity N β H x := by
  unfold gibbsDensity uniformInitialDensity
  rw [inv_div,div_eq_mul_inv,← Real.exp_neg]
  congr 1
  ring_nf

set_option linter.unusedVariables false in
theorem actual_pureSource_uniform_positive_pair_transform_full_eventually_le
    (d : ℕ) (hd : 4 ≤ d) (c : ℝ) (hc : 0 < c)
    {Q B β : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) (hβ : 0 ≤ β) :
    ∃ Cε Cη : ℝ,0<Cε ∧ 0<Cη ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) (FiniteMixture.pure d (by omega : 2 ≤ d) c hc).maxDegree), J∈
        EntranceLatitudeTangentObservable.originalLatitudeMeanGood n (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) →
      ∀ (α : ℝ) (hα : 0<α),
        α≤EntranceLatitudeTangentObservable.sourceCutoffMomentScale (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) Q B (2*β) →
      ∀ (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ),
        (∀ s,|χ s|≤1) → (∀ s,2 < |s| → χ s=0) →
      ∀ (e : ℝ), |e| ≤ B →
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
          let D₀ := FieldData.ofOriginal (by omega : 1 ≤ n+1) (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) p.1
          ((fun x => F (p,x))=ᵐ[gibbsLaw (n+1) β D.hamiltonian]
            referenceRate D₀ β θ (referenceInitialVector D₀ β)) ∧
          ((fun x => U (p,x))=ᵐ[gibbsLaw (n+1) β D.hamiltonian]
            rateLaplace D β (PhysicalHitting.capKilling α v)
              (PhysicalHitting.capKilling_contDiff α v).continuous
              (PhysicalHitting.capKilling_nonneg α v) θ
              (killingVector D β (PhysicalHitting.capKilling α v)
                (PhysicalHitting.capKilling_contDiff α v).continuous))) ∧
        StronglyMeasurable F ∧ StronglyMeasurable U ∧
        (∀ᵐ z ∂ν,1≤Fa z ∧ 0≤Ua z ∧ Ua z≤1) ∧
        (∀ u v x,Fa (u,x)=Fa (v,x)) ∧
        (∫ u, ∫ x, Ua (u,x) ∂sphereLaw (n+1) ∂sphereLaw (n+1)) ≤
          (∫ z,PhysicalHitting.capKilling α z.1 z.2*Fa z*(1-Ua z) ∂ν)/(θ : ℝ)+
          10*Real.sqrt ε+
          2*Real.sqrt (ε*Hf*
            ((∫ z,PhysicalHitting.capKilling α z.1 z.2*Fa z ∂ν)/(θ : ℝ)+
              ε*(1+Hf)))+4*η := by
  obtain ⟨Cε,hCε,hSource⟩ :=
    actual_pureSource_positive_pair_transform_full_eventually_le
      d hd c hc hQ hB hβ
  obtain ⟨Cη,hCη,hTransfer⟩ :=
    actual_pureSource_uniformKilledResolvent_reference_transfer_any
      d hd c hc hQ hB hβ
  refine ⟨Cε,Cη,hCε,hCη,?_⟩
  filter_upwards [hSource,hTransfer] with n hs ht
  intro J hJ α hα hαsmall χ hχ hχb hχR e he θ hθ
  dsimp only
  obtain ⟨F,U,hPhysical,hFsm,hUsm,hBounds,hFrozen,hSourceBound⟩ :=
    hs J hJ α hα hαsmall χ hχ hχb hχR e he θ hθ
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
  let I : Vector (n+1)×Vector (n+1)→ℝ := fun z =>
    1+uniformInitialDensity (n+1) β H₀ z.2
  let f₀ : Vector (n+1)→ℝ := fun x => (gibbsDensity (n+1) β H₀ x)⁻¹
  have hN : 1≤n+1 := by omega
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) J).continuous
  have hH : Continuous (fun z : Vector (n+1)×Vector (n+1) =>
      pureSourceSmoothCutoffField d (by omega) c hc Q J z.1 e α χ z.2) :=
    (pure_axisJointHamiltonian_contDiff d (by omega) c hc Q α χ hχ J e).continuous
  have hw : Continuous w := (hH.sub (hH₀.comp continuous_snd)).const_mul β
  let : IsProbabilityMeasure (sphereLaw (n+1)) := sphereLaw_probability (n+1)
  let : IsProbabilityMeasure (gibbsLaw (n+1) β H₀) :=
    gibbsLaw_probability hN β hH₀
  have heExp : Integrable (fun z => Real.exp (w z))
      ((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀)) :=
    pair_exp_integrable_uniform hN β H₀ hH₀ hw.rexp
  have hMpos : 0<M := integral_exp_pos heExp
  have hΓ : Integrable (fun x : Vector (n+1) =>
      1+uniformInitialDensity (n+1) β H₀ x) (gibbsLaw (n+1) β H₀) :=
    integrable_gibbs_of_continuous hN β hH₀
      (continuous_const.add (uniformInitialDensity_continuous β H₀ hH₀))
  have hIi : Integrable I ν := by
    have hh := frozen_integrable_mul_under_normalizedTilt hN β H₀ hH₀
      w (fun _ => (1 : ℝ)) hw continuous_const hMpos
      (fun x => 1+uniformInitialDensity (n+1) β H₀ x) hΓ
    simpa only [one_mul,I,ν] using hh
  have hUaSm : StronglyMeasurable Ua := hUsm.comp_measurable (by fun_prop)
  have hUnorm : ∀ᵐ z ∂ν,‖Ua z‖≤1 := hBounds.mono (fun z hz => by
    rw [Real.norm_eq_abs,abs_of_nonneg hz.2.1]
    exact hz.2.2)
  have hIUi : Integrable (fun z => I z*Ua z) ν :=
    hIi.mul_bdd hUaSm.aestronglyMeasurable hUnorm
  have hf₀I (x : Vector (n+1)) : f₀ x=uniformInitialDensity (n+1) β H₀ x :=
    inv_gibbsDensity_eq_uniformInitialDensity β H₀ x
  have hfUpos : ∀ᵐ z ∂ν,0≤f₀ z.2*Ua z := by
    filter_upwards [hBounds] with z hz
    rw [hf₀I]
    exact mul_nonneg (uniformInitialDensity_pos hN β H₀ hH₀ z.2).le hz.2.1
  have hfUle : ∀ᵐ z ∂ν,f₀ z.2*Ua z≤I z*Ua z := by
    filter_upwards [hBounds] with z hz
    dsimp only [I]
    have hpos := hz.2.1
    rw [hf₀I]
    nlinarith [hpos]
  have hIntegralLe : (∫ z,f₀ z.2*Ua z ∂ν)≤(∫ z,I z*Ua z ∂ν) :=
    integral_mono_of_nonneg hfUpos hIUi hfUle
  have hUslice (u : Vector (n+1)) (hu : OnSphere u) :
      let D := FieldData.ofPure hN d (by omega) c hc Q J u e α χ hχ
      (fun x => U ((J,(u,(e,0))),x))=ᵐ[gibbsLaw (n+1) β D.hamiltonian]
        rateLaplace D β (PhysicalHitting.capKilling α u)
          (PhysicalHitting.capKilling_contDiff α u).continuous
          (PhysicalHitting.capKilling_nonneg α u) θ
          (killingVector D β (PhysicalHitting.capKilling α u)
            (PhysicalHitting.capKilling_contDiff α u).continuous) := by
    exact (hPhysical u hu).2
  have hTransferBound := ht J hJ α hα hαsmall χ hχ hχb hχR
    e he θ hθ U hUsm hUslice
  refine ⟨F,U,hPhysical,hFsm,hUsm,hBounds,hFrozen,?_⟩
  dsimp only at hSourceBound hTransferBound ⊢
  dsimp only [f₀,Ua,ν,H₀,w,M] at hTransferBound hIntegralLe
  linarith

end SlowEquilibration.ConditionedEntrance

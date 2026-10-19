-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourcePairTransformFull
public import SlowEquilibration.ConditionedEntranceActualSourceGlobalTilt

/-! The source's original latitude-good disorder event supplies both
axis moments to the actual mixed-source positive-pair transform bound. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SphericalAging.HardSphereDynamics
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
open SmoothKilled
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem pair_exp_integrable {N : ℕ} (hN : 1 ≤ N)
    (β : ℝ) (H : Vector N → ℝ) (hH : Continuous H)
    {f : Vector N × Vector N → ℝ} (hf : Continuous f) :
    Integrable f ((sphereLaw N).prod (gibbsLaw N β H)) := by
  let : IsProbabilityMeasure (sphereLaw N) := sphereLaw_probability N
  let : IsProbabilityMeasure (gibbsLaw N β H) := gibbsLaw_probability hN β hH
  have hs : ∀ᵐ z : Vector N × Vector N
      ∂(sphereLaw N).prod (gibbsLaw N β H),
      ‖z.1‖^2 = (N : ℝ) ∧ ‖z.2‖^2 = (N : ℝ) := by
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

theorem actual_mixedSource_positive_pair_transform_full_eventually_le
    (μ : FiniteMixture) (hd : 4≤μ.minDegree)
    {Q B β : ℝ} (hQ : 0<Q) (hQ1 : Q≤1)
    (hnp : μ.minDegree<μ.maxDegree) (hB : 0≤B) (hβ : 0≤β) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) μ.maxDegree), J∈
        EntranceLatitudeTangentObservable.originalLatitudeMeanGood n μ →
      ∀ (α : ℝ) (hα : 0<α),
        α≤EntranceLatitudeTangentObservable.sourceCutoffMomentScale μ Q B (2*β) →
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
      let ε := C*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ))
      let Hf := 2*Real.log 2+
        4*β*derivativeConstant (mixtureCoefficients μ)*((n+1 : ℕ) : ℝ)
      ∃ F : SourceParameters (n+1) μ×Vector (n+1)→ℝ,
      ∃ U : SourceParameters (n+1) μ×Vector (n+1)→ℝ,
        let Fa : Vector (n+1)×Vector (n+1)→ℝ := fun z =>
          F ((J,(z.1,(e,k))),z.2)
        let Ua : Vector (n+1)×Vector (n+1)→ℝ := fun z =>
          U ((J,(z.1,(e,k))),z.2)
        let I : Vector (n+1)×Vector (n+1)→ℝ := fun z =>
          1+uniformInitialDensity (n+1) β H₀ z.2
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
        (∫ z,I z*Ua z ∂ν) ≤
          (∫ z,PhysicalHitting.capKilling α z.1 z.2*Fa z*(1-Ua z) ∂ν)/(θ : ℝ)+
          10*Real.sqrt ε+
          2*Real.sqrt (ε*Hf*
            ((∫ z,PhysicalHitting.capKilling α z.1 z.2*Fa z ∂ν)/(θ : ℝ)+
              ε*(1+Hf))) := by
  obtain ⟨C,hC,hMom⟩ :=
    EntranceLatitudeTangentObservable.actual_sourceSmoothCutoffField_tilt_moments
      μ hd hQ hnp hB hβ
  have hSmall := sourceTilt_eta_eventually_half μ.minDegree hd C
  refine ⟨C,hC,?_⟩
  filter_upwards [hMom,hSmall] with n hn hs
  intro J hJ α hα hαsmall χ hχ hχb hχR e k he hk θ hθ
  dsimp only
  let H₀ := fieldOfMixture μ J
  let w : Vector (n+1)×Vector (n+1)→ℝ := fun z =>
    β*(sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2-H₀ z.2)
  let π := gibbsLaw (n+1) β H₀
  let M := ∫ z,Real.exp (w z) ∂((sphereLaw (n+1)).prod π)
  let η := C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)
  let ε := C*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ))
  have hN : 1≤n+1 := by omega
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff μ J).continuous
  let : IsProbabilityMeasure (sphereLaw (n+1)) := sphereLaw_probability (n+1)
  let : IsProbabilityMeasure π := gibbsLaw_probability hN β hH₀
  have hH : Continuous (fun z : Vector (n+1)×Vector (n+1) =>
      sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2) :=
    (sourceSmoothCutoffField_jointContinuous μ Q hQ hnp α χ hχ.continuous).comp
      (show Continuous (fun z : Vector (n+1)×Vector (n+1) =>
        (((J,(z.1,(e,k))),z.2) : SourceParameters (n+1) μ×Vector (n+1))) by fun_prop)
  have hw : Continuous w := (hH.sub (hH₀.comp continuous_snd)).const_mul β
  have heExp : Integrable (fun z => Real.exp (w z))
      ((sphereLaw (n+1)).prod π) := pair_exp_integrable hN β H₀ hH₀ hw.rexp
  have hηaxis : ∀ᵐ x ∂π,
      (∫ v,|Real.exp (w (v,x))-1| ∂sphereLaw (n+1))≤η := by
    filter_upwards [gibbsLaw_support hN β H₀] with x hx
    exact (hn J hJ x hx α hα hαsmall χ hχ hχb hχR e k he hk).1
  have hMclose : |M-1|≤η :=
    exponential_mass_close_one (sphereLaw (n+1)) π w heExp rfl hηaxis
  have hMlower : 1-η≤M := by
    have hl := (abs_le.mp hMclose).1
    linarith
  have hMhalf : 1/2≤M := by
    dsimp only [η] at *
    have hl := (abs_le.mp hMclose).1
    linarith
  have hη : 0≤η := by dsimp only [η]; positivity
  have hε : 0≤ε := by dsimp only [ε]; positivity
  have hAxisExp := axis_exponential_mean_le (sphereLaw (n+1)) π w heExp hηaxis
  have hAxisDefect : ∀ᵐ x ∂π,
      (∫ v,Real.exp (w (v,x))*(tiltDefect w (v,x))^2
        ∂sphereLaw (n+1))≤ε := by
    filter_upwards [gibbsLaw_support hN β H₀] with x hx
    dsimp only [ε,w,H₀]
    simpa only [tiltDefect,neg_mul] using
      (hn J hJ x hx α hα hαsmall χ hχ hχb hχR e k he hk).2
  have hJreg : J∈regularDisorder := hJ.1
  exact source_joint_positive_pair_transform_global_full_witness
    hN μ hnp Q hQ hQ1 α hα χ hχ β hβ θ hθ J hJreg
    e k B B 1 2 he hk (by norm_num) (by norm_num) hχb hχR
    M η ε hMhalf hη hs hMlower hε rfl hAxisExp hAxisDefect

end SlowEquilibration.ConditionedEntrance

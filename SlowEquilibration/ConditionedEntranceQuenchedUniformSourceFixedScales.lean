-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceQuenchedUniformSourceFixedRate

/-! The physical radius and exponential horizon exponent are chosen before
dimension, disorder, cutoff, marks and the positive resolvent rate. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SphericalAging.HardSphereDynamics
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
open SmoothKilled
set_option autoImplicit false
set_option maxHeartbeats 700000

theorem actual_mixedSource_uniform_positive_pair_fixed_scales
    (μ : FiniteMixture) (hd : 4≤μ.minDegree)
    {Q B β : ℝ} (hQ : 0<Q) (hQ1 : Q≤1)
    (hnp : μ.minDegree<μ.maxDegree) (hB : 0≤B) (hβ : 0≤β) :
    ∃ (α : ℝ) (hα : 0<α) (γ Cε Cη Ccap : ℝ),
      0<γ ∧ 0<Cε ∧ 0<Cη ∧ 0<Ccap ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) μ.maxDegree), J∈
        EntranceLatitudeTangentObservable.originalLatitudeMeanGood n μ →
      ∀ (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ),
        (∀ s,|χ s|≤1) → (∀ s,2 < |s| → χ s=0) →
      ∀ (e k : ℝ), |e|≤B → |k|≤B →
      ∀ (θ : ℝ≥0),0<θ →
        Real.exp (-γ*((n+1 : ℕ) : ℝ))≤(θ : ℝ) →
      let ε := Cε*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ))
      let η := Cη*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)
      let Hf := 2*Real.log 2+
        4*β*derivativeConstant (mixtureCoefficients μ)*((n+1 : ℕ) : ℝ)
      ∃ U : SourceParameters (n+1) μ×Vector (n+1)→ℝ,
        let Ua : Vector (n+1)×Vector (n+1)→ℝ := fun z =>
          U ((J,(z.1,(e,k))),z.2)
        StronglyMeasurable U ∧
        (∀ v : Vector (n+1),∀ hv : OnSphere v,
          let p : SourceParameters (n+1) μ := (J,(v,(e,k)))
          let D := SourceData.atSourceParameters (by omega : 1≤n+1)
            μ hnp Q hQ hQ1 α hα χ hχ p hv
          ((fun x => U (p,x))=ᵐ[gibbsLaw (n+1) β D.hamiltonian]
            rateLaplace D β (PhysicalHitting.capKilling α v)
              (PhysicalHitting.capKilling_contDiff α v).continuous
              (PhysicalHitting.capKilling_nonneg α v) θ
              (killingVector D β (PhysicalHitting.capKilling α v)
                (PhysicalHitting.capKilling_contDiff α v).continuous))) ∧
        (∫ u, ∫ x, Ua (u,x) ∂sphereLaw (n+1) ∂sphereLaw (n+1))≤
          4*η+10*Real.sqrt ε+3*ε*(1+Hf)+
            8*Ccap*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/256) := by
  let a₁ := EntranceLatitudeTangentObservable.sourceCutoffMomentScale μ Q B (2*β)
  let a₂ := 1/(128*(1+β*
    PhysicalHitting.uniformCutoffEnergyConstant μ Q B B 1 2))
  let α := min a₁ a₂
  let γ := α^2/256
  have ha₁ : 0<a₁ :=
    EntranceLatitudeTangentObservable.sourceCutoffMomentScale_pos μ Q B (2*β)
  have ha₂ : 0<a₂ :=
    PhysicalHitting.uniform_source_cutoff_cap_tail_radius_pos μ hβ hB hB
      (by norm_num : (0 : ℝ)≤2)
  have hα : 0<α := lt_min ha₁ ha₂
  have hγ : 0<γ := by dsimp only [γ]; positivity
  obtain ⟨Cε,Cη,Ccap,hCε,hCη,hCcap,hEvent⟩ :=
    actual_mixedSource_uniform_positive_pair_fixed_rate_eventually_le
      μ hd hQ hQ1 hnp hB hβ hα (min_le_left _ _) (min_le_right _ _)
      (le_refl γ)
  refine ⟨α,hα,γ,Cε,Cη,Ccap,hγ,hCε,hCη,hCcap,?_⟩
  filter_upwards [hEvent] with n hn
  intro J hJ χ hχ hχb hχR e k he hk θ hθ hrate
  dsimp only
  obtain ⟨F,U,hPhysical,_hFsm,hUsm,_hBounds,_hFrozen,hBound⟩ :=
    hn J hJ χ hχ hχb hχR e k he hk θ hθ hrate
  exact ⟨U,hUsm,(fun v hv => (hPhysical v hv).2),hBound⟩

end SlowEquilibration.ConditionedEntrance

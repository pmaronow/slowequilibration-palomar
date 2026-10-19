-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConditionedEntranceQuenchedUniformCapHitFixedScales

/-! Physical source cap-hit exposure at every sufficiently small prescribed
cutoff scale, rather than at just one selected scale. -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalOverlapExponential
open SphericalAging.HardSphereDynamics
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
open SmoothKilled PhysicalHitting
set_option autoImplicit false
set_option maxHeartbeats 900000

theorem actual_mixedSource_uniform_cap_hit_at_scale
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree)
    {Q B β : ℝ} (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hnp : μ.minDegree < μ.maxDegree) (hB : 0 ≤ B) (hβ : 0 ≤ β)
    {α : ℝ} (hα : 0 < α)
    (hαmoment : α ≤ EntranceLatitudeTangentObservable.sourceCutoffMomentScale μ Q B (2*β))
    (hαenergy : α ≤ 1/(128*(1+β*
      PhysicalHitting.uniformCutoffEnergyConstant μ Q B B 1 2))) :
    ∃ (γ Cε Cη Ccap : ℝ),
      0 < γ ∧ 0 < Cε ∧ 0 < Cη ∧ 0 < Ccap ∧
      ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) μ.maxDegree), J ∈
        EntranceLatitudeTangentObservable.originalLatitudeMeanGood n μ →
      ∀ (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ),
        (∀ s, |χ s| ≤ 1) → (∀ s, 2 < |s| → χ s = 0) →
      ∀ (e k : ℝ), |e| ≤ B → |k| ≤ B →
      ∀ (θ : ℝ≥0), 0 < θ →
        Real.exp (-γ*((n+1 : ℕ) : ℝ)) ≤ (θ : ℝ) →
      ∀ (u₀ : Vector (n+1)), OnSphere u₀ →
      ∀ (H T : ℝ≥0), 0 < T →
        4*(1+β*sourceGradientConstant μ Q e k α χ hχ)*(T : ℝ) ≤ α/12 →
      let ε := Cε*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ))
      let η := Cη*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)
      let Hf := 2*Real.log 2+
        4*β*derivativeConstant (mixtureCoefficients μ)*((n+1 : ℕ) : ℝ)
      exposureFactor (θ : ℝ) H T *
        ((∫ u,∫ x,sourceAxisCapHitProbability μ hQ hnp J β α χ hχ e k H u x
          ∂sphereLaw (n+1) ∂sphereLaw (n+1)) -
          (gridSize H T : ℝ)*
            (2*Real.exp (-((n+1 : ℕ) : ℝ)*(α/12)^2/(16*(T : ℝ))))) ≤
        4*η+10*Real.sqrt ε+3*ε*(1+Hf)+
          8*Ccap*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/256) := by
  let γ := α^2/256
  have hγ : 0 < γ := by dsimp only [γ]; positivity
  obtain ⟨Cε,Cη,Ccap,hCε,hCη,hCcap,hEvent⟩ :=
    actual_mixedSource_uniform_positive_pair_fixed_rate_eventually_le
      μ hd hQ hQ1 hnp hB hβ hα hαmoment hαenergy (le_refl γ)
  refine ⟨γ,Cε,Cη,Ccap,hγ,hCε,hCη,hCcap,?_⟩
  filter_upwards [hEvent] with n hn
  intro J hJ χ hχ hχb hχR e k he hk θ hθ hrate u₀ hu₀ H T hT hshort
  dsimp only
  obtain ⟨F,U,hPhysical,_hFsm,hUsm,_hBounds,_hFrozen,hBound⟩ :=
    hn J hJ χ hχ hχb hχR e k he hk θ hθ hrate
  have hReg : J ∈ regularDisorder := hJ.1
  have hCap := source_joint_uniform_cap_hit_le_physical_resolvent
    (by omega : 1 ≤ n+1) μ hnp Q hQ hQ1 α hα χ hχ β hβ θ hθ
    J hReg e k U hUsm (fun v hv => (hPhysical v hv).2)
    u₀ hu₀ H T hT hshort
  exact hCap.trans hBound

end SlowEquilibration.ConditionedEntrance

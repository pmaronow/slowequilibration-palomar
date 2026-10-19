-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConditionedEntrancePureQuenchedUniformFixedRate
public import SlowEquilibration.ConditionedEntrancePureJointUniformCapHitResolvent

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
open SmoothKilledGeneral PhysicalHitting
set_option autoImplicit false
set_option maxHeartbeats 900000

theorem actual_pureSource_uniform_cap_hit_at_scale
    (d : ℕ) (hd : 4 ≤ d) (c : ℝ) (hc : 0 < c)
    {Q B β : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) (hβ : 0 ≤ β)
    {α : ℝ} (hα : 0 < α)
    (hαmoment : α ≤ EntranceLatitudeTangentObservable.sourceCutoffMomentScale (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) Q B (2*β))
    (hαenergy : α ≤ 1/(128*(1+β*
      pureCutoffEnergyConstant d (by omega) c hc Q B))) :
    ∃ (γ Cε Cη Ccap : ℝ),
      0 < γ ∧ 0 < Cε ∧ 0 < Cη ∧ 0 < Ccap ∧
      ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) (FiniteMixture.pure d (by omega : 2 ≤ d) c hc).maxDegree), J ∈
        EntranceLatitudeTangentObservable.originalLatitudeMeanGood n (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) →
      ∀ (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ),
        (∀ s, |χ s| ≤ 1) → (∀ s, 2 < |s| → χ s = 0) →
      ∀ (e : ℝ), |e| ≤ B →
      ∀ (θ : ℝ≥0), 0 < θ →
        Real.exp (-γ*((n+1 : ℕ) : ℝ)) ≤ (θ : ℝ) →
      ∀ (H : ℝ≥0),
      let T := pureSourceShortCell d (by omega) c hc Q B α β hB hα hβ χ hχ
      let ε := Cε*((n+1 : ℕ) : ℝ)^(2-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ))
      let η := Cη*((n+1 : ℕ) : ℝ)^(1-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ)/2)
      let Hf := 2*Real.log 2+
        4*β*derivativeConstant (mixtureCoefficients (FiniteMixture.pure d (by omega : 2 ≤ d) c hc))*((n+1 : ℕ) : ℝ)
      exposureFactor (θ : ℝ) H T *
        ((∫ u,pureSourceCapHitProbability d (by omega) c hc Q α χ hχ β H
          (J,(u,(e,0))) ∂sphereLaw (n+1)) -
          (gridSize H T : ℝ)*
            (2*Real.exp (-((n+1 : ℕ) : ℝ)*(α/12)^2/(16*(T : ℝ))))) ≤
        4*η+10*Real.sqrt ε+3*ε*(1+Hf)+
          8*Ccap*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/256) := by
  let γ := α^2/256
  have hγ : 0 < γ := by dsimp only [γ]; positivity
  obtain ⟨Cε,Cη,Ccap,hCε,hCη,hCcap,hEvent⟩ :=
    actual_pureSource_uniform_positive_pair_fixed_rate_eventually_le
      d hd c hc hQ hB hβ hα hαmoment hαenergy (le_refl γ)
  refine ⟨γ,Cε,Cη,Ccap,hγ,hCε,hCη,hCcap,?_⟩
  filter_upwards [hEvent] with n hn
  intro J hJ χ hχ hχb hχR e he θ hθ hrate H
  dsimp only
  obtain ⟨F,U,hPhysical,_hFsm,hUsm,_hBounds,_hFrozen,hBound⟩ :=
    hn J hJ χ hχ hχb hχR e he θ hθ hrate
  have hReg : J ∈ regularDisorder := hJ.1
  have hCap := pure_joint_uniform_cap_hit_le_physical_resolvent
    (by omega : 1 ≤ n+1) d (by omega) c hc Q B α β hB hα hβ
    χ hχ θ hθ J hReg e he U hUsm (fun v hv => (hPhysical v hv).2) H
  exact hCap.trans hBound

end SlowEquilibration.ConditionedEntrance

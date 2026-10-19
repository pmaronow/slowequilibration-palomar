-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceUniformCapHitExponentialAtScale
public import SlowEquilibration.ConditionedEntranceSourceDisorderGoodTransfer

/-! The physical mixed-source cap-hit estimate after averaging the original
Gaussian tensor disorder, with its literal exceptional-event probability. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalOverlapExponential
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 900000

theorem actual_mixedSource_axis_averaged_cap_hit_disorder_bound_at_scale
    (μ : FiniteMixture) (hd : 4≤μ.minDegree)
    {Q B β : ℝ} (hQ : 0<Q) (hQ1 : Q≤1)
    (hnp : μ.minDegree<μ.maxDegree) (hB : 0≤B) (hβ : 0≤β)
    {α : ℝ} (hα : 0<α)
    (hαmoment : α≤EntranceLatitudeTangentObservable.sourceCutoffMomentScale μ Q B (2*β))
    (hαenergy : α≤1/(128*(1+β*
      PhysicalHitting.uniformCutoffEnergyConstant μ Q B B 1 2)))
    (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (hχb : ∀ s,|χ s|≤1) (hχR : ∀ s,2 < |s|→χ s=0) :
    ∃ (γ Cε Cη Ccap : ℝ),
      0<γ ∧ 0<Cε ∧ 0<Cη ∧ 0<Ccap ∧
      let T := sourceShortCell μ Q B α β hα hβ χ hχ
      let c₀ := Real.exp (-2)*(1-Real.exp (-(T : ℝ)))
      0<c₀ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (e k : ℝ), |e|≤B → |k|≤B →
      let H := exponentialGridHorizon γ (n+1)
      let ε := Cε*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ))
      let η := Cη*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)
      let Hf := 2*Real.log 2+
        4*β*derivativeConstant (mixtureCoefficients μ)*((n+1 : ℕ) : ℝ)
      let R := (2/(T : ℝ)+4)*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/256)+
        (4*η+10*Real.sqrt ε+3*ε*(1+Hf)+
          8*Ccap*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/256))/c₀
      (∫ J,sourceAxisAveragedCapHitProbability μ Q hQ hnp α χ hχ β H e k J
        ∂disorderLaw (n+1) μ.maxDegree)≤
        R+(disorderLaw (n+1) μ.maxDegree).real
          (EntranceLatitudeTangentObservable.originalLatitudeMeanGood n μ)ᶜ := by
  obtain ⟨γ,Cε,Cη,Ccap,hγ,hCε,hCη,hCcap,hc₀,hEvent⟩ :=
    actual_mixedSource_uniform_cap_hit_exponential_horizon_at_scale
      μ hd hQ hQ1 hnp hB hβ hα hαmoment hαenergy χ hχ hχb hχR
  refine ⟨γ,Cε,Cη,Ccap,hγ,hCε,hCη,hCcap,hc₀,?_⟩
  filter_upwards [hEvent,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  intro e k he hk
  dsimp only
  let T := sourceShortCell μ Q B α β hα hβ χ hχ
  let c₀ := Real.exp (-2)*(1-Real.exp (-(T : ℝ)))
  let H := exponentialGridHorizon γ (n+1)
  let ε := Cε*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ))
  let η := Cη*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)
  let Hf := 2*Real.log 2+
    4*β*derivativeConstant (mixtureCoefficients μ)*((n+1 : ℕ) : ℝ)
  let R := (2/(T : ℝ)+4)*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/256)+
    (4*η+10*Real.sqrt ε+3*ε*(1+Hf)+
      8*Ccap*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/256))/c₀
  have hε : 0≤ε := by dsimp only [ε]; positivity
  have hη : 0≤η := by dsimp only [η]; positivity
  have hHf : 0≤Hf := by
    have hdpos := (derivativeConstant_pos (mixtureCoefficients μ)).le
    have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
    dsimp only [Hf]
    positivity
  have hT : 0<T := sourceShortCell_pos μ Q B α β hα hβ χ hχ
  have hR : 0≤R := by dsimp only [R]; positivity
  have hGood : MeasurableSet (EntranceLatitudeTangentObservable.originalLatitudeMeanGood n μ) :=
    EntranceLatitudeTangentObservable.originalLatitudeMeanGood_measurable hn1 μ
  have hPoint (J : Disorder (n+1) μ.maxDegree)
      (hJ : J∈EntranceLatitudeTangentObservable.originalLatitudeMeanGood n μ) :
      sourceAxisAveragedCapHitProbability μ Q hQ hnp α χ hχ β H e k J≤R := by
    rw [sourceAxisAveragedCapHitProbability_eq_physical (by omega : 1≤n+1)
      μ hnp Q hQ hQ1 α hα χ hχ β H e k J]
    have h := hn J hJ e k he hk
    change (∫ u,∫ x,sourceAxisCapHitProbability μ hQ hnp J β α χ hχ e k H u x
      ∂sphereLaw (n+1) ∂sphereLaw (n+1))≤R at h
    exact h
  exact sourceAxisAveragedCapHitProbability_disorder_good_transfer
    μ Q hQ hnp α χ hχ β H e k _ hGood R hR hPoint

end SlowEquilibration.ConditionedEntrance

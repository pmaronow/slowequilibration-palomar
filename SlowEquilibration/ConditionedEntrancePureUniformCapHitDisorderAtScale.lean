-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureAxisDisorderAverage
public import SlowEquilibration.ConditionedEntrancePureUniformCapHitExponentialAtScale
public import SlowEquilibration.ConditionedEntranceSourceDisorderGoodTransfer

/-! The physical proper-pure source cap-hit estimate after averaging the original
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

theorem actual_pureSource_axis_averaged_cap_hit_disorder_bound_at_scale
    (d : ℕ) (hd : 4 ≤ d) (c : ℝ) (hc : 0 < c)
    {Q B β : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) (hβ : 0 ≤ β)
    {α : ℝ} (hα : 0<α)
    (hαmoment : α≤EntranceLatitudeTangentObservable.sourceCutoffMomentScale (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) Q B (2*β))
    (hαenergy : α≤1/(128*(1+β*
      pureCutoffEnergyConstant d (by omega) c hc Q B)))
    (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (hχb : ∀ s,|χ s|≤1) (hχR : ∀ s,2 < |s|→χ s=0) :
    ∃ (γ Cε Cη Ccap : ℝ),
      0<γ ∧ 0<Cε ∧ 0<Cη ∧ 0<Ccap ∧
      let T := pureSourceShortCell d (by omega) c hc Q B α β hB hα hβ χ hχ
      let c₀ := Real.exp (-2)*(1-Real.exp (-(T : ℝ)))
      0<c₀ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (e : ℝ), |e|≤B →
      let H := exponentialGridHorizon γ (n+1)
      let ε := Cε*((n+1 : ℕ) : ℝ)^(2-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ))
      let η := Cη*((n+1 : ℕ) : ℝ)^(1-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ)/2)
      let Hf := 2*Real.log 2+
        4*β*derivativeConstant (mixtureCoefficients (FiniteMixture.pure d (by omega : 2 ≤ d) c hc))*((n+1 : ℕ) : ℝ)
      let R := (2/(T : ℝ)+4)*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/256)+
        (4*η+10*Real.sqrt ε+3*ε*(1+Hf)+
          8*Ccap*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/256))/c₀
      (∫ J,pureAxisAveragedCapHitProbability d (by omega) c hc Q α χ hχ β H e J
        ∂disorderLaw (n+1) (FiniteMixture.pure d (by omega : 2 ≤ d) c hc).maxDegree)≤
        R+(disorderLaw (n+1) (FiniteMixture.pure d (by omega : 2 ≤ d) c hc).maxDegree).real
          (EntranceLatitudeTangentObservable.originalLatitudeMeanGood n (FiniteMixture.pure d (by omega : 2 ≤ d) c hc))ᶜ := by
  obtain ⟨γ,Cε,Cη,Ccap,hγ,hCε,hCη,hCcap,hc₀,hEvent⟩ :=
    actual_pureSource_uniform_cap_hit_exponential_horizon_at_scale
      d hd c hc hQ hB hβ hα hαmoment hαenergy χ hχ hχb hχR
  refine ⟨γ,Cε,Cη,Ccap,hγ,hCε,hCη,hCcap,hc₀,?_⟩
  filter_upwards [hEvent,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  intro e he
  dsimp only
  let T := pureSourceShortCell d (by omega) c hc Q B α β hB hα hβ χ hχ
  let c₀ := Real.exp (-2)*(1-Real.exp (-(T : ℝ)))
  let H := exponentialGridHorizon γ (n+1)
  let ε := Cε*((n+1 : ℕ) : ℝ)^(2-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ))
  let η := Cη*((n+1 : ℕ) : ℝ)^(1-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ)/2)
  let Hf := 2*Real.log 2+
    4*β*derivativeConstant (mixtureCoefficients (FiniteMixture.pure d (by omega : 2 ≤ d) c hc))*((n+1 : ℕ) : ℝ)
  let R := (2/(T : ℝ)+4)*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/256)+
    (4*η+10*Real.sqrt ε+3*ε*(1+Hf)+
      8*Ccap*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/256))/c₀
  have hε : 0≤ε := by dsimp only [ε]; positivity
  have hη : 0≤η := by dsimp only [η]; positivity
  have hHf : 0≤Hf := by
    have hdpos := (derivativeConstant_pos (mixtureCoefficients (FiniteMixture.pure d (by omega : 2 ≤ d) c hc))).le
    have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
    dsimp only [Hf]
    positivity
  have hT : 0<T := pureSourceShortCell_pos d (by omega) c hc Q B α β hB hα hβ χ hχ
  have hR : 0≤R := by dsimp only [R]; positivity
  have hGood : MeasurableSet (EntranceLatitudeTangentObservable.originalLatitudeMeanGood n (FiniteMixture.pure d (by omega : 2 ≤ d) c hc)) :=
    EntranceLatitudeTangentObservable.originalLatitudeMeanGood_measurable hn1 (FiniteMixture.pure d (by omega : 2 ≤ d) c hc)
  have hd2 : 2 ≤ d := by omega
  have hPoint (J : Disorder (n+1) (FiniteMixture.pure d hd2 c hc).maxDegree)
      (hJ : J∈EntranceLatitudeTangentObservable.originalLatitudeMeanGood n (FiniteMixture.pure d hd2 c hc)) :
      pureAxisAveragedCapHitProbability d hd2 c hc Q α χ hχ β H e J≤R := by
    exact hn J hJ e he
  exact unit_observable_good_event_integral_le (disorderLaw (n+1) (FiniteMixture.pure d (by omega : 2 ≤ d) c hc).maxDegree) _
    (pureAxisAveragedCapHitProbability_measurable d (by omega) c hc Q α χ hχ β H e)
    (pureAxisAveragedCapHitProbability_mem_unit d (by omega) c hc Q α χ hχ β H e)
    _ hGood R hR hPoint

end SlowEquilibration.ConditionedEntrance

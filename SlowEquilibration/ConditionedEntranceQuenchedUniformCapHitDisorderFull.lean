-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceDisorderFailureReal

/-! Explicit unconditional Gaussian-disorder bound for the original
axis-averaged, uniform-start, physical mixed-source cap-hit probability. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalOverlapExponential
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false

theorem actual_mixedSource_axis_averaged_cap_hit_disorder_full
    (μ : FiniteMixture) (hd : 4≤μ.minDegree)
    {Q B β : ℝ} (hQ : 0<Q) (hQ1 : Q≤1)
    (hnp : μ.minDegree<μ.maxDegree) (hB : 0≤B) (hβ : 0≤β)
    (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (hχb : ∀ s,|χ s|≤1) (hχR : ∀ s,2 < |s|→χ s=0) :
    ∃ (α : ℝ) (hα : 0<α) (γ Cε Cη Ccap : ℝ),
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
        R+Real.exp (-((n+1 : ℕ) : ℝ))+
          (EntranceLatitudeTangentObservable.originalLatitudeBankCount μ : ℝ)*
            (2*Real.exp (-((n+1 : ℕ) : ℝ)/2)) := by
  obtain ⟨α,hα,γ,Cε,Cη,Ccap,hγ,hCε,hCη,hCcap,hc₀,hEvent⟩ :=
    actual_mixedSource_axis_averaged_cap_hit_disorder_bound
      μ hd hQ hQ1 hnp hB hβ χ hχ hχb hχR
  refine ⟨α,hα,γ,Cε,Cη,Ccap,hγ,hCε,hCη,hCcap,hc₀,?_⟩
  filter_upwards [hEvent,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  intro e k he hk
  dsimp only
  have h := hn e k he hk
  have hb := originalLatitudeMeanGood_failure_real_le hn1 μ
  have hR :
      (disorderLaw (n+1) μ.maxDegree).real
        (EntranceLatitudeTangentObservable.originalLatitudeMeanGood n μ)ᶜ≤
      Real.exp (-((n+1 : ℕ) : ℝ))+
        (EntranceLatitudeTangentObservable.originalLatitudeBankCount μ : ℝ)*
          (2*Real.exp (-((n+1 : ℕ) : ℝ)/2)) := hb
  dsimp only at h
  linarith

end SlowEquilibration.ConditionedEntrance

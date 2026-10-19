-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceRateNumeric
public import SlowEquilibration.ConditionedEntrancePureUniformCapHitDisorderFullAtScale

/-! The physical averaged cutoff cap-hit rate for any prescribed sufficiently small scale. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SlowEquilibration.SphericalModel
open SlowEquilibration.SphericalOverlapExponential
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The original Gaussian-disorder, uniform-axis, uniform-start proper-pure source
cap-hit probability has exactly the two powers and the exponential remainder
printed in the manuscript. The cutoff scale and constants are chosen before
dimension and before the value mark. -/
theorem actual_pureSource_axis_averaged_cap_hit_source_rate_at_scale
    (d : ℕ) (hd : 4 ≤ d) (c : ℝ) (hc : 0 < c)
    {Q B β : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) (hβ : 0 ≤ β)
    {α : ℝ} (hα : 0 < α)
    (hαmoment : α ≤ EntranceLatitudeTangentObservable.sourceCutoffMomentScale (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) Q B (2*β))
    (hαenergy : α ≤ 1/(128*(1+β*
      pureCutoffEnergyConstant d (by omega) c hc Q B)))
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (hχb : ∀ s, |χ s| ≤ 1) (hχR : ∀ s, 2 < |s| → χ s = 0) :
    ∃ (γ decay C : ℝ),
      0 < γ ∧ 0 < decay ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (e : ℝ), |e| ≤ B →
        (∫ J, pureAxisAveragedCapHitProbability d (by omega) c hc Q α χ hχ β
          (exponentialGridHorizon γ (n+1)) e J
          ∂disorderLaw (n+1) (FiniteMixture.pure d (by omega : 2 ≤ d) c hc).maxDegree) ≤
        C*(((n+1 : ℕ) : ℝ)^(1-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ)/2)+
          ((n+1 : ℕ) : ℝ)^(3-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ)))+
          Real.exp (-decay*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨γ,Cε,Cη,Ccap,hγ,hCε,hCη,hCcap,hc₀,hEvent⟩ :=
    actual_pureSource_axis_averaged_cap_hit_disorder_full_at_scale
      d hd c hc hQ hB hβ hα hαmoment hαenergy χ hχ hχb hχR
  let T := pureSourceShortCell d (by omega) c hc Q B α β hB hα hβ χ hχ
  let c₀ := Real.exp (-2)*(1-Real.exp (-(T : ℝ)))
  let D := derivativeConstant (mixtureCoefficients (FiniteMixture.pure d (by omega : 2 ≤ d) c hc))
  let a := min (α^2/256) (1/2 : ℝ)
  let decay := a/2
  let C := 1+(4*Cη+10*Real.sqrt Cε+
    3*Cε*(1+2*Real.log 2+4*β*D))/c₀
  have hT : 0 < (T : ℝ) := by
    exact_mod_cast pureSourceShortCell_pos d (by omega) c hc Q B α β hB hα hβ χ hχ
  have hD : 0 ≤ D := (derivativeConstant_pos (mixtureCoefficients (FiniteMixture.pure d (by omega : 2 ≤ d) c hc))).le
  have hC : 0 < C :=
    (entrance_polynomial_source_bound ((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ) 1 Cε Cη β D c₀
      (le_refl 1) hCε.le hCη.le hβ hD hc₀).1
  have hExp := entrance_exponential_source_bound α (T : ℝ) c₀ Ccap
    (EntranceLatitudeTangentObservable.originalLatitudeBankCount (FiniteMixture.pure d (by omega : 2 ≤ d) c hc))
    hα hT hc₀ hCcap.le
  have hdecay : 0 < decay := hExp.1
  refine ⟨γ,decay,C,hγ,hdecay,hC,?_⟩
  filter_upwards [hEvent,hExp.2] with n hn hEn
  intro e he
  let x : ℝ := ((n+1 : ℕ) : ℝ)
  let p := x^(1-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ)/2)
  let q := x^(3-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ))
  let ε := Cε*x^(2-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ))
  let η := Cη*p
  let Hf := 2*Real.log 2+4*β*D*x
  let P : ℝ := ∫ J, pureAxisAveragedCapHitProbability d (by omega) c hc Q α χ hχ β
    (exponentialGridHorizon γ (n+1)) e J ∂disorderLaw (n+1) (FiniteMixture.pure d (by omega : 2 ≤ d) c hc).maxDegree
  have hx : 1 ≤ x := by dsimp only [x]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hpoly := (entrance_polynomial_source_bound ((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ) x
    Cε Cη β D c₀ hx hCε.le hCη.le hβ hD hc₀).2
  change (4*η+10*Real.sqrt ε+3*ε*(1+Hf))/c₀ ≤ C*(p+q) at hpoly
  change (2/(T : ℝ)+4)*Real.exp (-x*α^2/256)+
      (8*Ccap*Real.exp (-x*α^2/256))/c₀+Real.exp (-x)+
      (EntranceLatitudeTangentObservable.originalLatitudeBankCount (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) : ℝ)*
        (2*Real.exp (-x/2)) ≤ Real.exp (-decay*x) at hEn
  have hP : P ≤ (2/(T : ℝ)+4)*Real.exp (-x*α^2/256)+
      (4*η+10*Real.sqrt ε+3*ε*(1+Hf)+
        8*Ccap*Real.exp (-x*α^2/256))/c₀+
      Real.exp (-x)+
      (EntranceLatitudeTangentObservable.originalLatitudeBankCount (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) : ℝ)*
        (2*Real.exp (-x/2)) := by
    simpa only [P,T,c₀,D,x,p,ε,η,Hf] using hn e he
  change P ≤ C*(p+q)+Real.exp (-decay*x)
  calc
    P ≤ (4*η+10*Real.sqrt ε+3*ε*(1+Hf))/c₀+
      ((2/(T : ℝ)+4)*Real.exp (-x*α^2/256)+
        (8*Ccap*Real.exp (-x*α^2/256))/c₀+Real.exp (-x)+
        (EntranceLatitudeTangentObservable.originalLatitudeBankCount (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) : ℝ)*
          (2*Real.exp (-x/2))) := by
      convert hP using 1
      ring
    _ ≤ C*(p+q)+Real.exp (-decay*x) := add_le_add hpoly hEn

end SlowEquilibration.ConditionedEntrance

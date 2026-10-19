-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceRateNumeric
public import SlowEquilibration.ConditionedEntranceSourceUniformCapHitDisorderFullAtScale

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

/-- The original Gaussian-disorder, uniform-axis, uniform-start mixed-source
cap-hit probability has exactly the two powers and the exponential remainder
printed in the manuscript. The cutoff scale and constants are chosen before
dimension and before the two marks. -/
theorem actual_mixedSource_axis_averaged_cap_hit_source_rate_at_scale
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree)
    {Q B β : ℝ} (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hnp : μ.minDegree < μ.maxDegree) (hB : 0 ≤ B) (hβ : 0 ≤ β)
    {α : ℝ} (hα : 0 < α)
    (hαmoment : α ≤ EntranceLatitudeTangentObservable.sourceCutoffMomentScale μ Q B (2*β))
    (hαenergy : α ≤ 1/(128*(1+β*
      PhysicalHitting.uniformCutoffEnergyConstant μ Q B B 1 2)))
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (hχb : ∀ s, |χ s| ≤ 1) (hχR : ∀ s, 2 < |s| → χ s = 0) :
    ∃ (γ c C : ℝ),
      0 < γ ∧ 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (e k : ℝ), |e| ≤ B → |k| ≤ B →
        (∫ J, sourceAxisAveragedCapHitProbability μ Q hQ hnp α χ hχ β
          (exponentialGridHorizon γ (n+1)) e k J
          ∂disorderLaw (n+1) μ.maxDegree) ≤
        C*(((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)+
          ((n+1 : ℕ) : ℝ)^(3-(μ.minDegree : ℝ)))+
          Real.exp (-c*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨γ,Cε,Cη,Ccap,hγ,hCε,hCη,hCcap,hc₀,hEvent⟩ :=
    actual_mixedSource_axis_averaged_cap_hit_disorder_full_at_scale
      μ hd hQ hQ1 hnp hB hβ hα hαmoment hαenergy χ hχ hχb hχR
  let T := sourceShortCell μ Q B α β hα hβ χ hχ
  let c₀ := Real.exp (-2)*(1-Real.exp (-(T : ℝ)))
  let D := derivativeConstant (mixtureCoefficients μ)
  let a := min (α^2/256) (1/2 : ℝ)
  let c := a/2
  let C := 1+(4*Cη+10*Real.sqrt Cε+
    3*Cε*(1+2*Real.log 2+4*β*D))/c₀
  have hT : 0 < (T : ℝ) := by
    exact_mod_cast sourceShortCell_pos μ Q B α β hα hβ χ hχ
  have hD : 0 ≤ D := (derivativeConstant_pos (mixtureCoefficients μ)).le
  have hC : 0 < C :=
    (entrance_polynomial_source_bound (μ.minDegree : ℝ) 1 Cε Cη β D c₀
      (le_refl 1) hCε.le hCη.le hβ hD hc₀).1
  have hExp := entrance_exponential_source_bound α (T : ℝ) c₀ Ccap
    (EntranceLatitudeTangentObservable.originalLatitudeBankCount μ)
    hα hT hc₀ hCcap.le
  have hc : 0 < c := hExp.1
  refine ⟨γ,c,C,hγ,hc,hC,?_⟩
  filter_upwards [hEvent,hExp.2] with n hn hEn
  intro e k he hk
  let x : ℝ := ((n+1 : ℕ) : ℝ)
  let p := x^(1-(μ.minDegree : ℝ)/2)
  let q := x^(3-(μ.minDegree : ℝ))
  let ε := Cε*x^(2-(μ.minDegree : ℝ))
  let η := Cη*p
  let Hf := 2*Real.log 2+4*β*D*x
  let P : ℝ := ∫ J, sourceAxisAveragedCapHitProbability μ Q hQ hnp α χ hχ β
    (exponentialGridHorizon γ (n+1)) e k J ∂disorderLaw (n+1) μ.maxDegree
  have hx : 1 ≤ x := by dsimp only [x]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hpoly := (entrance_polynomial_source_bound (μ.minDegree : ℝ) x
    Cε Cη β D c₀ hx hCε.le hCη.le hβ hD hc₀).2
  change (4*η+10*Real.sqrt ε+3*ε*(1+Hf))/c₀ ≤ C*(p+q) at hpoly
  change (2/(T : ℝ)+4)*Real.exp (-x*α^2/256)+
      (8*Ccap*Real.exp (-x*α^2/256))/c₀+Real.exp (-x)+
      (EntranceLatitudeTangentObservable.originalLatitudeBankCount μ : ℝ)*
        (2*Real.exp (-x/2)) ≤ Real.exp (-c*x) at hEn
  have hP : P ≤ (2/(T : ℝ)+4)*Real.exp (-x*α^2/256)+
      (4*η+10*Real.sqrt ε+3*ε*(1+Hf)+
        8*Ccap*Real.exp (-x*α^2/256))/c₀+
      Real.exp (-x)+
      (EntranceLatitudeTangentObservable.originalLatitudeBankCount μ : ℝ)*
        (2*Real.exp (-x/2)) := by
    simpa only [P,T,c₀,D,x,p,ε,η,Hf] using hn e k he hk
  change P ≤ C*(p+q)+Real.exp (-c*x)
  calc
    P ≤ (4*η+10*Real.sqrt ε+3*ε*(1+Hf))/c₀+
      ((2/(T : ℝ)+4)*Real.exp (-x*α^2/256)+
        (8*Ccap*Real.exp (-x*α^2/256))/c₀+Real.exp (-x)+
        (EntranceLatitudeTangentObservable.originalLatitudeBankCount μ : ℝ)*
          (2*Real.exp (-x/2))) := by
      convert hP using 1
      ring
    _ ≤ C*(p+q)+Real.exp (-c*x) := add_le_add hpoly hEn

end SlowEquilibration.ConditionedEntrance

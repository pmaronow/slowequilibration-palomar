-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConditionedEntranceQuenchedUniformCapHitDisorderFull
public import SlowEquilibration.SphericalEvenReplicaTypicality

/-! Reduction of the literal physical entrance error to the manuscript's
two power laws and one exponential. -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SlowEquilibration.SphericalModel
open SlowEquilibration.SphericalOverlapExponential
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem entrance_sqrt_power_identity (x C d : ℝ)
    (hx : 0 < x) (hC : 0 ≤ C) :
    Real.sqrt (C*x^(2-d)) = Real.sqrt C*x^(1-d/2) := by
  rw [Real.sqrt_mul hC, Real.sqrt_eq_rpow]
  have hh : Real.sqrt (x^(2-d)) = x^(1-d/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
    congr 1
    ring
  rw [hh]

theorem entrance_power_linear_identity (x d : ℝ) (hx : 0 < x) :
    x^(2-d)*x = x^(3-d) := by
  calc
    x^(2-d)*x = x^(2-d)*x^(1:ℝ) := by rw [Real.rpow_one]
    _ = x^((2-d)+1) := (Real.rpow_add hx (2-d) 1).symm
    _ = x^(3-d) := by congr 1; ring

theorem entrance_polynomial_source_bound (d x Cε Cη β D c₀ : ℝ)
    (hx : 1 ≤ x) (hCε : 0 ≤ Cε) (hCη : 0 ≤ Cη)
    (hβ : 0 ≤ β) (hD : 0 ≤ D) (hc₀ : 0 < c₀) :
    let p := x^(1-d/2)
    let q := x^(3-d)
    let ε := Cε*x^(2-d)
    let η := Cη*p
    let Hf := 2*Real.log 2+4*β*D*x
    let C := 1+(4*Cη+10*Real.sqrt Cε+
      3*Cε*(1+2*Real.log 2+4*β*D))/c₀
    0 < C ∧
      (4*η+10*Real.sqrt ε+3*ε*(1+Hf))/c₀ ≤ C*(p+q) := by
  dsimp only
  let p := x^(1-d/2)
  let q := x^(3-d)
  let r := x^(2-d)
  let A := 4*Cη+10*Real.sqrt Cε
  let B := 3*Cε*(1+2*Real.log 2+4*β*D)
  let C := 1+(A+B)/c₀
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hp : 0 ≤ p := Real.rpow_nonneg hxpos.le _
  have hq : 0 ≤ q := Real.rpow_nonneg hxpos.le _
  have hr : 0 ≤ r := Real.rpow_nonneg hxpos.le _
  have hrq : r ≤ q := by
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hrx : r*x = q := entrance_power_linear_identity x d hxpos
  have hsqrt : Real.sqrt (Cε*r) = Real.sqrt Cε*p :=
    entrance_sqrt_power_identity x Cε d hxpos hCε
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hCp : 0 < C := by dsimp only [C]; positivity
  have hpoly :
      4*(Cη*p)+10*Real.sqrt (Cε*r)+
        3*(Cε*r)*(1+(2*Real.log 2+4*β*D*x)) ≤ A*p+B*q := by
    rw [hsqrt]
    have hfront : 0 ≤ 3*Cε*(1+2*Real.log 2) := by positivity
    have hmove := mul_le_mul_of_nonneg_left hrq hfront
    dsimp only [A,B]
    nlinarith [hrx]
  have hCdom : (A*p+B*q)/c₀ ≤ C*(p+q) := by
    have hC₁ : 0 ≤ (A+B)*p - A*p := by nlinarith [mul_nonneg hB hp]
    have hC₂ : 0 ≤ (A+B)*q - B*q := by nlinarith [mul_nonneg hA hq]
    have hsum : A*p+B*q ≤ (A+B)*(p+q) := by nlinarith
    calc
      _ ≤ ((A+B)*(p+q))/c₀ :=
        div_le_div_of_nonneg_right hsum hc₀.le
      _ = ((A+B)/c₀)*(p+q) := by ring
      _ ≤ C*(p+q) := by
        dsimp only [C]
        nlinarith [add_nonneg hp hq]
  constructor
  · exact hCp
  · have hdiv := div_le_div_of_nonneg_right hpoly hc₀.le
    exact hdiv.trans hCdom

theorem entrance_exponential_source_bound
    (α T c₀ Ccap : ℝ) (bank : ℕ)
    (hα : 0 < α) (hT : 0 < T) (hc₀ : 0 < c₀)
    (hCcap : 0 ≤ Ccap) :
    let a := min (α^2/256) (1/2 : ℝ)
    0 < a/2 ∧ ∀ᶠ n : ℕ in atTop,
      (2/T+4)*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/256)+
        (8*Ccap*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/256))/c₀+
        Real.exp (-((n+1 : ℕ) : ℝ))+
        (bank : ℝ)*(2*Real.exp (-((n+1 : ℕ) : ℝ)/2)) ≤
          Real.exp (-(a/2)*((n+1 : ℕ) : ℝ)) := by
  dsimp only
  let a := min (α^2/256) (1/2 : ℝ)
  let K := 2/T+4+8*Ccap/c₀+1+2*(bank : ℝ)
  have ha : 0 < a := lt_min (by positivity) (by norm_num)
  have hg : 0 ≤ 2/T+4 := by positivity
  have hh : 0 ≤ 8*Ccap/c₀ := by positivity
  have hb : 0 ≤ (bank : ℝ) := Nat.cast_nonneg bank
  refine ⟨half_pos ha,?_⟩
  filter_upwards [weighted_exponential_eventually_le ha K] with n hn
  let x : ℝ := ((n+1 : ℕ) : ℝ)
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hαexp : Real.exp (-x*α^2/256) ≤ Real.exp (-a*x) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (min_le_left (α^2/256) (1/2)) hx
    nlinarith
  have hhalfexp : Real.exp (-x/2) ≤ Real.exp (-a*x) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (min_le_right (α^2/256) (1/2)) hx
    nlinarith
  have honeexp : Real.exp (-x) ≤ Real.exp (-a*x) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (min_le_right (α^2/256) (1/2)) hx
    nlinarith
  have h₁ := mul_le_mul_of_nonneg_left hαexp hg
  have h₂ := mul_le_mul_of_nonneg_left hαexp hh
  have h₃ := mul_le_mul_of_nonneg_left hhalfexp (by positivity : 0 ≤ 2*(bank : ℝ))
  have hsum :
      (2/T+4)*Real.exp (-x*α^2/256)+
        (8*Ccap*Real.exp (-x*α^2/256))/c₀+
        Real.exp (-x)+(bank : ℝ)*(2*Real.exp (-x/2)) ≤
          K*Real.exp (-a*x) := by
    calc
      _ = (2/T+4)*Real.exp (-x*α^2/256)+
          (8*Ccap/c₀)*Real.exp (-x*α^2/256)+
          Real.exp (-x)+(2*(bank : ℝ))*Real.exp (-x/2) := by ring
      _ ≤ (2/T+4)*Real.exp (-a*x)+
          (8*Ccap/c₀)*Real.exp (-a*x)+
          Real.exp (-a*x)+(2*(bank : ℝ))*Real.exp (-a*x) := by
        gcongr
      _ = K*Real.exp (-a*x) := by dsimp only [K]; ring
  exact hsum.trans hn

/-- The original Gaussian-disorder, uniform-axis, uniform-start mixed-source
cap-hit probability has exactly the two powers and the exponential remainder
printed in the manuscript. The cutoff scale and constants are chosen before
dimension and before the two marks. -/
theorem actual_mixedSource_axis_averaged_cap_hit_source_rate
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree)
    {Q B β : ℝ} (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hnp : μ.minDegree < μ.maxDegree) (hB : 0 ≤ B) (hβ : 0 ≤ β)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (hχb : ∀ s, |χ s| ≤ 1) (hχR : ∀ s, 2 < |s| → χ s = 0) :
    ∃ (α : ℝ) (_hα : 0 < α) (γ c C : ℝ),
      0 < γ ∧ 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (e k : ℝ), |e| ≤ B → |k| ≤ B →
        (∫ J, sourceAxisAveragedCapHitProbability μ Q hQ hnp α χ hχ β
          (exponentialGridHorizon γ (n+1)) e k J
          ∂disorderLaw (n+1) μ.maxDegree) ≤
        C*(((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)+
          ((n+1 : ℕ) : ℝ)^(3-(μ.minDegree : ℝ)))+
          Real.exp (-c*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨α,hα,γ,Cε,Cη,Ccap,hγ,hCε,hCη,hCcap,hc₀,hEvent⟩ :=
    actual_mixedSource_axis_averaged_cap_hit_disorder_full
      μ hd hQ hQ1 hnp hB hβ χ hχ hχb hχR
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
  refine ⟨α,hα,γ,c,C,hγ,hc,hC,?_⟩
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

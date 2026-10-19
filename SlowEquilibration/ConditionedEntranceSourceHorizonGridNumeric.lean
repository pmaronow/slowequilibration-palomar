-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceGradientUniformMarks
public import SlowEquilibration.SphericalOverlapExponentialGridRates

/-! Quantitative exposure and grid-error bounds at the source's exponential
time horizon with a fixed short cell. -/
@[expose] public section
noncomputable section
open SlowEquilibration.SphericalOverlapExponential
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
open PhysicalHitting
set_option autoImplicit false
set_option maxHeartbeats 700000

def sourceExponentialDiscount (γ : ℝ) (N : ℕ) : ℝ≥0 :=
  ⟨Real.exp (-γ*(N : ℝ)),(Real.exp_pos _).le⟩

theorem sourceExponentialDiscount_pos (γ : ℝ) (N : ℕ) :
    0<sourceExponentialDiscount γ N := Real.exp_pos _

theorem source_exponential_exposure_floor (γ : ℝ) (hγ : 0≤γ)
    (N : ℕ) (T : ℝ≥0) (hT : 0<T) (hT1 : (T : ℝ)≤1) :
    0<Real.exp (-2)*(1-Real.exp (-(T : ℝ))) ∧
    Real.exp (-2)*(1-Real.exp (-(T : ℝ)))≤
      exposureFactor (sourceExponentialDiscount γ N : ℝ)
        (exponentialGridHorizon γ N) T := by
  have hθle : (sourceExponentialDiscount γ N : ℝ)≤1 := by
    change Real.exp (-γ*(N : ℝ))≤1
    apply Real.exp_le_one_iff.mpr
    nlinarith [Nat.cast_nonneg (α:=ℝ) N]
  have hθH : (sourceExponentialDiscount γ N : ℝ)*
      (exponentialGridHorizon γ N : ℝ)=1 := by
    change Real.exp (-γ*(N : ℝ))*Real.exp ((N : ℝ)*γ)=1
    rw [← Real.exp_add,show -γ*(N : ℝ)+(N : ℝ)*γ=0 by ring,Real.exp_zero]
  have hT0 : 0<(T : ℝ) := by exact_mod_cast hT
  have hθ0 : 0≤(sourceExponentialDiscount γ N : ℝ) := by positivity
  have hθT : (sourceExponentialDiscount γ N : ℝ)*(T : ℝ)≤(T : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hθle) hT0.le]
  have hθtotal : (sourceExponentialDiscount γ N : ℝ)*
      (((exponentialGridHorizon γ N + T : ℝ≥0) : ℝ))≤2 := by
    rw [NNReal.coe_add]
    nlinarith
  have hExp : Real.exp (-2)≤Real.exp (-(sourceExponentialDiscount γ N : ℝ)*
      (((exponentialGridHorizon γ N + T : ℝ≥0) : ℝ))) :=
    Real.exp_le_exp.mpr (by linarith)
  have hFactor : 0<1-Real.exp (-(T : ℝ)) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  constructor
  · exact mul_pos (Real.exp_pos _) hFactor
  · exact mul_le_mul_of_nonneg_right hExp hFactor.le

theorem source_exponential_grid_error_le (γ α : ℝ) (hγ : 0≤γ)
    (hγα : γ≤α^2/256) (N : ℕ) (T : ℝ≥0)
    (hT : 0<T) (hT18 : (T : ℝ)≤1/18) :
    (gridSize (exponentialGridHorizon γ N) T : ℝ)*
      (2*Real.exp (-(N : ℝ)*(α/12)^2/(16*(T : ℝ)))) ≤
      (2/(T : ℝ)+4)*Real.exp (-(N : ℝ)*α^2/256) := by
  let c := (α/12)^2/(16*(T : ℝ))
  have hTreal : 0<(T : ℝ) := by exact_mod_cast hT
  have hcDen : 0<16*(T : ℝ) := by positivity
  have hc : α^2/128≤c := by
    apply (le_div_iff₀ hcDen).mpr
    have hmul : 0≤α^2*(1-18*(T : ℝ)) :=
      mul_nonneg (sq_nonneg α) (by linarith)
    nlinarith
  have hgap : α^2/256≤c-γ := by linarith
  have hexp : Real.exp (-(N : ℝ)*(c-γ))≤
      Real.exp (-(N : ℝ)*α^2/256) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hgap)]
  have hcoef : 0≤2/(T : ℝ)+4 := by positivity
  have hb := exponentialGridError_bound T hT γ c hγ N
  have h := hb.trans (mul_le_mul_of_nonneg_left hexp hcoef)
  convert h using 1
  simp only [exponentialGridError,c]
  ring

theorem source_exposure_to_probability
    {P E R c c₀ : ℝ} (hc₀ : 0<c₀) (hcc₀ : c₀≤c) (hR : 0≤R)
    (hExposure : c*(P-E)≤R) :
    P≤E+R/c₀ := by
  by_cases hP : P≤E
  · have : 0≤R/c₀ := div_nonneg hR hc₀.le
    linarith
  · have hp : 0≤P-E := by linarith
    have hsmall : c₀*(P-E)≤R :=
      (mul_le_mul_of_nonneg_right hcc₀ hp).trans hExposure
    have hdiv : P-E≤R/c₀ := (le_div_iff₀ hc₀).mpr (by nlinarith [hsmall])
    linarith

end SlowEquilibration.ConditionedEntrance

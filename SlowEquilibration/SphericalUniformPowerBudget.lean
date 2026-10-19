-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCubePowerBudget

/-! Uniform vanishing of the actual finite tensor perturbation's power-GG
errors. The threshold is selected before the spin dimension, base law,
replica test and overlap cutoff. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalPositivePerturbation

open MeasureTheory ProbabilityTheory Set
open GaussianGGEnsemble GaussianPerturbationDeviation
open SphericalAging.FiniteModel
open scoped ProbabilityTheory Topology BigOperators

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every tested positive power present in the finite perturbation has
arbitrarily small actual averaged GG discrepancy, uniformly over all
ordinary unit-sphere Gibbs base laws and all dimensions and star tests. -/
theorem exists_uniform_cube_power_threshold (K : ℕ) {δ : ℝ} (hδ : 0<δ) :
    ∃ V : ℝ, 1≤V ∧ ∀ {N : ℕ} (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν]
      (v : ℝ), V≤v → ∀ (p : Fin K) (ε : ℝ) (m : ℕ),
      cubeMeanPowerDefect (K := K) ν v ε m (p.val+1)≤δ := by
  let A : ℝ := 4/(1/4:ℝ)^K
  have hA : 0<A := by dsimp [A];positivity
  let y : ℝ := min 1 (δ/(16*A))
  have hy : 0<y := by dsimp [y];exact lt_min (by norm_num) (by positivity)
  have hy1 : y≤1 := min_le_left _ _
  have hyδ : y≤δ/(16*A) := min_le_right _ _
  have hAy : 8*A*y≤δ/2 := by
    have ht := (le_div_iff₀ (by positivity : 0<16*A)).mp hyδ
    nlinarith
  let c : ℝ := 1+36*Real.exp (1/2)/y
  have hc : 0<c := by dsimp [c];positivity
  let V : ℝ := max 1 (2*A*c/δ)
  refine ⟨V,le_max_left _ _,?_⟩
  intro N ν _ v hV p ε m
  have hv1 : 1≤v := (le_max_left _ _).trans hV
  have hv : 0<v := lt_of_lt_of_le (by norm_num) hv1
  have hvc : 2*A*c/δ≤v := (le_max_right _ _).trans hV
  have hvc' : 2*A*c≤v*δ := (div_le_iff₀ hδ).mp hvc
  have hcv : A*(c/v)≤δ/2 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    calc
      A*(c/v)*2=(2*A*c)/v := by ring
      _≤δ := (div_le_iff₀ hv).mpr (by nlinarith)
  have hpK : p.val+1≤K := by omega
  have hp : (1/4:ℝ)^K≤(1/4:ℝ)^(p.val+1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hpK
  have hcoeff : 4/(1/4:ℝ)^(p.val+1)≤A := by
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hp
  have hbr : 0≤8*y+c/v := by positivity
  have hbound := cubeMeanPowerDefect_le ν hv p ε m hv hy hy1
  have heq : (4/(v^2*(1/4:ℝ)^(p.val+1)))*
      ((v^2+v^2)/(2*v)+8*v^2*y+36*Real.exp (1/2)*v/y)=
      (4/(1/4:ℝ)^(p.val+1))*(8*y+c/v) := by
    dsimp [c]
    field_simp [hv.ne',hy.ne',show (1/4:ℝ)^(p.val+1)≠0 by positivity]
    ring
  rw [heq] at hbound
  calc
    _ ≤ (4/(1/4:ℝ)^(p.val+1))*(8*y+c/v) := hbound
    _ ≤ A*(8*y+c/v) := mul_le_mul_of_nonneg_right hcoeff hbr
    _ = 8*A*y+A*(c/v) := by ring
    _ ≤ δ := by linarith

/-- Constants have exactly zero actual power-GG discrepancy. -/
theorem cubeMeanPowerDefect_zero {N K : ℕ} (ν : Measure (UnitSpin N))
    [IsProbabilityMeasure ν] {v : ℝ} (hv : 0≤v) (ε : ℝ) (m : ℕ) :
    cubeMeanPowerDefect (K := K) ν v ε m 0=0 := by
  let _ := ambientParameterizedGibbsKernel_markov (K := K) ν hv
  unfold cubeMeanPowerDefect cubePowerDefect
  simp only [powerDefect_zero,integral_zero]

end SlowEquilibration.SphericalPositivePerturbation

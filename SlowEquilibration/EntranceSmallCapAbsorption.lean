-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib

/-! A fixed small-cap radius absorbs the actual source-cutoff error terms
for every dimension and every finite-mixture minimum degree at least four. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance

def smallCapAbsorptionRadius (C : ℝ) : ℝ := 1/(24*(C+1))

theorem smallCapAbsorptionRadius_pos {C : ℝ} (hC : 0 < C) :
    0 < smallCapAbsorptionRadius C := by
  unfold smallCapAbsorptionRadius
  positivity

theorem smallCapAbsorptionRadius_le_quarter {C : ℝ} (hC : 0 < C) :
    smallCapAbsorptionRadius C ≤ 1/4 := by
  unfold smallCapAbsorptionRadius
  apply (div_le_iff₀ (by positivity : 0 < 24*(C+1))).mpr
  nlinarith

private theorem pow_le_cubic {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    {m : ℕ} (hm : 3 ≤ m) : x^m ≤ x^3 := by
  have he : m = 3+(m-3) := by omega
  calc
    x^m = x^3*x^(m-3) := by
      conv_lhs => rw [he, pow_add]
    _ ≤ x^3*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hx hx1) (pow_nonneg hx _)
    _ = x^3 := mul_one _

/-- One radius, chosen solely from the fixed physical coefficient `C`,
works for every ambient dimension, every degree at least four, and every
overlap inside the cap. The three monomials are the literal cutoff-error
orders from the conditioned source field. -/
theorem smallCapAbsorption {C : ℝ} (hC : 0 < C) (N d : ℕ)
    (hN : 1 ≤ N) (hd : 4 ≤ d) (r : ℝ)
    (hr : |r| ≤ smallCapAbsorptionRadius C) :
    C*((N : ℝ)*|r|^d+(N : ℝ)*|r|^(2*d-2)+
      Real.sqrt (N : ℝ)*|r|^(d-1)) ≤ (N : ℝ)*r^2/8 := by
  let ρ := smallCapAbsorptionRadius C
  let x := |r|
  have hρ0 : 0 < ρ := smallCapAbsorptionRadius_pos hC
  have hρ1 : ρ ≤ 1 := (smallCapAbsorptionRadius_le_quarter hC).trans (by norm_num)
  have hx0 : 0 ≤ x := abs_nonneg r
  have hxρ : x ≤ ρ := hr
  have hx1 : x ≤ 1 := hxρ.trans hρ1
  have hx3 : x^3 ≤ ρ*r^2 := by
    rw [←sq_abs]
    change x^3 ≤ ρ*x^2
    calc
      x^3 = x*x^2 := by ring
      _ ≤ ρ*x^2 := mul_le_mul_of_nonneg_right hxρ (sq_nonneg x)
  have hpow (m : ℕ) (hm : 3 ≤ m) : x^m ≤ ρ*r^2 :=
    (pow_le_cubic hx0 hx1 hm).trans hx3
  have hNr : 0 ≤ (N : ℝ) := by positivity
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hsqrt : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
    have hs := Real.sq_sqrt hNr
    have hs0 := Real.sqrt_nonneg (N : ℝ)
    nlinarith
  have h₁ : (N : ℝ)*x^d ≤ (N : ℝ)*ρ*r^2 :=
    (mul_le_mul_of_nonneg_left (hpow d (by omega)) hNr).trans_eq (by ring)
  have h₂ : (N : ℝ)*x^(2*d-2) ≤ (N : ℝ)*ρ*r^2 :=
    (mul_le_mul_of_nonneg_left (hpow (2*d-2) (by omega)) hNr).trans_eq (by ring)
  have h₃ : Real.sqrt (N : ℝ)*x^(d-1) ≤ (N : ℝ)*ρ*r^2 := by
    calc
      _ ≤ (N : ℝ)*x^(d-1) := mul_le_mul_of_nonneg_right hsqrt (pow_nonneg hx0 _)
      _ ≤ (N : ℝ)*ρ*r^2 := (mul_le_mul_of_nonneg_left (hpow (d-1) (by omega)) hNr).trans_eq (by ring)
  have hcoef : 3*C*ρ ≤ 1/8 := by
    dsimp [ρ,smallCapAbsorptionRadius]
    calc
      3*C*(1/(24*(C+1))) = (3*C)/(24*(C+1)) := by ring
      _ ≤ 1/8 := by
        apply (div_le_iff₀ (by positivity : 0 < 24*(C+1))).mpr
        nlinarith
  have hmass : 0 ≤ (N : ℝ)*r^2 := mul_nonneg hNr (sq_nonneg r)
  calc
    C*((N : ℝ)*|r|^d+(N : ℝ)*|r|^(2*d-2)+
      Real.sqrt (N : ℝ)*|r|^(d-1))
      ≤ C*(3*(N : ℝ)*ρ*r^2) := by
        change C*((N : ℝ)*x^d+(N : ℝ)*x^(2*d-2)+
          Real.sqrt (N : ℝ)*x^(d-1)) ≤ _
        exact mul_le_mul_of_nonneg_left (by linarith [h₁,h₂,h₃]) hC.le
    _ = (3*C*ρ)*((N : ℝ)*r^2) := by ring
    _ ≤ (1/8)*((N : ℝ)*r^2) := mul_le_mul_of_nonneg_right hcoef hmass
    _ = (N : ℝ)*r^2/8 := by ring

end SlowEquilibration.ConditionedEntrance

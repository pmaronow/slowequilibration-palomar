module
-- SPDX-License-Identifier: Apache-2.0

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-!
# The quantitative weighted-energy step of entropy–resolvent comparison

This file proves the actual scalar absorption argument in `eq:ent-energy`
and the square-root error estimate in `eq:ent-resolvent-bound`. Inputs are
explicit energy identities/inequalities; these results do not assume a
hitting-time bound, and do not assert the missing Feynman–Kac or Dirichlet
form calculus bridges.
-/

namespace SlowEquilibration.ConditionedEntrance
noncomputable section

/-- The tangent inequality for entropy, used when testing the genuine
resolvent equation by `log F`. -/
theorem entropy_tangent_line {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a - b) * Real.log b ≤
      a * Real.log a - b * Real.log b - (a - b) := by
  have ht := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at ht
  have hmul := mul_le_mul_of_nonneg_left ht ha.le
  have he : a * (b / a - 1) = b - a := by field_simp
  rw [he] at hmul
  nlinarith

/-- First exact Young bound used to retain and absorb the `lam A_h` term. -/
theorem sqrt_two_product_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (2 * a * b) ≤ a / 2 + b := by
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · nlinarith [sq_nonneg (a / 2 - b)]

/-- The source's weighted energy bound. The hypotheses are the tested
resolvent inequality and the entropy/Fisher bound, rather than the result
being established. -/
theorem resolvent_weighted_energy_bound {lam A B ε J H R : ℝ}
    (hlam : 0 < lam) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hε : 0 ≤ ε) (hJ : 0 ≤ J) (_hH : 0 ≤ H)
    (hFisher : J ≤ lam * H)
    (henergy : B + lam / 2 * A ≤ lam * R + lam / 2 * Real.sqrt (2 * ε * A) +
      Real.sqrt (2 * ε * J * B)) :
    B / lam ≤ 2 * R + ε + 2 * ε * H := by
  have hYoungA := sqrt_two_product_le hA hε
  have hYoungB := sqrt_two_product_le hB (mul_nonneg hε hJ)
  have hYoungA' : Real.sqrt (2 * ε * A) ≤ A / 2 + ε := by
    calc
      _ = Real.sqrt (2 * A * ε) := congrArg Real.sqrt (by ring)
      _ ≤ _ := hYoungA
  have hYoungB' : Real.sqrt (2 * ε * J * B) ≤ B / 2 + ε * J := by
    calc
      _ = Real.sqrt (2 * B * (ε * J)) := congrArg Real.sqrt (by ring)
      _ ≤ _ := hYoungB
  have h1 := mul_le_mul_of_nonneg_left hYoungA' (by positivity : 0 ≤ lam / 2)
  have h2 := mul_le_mul_of_nonneg_left hFisher hε
  apply (div_le_iff₀ hlam).2
  nlinarith

/-- The commutator error is of the same order as the manuscript's final
resolvent bound; its estimate uses the proved energy absorption above. -/
theorem resolvent_commutator_error_bound {lam A B ε J H R : ℝ}
    (hlam : 0 < lam) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hε : 0 ≤ ε) (hJ : 0 ≤ J) (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hFisher : J ≤ lam * H)
    (henergy : B + lam / 2 * A ≤ lam * R + lam / 2 * Real.sqrt (2 * ε * A) +
      Real.sqrt (2 * ε * J * B)) :
    Real.sqrt (2 * ε * J * B) / lam ≤
      2 * Real.sqrt (ε * H * (R + ε * (1 + H))) := by
  have he := resolvent_weighted_energy_bound hlam hA hB hε hJ hH hFisher henergy
  have hBbound : B ≤ 2 * lam * (R + ε * (1 + H)) := by
    have hh := (div_le_iff₀ hlam).mp he
    have hnon := mul_nonneg hlam.le hε
    nlinarith
  have h1 : (2 * ε * B) * J ≤ (2 * ε * B) * (lam * H) :=
    mul_le_mul_of_nonneg_left hFisher (by positivity)
  have h2 : (2 * ε * lam * H) * B ≤
      (2 * ε * lam * H) * (2 * lam * (R + ε * (1 + H))) :=
    mul_le_mul_of_nonneg_left hBbound (by positivity)
  have hlarge : 2 * ε * J * B ≤
      4 * lam ^ 2 * (ε * H * (R + ε * (1 + H))) := by nlinarith
  have hs1 := Real.sq_sqrt (show 0 ≤ 2 * ε * J * B by positivity)
  have hs2 := Real.sq_sqrt (show 0 ≤ ε * H * (R + ε * (1 + H)) by positivity)
  have hs1n := Real.sqrt_nonneg (2 * ε * J * B)
  have hs2n := Real.sqrt_nonneg (ε * H * (R + ε * (1 + H)))
  apply (div_le_iff₀ hlam).2
  have hsq : (Real.sqrt (2 * ε * J * B)) ^ 2 ≤
      (2 * Real.sqrt (ε * H * (R + ε * (1 + H))) * lam) ^ 2 := by
    rw [hs1, mul_pow, mul_pow, hs2]
    nlinarith only [hlarge]
  exact (sq_le_sq₀ hs1n (by positivity)).1 hsq

/-- The error simplification used when converting the Laplace-transform
estimate to a bound at a fixed time horizon. -/
theorem resolvent_root_error_simplification {ε H R : ℝ}
    (hε : 0 ≤ ε) (hH : 0 ≤ H) (hR : 0 ≤ R) :
    2 * Real.sqrt (ε * H * (R + ε * (1 + H))) ≤
      R + 3 * ε * (1 + H) := by
  have hs := Real.sq_sqrt (show 0 ≤ ε * H * (R + ε * (1 + H)) by positivity)
  have hn := Real.sqrt_nonneg (ε * H * (R + ε * (1 + H)))
  have ht : 0 ≤ ε * (1 + H) := by positivity
  have hprod : ε * H * (R + ε * (1 + H)) ≤
      ε * (1 + H) * (R + ε * (1 + H)) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    nlinarith
  nlinarith [sq_nonneg (R + 3 * ε * (1 + H)), sq_nonneg R]

end
end SlowEquilibration.ConditionedEntrance

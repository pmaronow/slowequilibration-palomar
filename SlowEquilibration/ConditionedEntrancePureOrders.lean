module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.ConditionedEntranceRegressionOrders
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! The singular pure-score case uses the explicit homogeneous regression
multipliers; its redundant radial coordinate is never inverted. -/

namespace SlowEquilibration.ConditionedEntrance
noncomputable section

/-- The source pure prefactor, written in the equivalent square-root form. -/
def purePrefactor (Q : ℝ) (p : ℕ) : ℝ := (Real.sqrt Q ^ p)⁻¹

def pureValueTheta (Q : ℝ) (p : ℕ) (r : ℝ) : ℝ := purePrefactor Q p * r ^ p

def pureTangentTheta (Q : ℝ) (p : ℕ) (r : ℝ) : ℝ :=
  purePrefactor Q p * r ^ (p - 1)

/-- Literal equality to the manuscript's `Q^(-p/2)` coefficient. -/
lemma purePrefactor_eq_rpow {Q : ℝ} (hQ : 0 ≤ Q) (p : ℕ) :
    purePrefactor Q p = Q ^ (-(p : ℝ) / 2) := by
  unfold purePrefactor
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hQ, ← Real.rpow_neg hQ]
  congr 1
  ring

lemma pureValueTheta_hasDerivAt (Q : ℝ) (p : ℕ) (r : ℝ) :
    HasDerivAt (pureValueTheta Q p)
      (purePrefactor Q p * (p : ℝ) * r ^ (p - 1)) r := by
  unfold pureValueTheta
  convert (hasDerivAt_pow p r).const_mul (purePrefactor Q p) using 1
  ring

lemma pureTangentTheta_hasDerivAt (Q : ℝ) (p : ℕ) (r : ℝ) :
    HasDerivAt (pureTangentTheta Q p)
      (purePrefactor Q p * ((p - 1 : ℕ) : ℝ) * r ^ (p - 2)) r := by
  unfold pureTangentTheta
  convert (hasDerivAt_pow (p - 1) r).const_mul (purePrefactor Q p) using 1
  rw [show p - 1 - 1 = p - 2 by omega]
  ring

/-- A single strictly positive constant for all pure-case source orders. -/
def pureOrderConstant (Q : ℝ) (p : ℕ) : ℝ :=
  1 + |purePrefactor Q p| + |purePrefactor Q p * (p : ℝ)| +
    |purePrefactor Q p * ((p - 1 : ℕ) : ℝ)|

lemma pureOrderConstant_pos (Q : ℝ) (p : ℕ) : 0 < pureOrderConstant Q p := by
  unfold pureOrderConstant
  positivity

/-- All three source vanishing orders in the pure case, with radial
multiplier identically zero and no inversion of its singular score matrix. -/
theorem pure_regression_orders (Q : ℝ) (p : ℕ) (r : ℝ) :
    |pureValueTheta Q p r| ≤ pureOrderConstant Q p * |r| ^ p ∧
    |purePrefactor Q p * (p : ℝ) * r ^ (p - 1)| + |pureTangentTheta Q p r| ≤
      pureOrderConstant Q p * |r| ^ (p - 1) ∧
    |purePrefactor Q p * ((p - 1 : ℕ) : ℝ) * r ^ (p - 2)| ≤
      pureOrderConstant Q p * |r| ^ (p - 2) := by
  simp only [pureValueTheta, pureTangentTheta, abs_mul, abs_pow]
  have h1 := abs_nonneg (purePrefactor Q p)
  have h2 := abs_nonneg (purePrefactor Q p * (p : ℝ))
  have h3 := abs_nonneg (purePrefactor Q p * ((p - 1 : ℕ) : ℝ))
  have hp1 := pow_nonneg (abs_nonneg r) p
  have hp2 := pow_nonneg (abs_nonneg r) (p - 1)
  have hp3 := pow_nonneg (abs_nonneg r) (p - 2)
  unfold pureOrderConstant
  simp only [abs_mul] at *
  constructor
  · nlinarith
  constructor <;> nlinarith

end
end SlowEquilibration.ConditionedEntrance

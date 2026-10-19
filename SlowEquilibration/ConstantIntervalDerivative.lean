module
-- SPDX-License-Identifier: Apache-2.0

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Tactic

@[expose] public section

/-! # Genuine derivatives of closed-interval plateaus -/
namespace SlowEquilibration
open Set
open scoped ContDiff

/-- Constancy on a nontrivial closed interval forces the ordinary
ambient derivative to vanish even at either endpoint. -/
theorem deriv_eq_zero_of_constant_Icc {h : ℝ → ℝ} {a b c x : ℝ}
    (hab : a < b) (hx : x ∈ Icc a b) (hh : DifferentiableAt ℝ h x)
    (hplateau : ∀ r ∈ Icc a b, h r = c) : deriv h x = 0 := by
  calc
    deriv h x = derivWithin h (Icc a b) x := (hh.derivWithin (uniqueDiffOn_Icc hab x hx)).symm
    _ = derivWithin (fun _ : ℝ => c) (Icc a b) x :=
      derivWithin_congr hplateau (hplateau x hx)
    _ = 0 := by simp

end SlowEquilibration

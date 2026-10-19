module
-- SPDX-License-Identifier: Apache-2.0

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Tactic

@[expose] public section

/-! # Genuine directional derivative of a normalized scalar moment -/
namespace SlowEquilibration
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of a literal quotient moment, with its actual Frechet
normalization obtained by the ordinary product and inverse chain rules. -/
theorem scalar_normalized_fderiv_apply (d n : E → ℝ) (x v : E)
    (hd : DifferentiableAt ℝ d x) (hn : DifferentiableAt ℝ n x) (hp : d x ≠ 0) :
    (fderiv ℝ (fun y => (d y)⁻¹*n y) x) v =
      (d x)⁻¹*((fderiv ℝ n x) v)+n x*(-(d x^2)⁻¹*((fderiv ℝ d x) v)) := by
  have hi := (hasDerivAt_inv hp).comp_hasFDerivAt x hd.hasFDerivAt
  have hq := hi.mul hn.hasFDerivAt
  have he := congrArg (fun L : E →L[ℝ] ℝ => L v) hq.fderiv
  simp only [Pi.mul_apply, Function.comp_def, _root_.add_apply, _root_.smul_apply, smul_eq_mul] at he
  convert! he using 1

end SlowEquilibration

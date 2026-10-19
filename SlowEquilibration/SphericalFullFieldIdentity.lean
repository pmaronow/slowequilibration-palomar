-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalEffectiveField
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Order.Interval.Set.Infinite

/-! Ball restriction faithfully represents the complete mixed polynomial,
including its radial information. This is stronger than the spherical
restriction used by the diffusion. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalEffectiveField

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel
open scoped Topology NNReal ENNReal BigOperators

set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N P : ℕ}

theorem tensorMonomial_smul {p : ℕ} (x : Vector N)
    (I : SphericalAging.FiniteModel.TensorIndex N p) (r : ℝ) :
    SphericalAging.FiniteModel.tensorMonomial (r • x) I =
      r^p*SphericalAging.FiniteModel.tensorMonomial x I := by
  simp only [SphericalAging.FiniteModel.tensorMonomial, PiLp.smul_apply, smul_eq_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem blockField_smul (p : Degree P) (J : Disorder N P) (x : Vector N) (r : ℝ) :
    blockField p J (r • x) = r^p.val.val*blockField p J x := by
  simp only [blockField, SphericalAging.FiniteModel.Hamiltonian, tensorMonomial_smul]
  simp_rw [show ∀ I : SphericalAging.FiniteModel.TensorIndex N p.val.val,
    J p I*(r^p.val.val*SphericalAging.FiniteModel.tensorMonomial x I) =
      r^p.val.val*(J p I*SphericalAging.FiniteModel.tensorMonomial x I) from fun I => by ring]
  rw [← Finset.mul_sum]
  ring

/-- The literal restriction of a mixed polynomial to any line. -/
def linePolynomial (c : Degree P → ℝ) (J : Disorder N P) (x : Vector N) : Polynomial ℝ :=
  ∑ p : Degree P, Polynomial.C (Real.sqrt (c p)*blockField p J x)*Polynomial.X^p.val.val

@[simp] theorem linePolynomial_eval (c : Degree P → ℝ) (J : Disorder N P)
    (x : Vector N) (r : ℝ) :
    (linePolynomial c J x).eval r = field c J (r • x) := by
  simp only [linePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, field, blockField_smul]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Equality on the fixed compact ball implies equality of the actual
polynomials everywhere, by their literal one-variable line polynomials. -/
theorem field_eq_of_ball_eq (c : Degree P → ℝ) (J K : Disorder N P)
    (h : ∀ x ∈ fieldBall N, field c J x = field c K x) : field c J = field c K := by
  funext x
  let R := linePolynomial c J x - linePolynomial c K x
  let a : ℝ := (Real.sqrt N+1)/(‖x‖+1)
  have ha : 0 < a := div_pos (by positivity) (by positivity)
  have hroots : Ioo (0:ℝ) a ⊆ {r | R.IsRoot r} := by
    intro r hr
    have hx : r • x ∈ fieldBall N := by
      simp only [fieldBall, Metric.mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos hr.1]
      have ha' : r*(‖x‖+1) < Real.sqrt N+1 :=
        (lt_div_iff₀ (by positivity)).mp hr.2
      nlinarith [norm_nonneg x, hr.1]
    change R.eval r=0
    simp only [R, Polynomial.eval_sub, linePolynomial_eval]
    rw [h (r • x) hx, sub_self]
  have hR : R=0 := Polynomial.eq_zero_of_infinite_isRoot R ((Set.Ioo_infinite ha).mono hroots)
  have heval := congrArg (fun p : Polynomial ℝ => p.eval 1) hR
  simpa only [R, Polynomial.eval_sub, linePolynomial_eval, one_smul, Polynomial.eval_zero,
    sub_eq_zero] using heval

/-- Equality of compressed full fields is equivalent to equality of the
complete polynomial functions, not merely their spherical restrictions. -/
theorem full_project_eq_iff (c : Degree P → ℝ) (J K : Disorder N P) :
    project c (fieldBall N) J = project c (fieldBall N) K ↔ field c J = field c K := by
  constructor
  · intro h
    apply field_eq_of_ball_eq c J K
    intro x hx
    exact congrArg (fun H : FullSpace c => H.val ⟨x,hx⟩) h
  · intro h
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    exact congrFun h x.val

/-- The constructed canonical lift represents the full polynomial at
all ambient points. No ambient-field identity is an extra assumption. -/
theorem full_lift_project (c : Degree P → ℝ) (J : Disorder N P) :
    field c (lift c (fieldBall N) (project c (fieldBall N) J)) = field c J :=
  (full_project_eq_iff c _ J).mp (project_lift c (fieldBall N) _)

end SlowEquilibration.SphericalEffectiveField

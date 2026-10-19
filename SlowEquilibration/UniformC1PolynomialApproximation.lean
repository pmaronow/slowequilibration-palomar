-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.MeanValue

/-! Actual simultaneous polynomial approximation of a scalar cutoff and its
first derivative. This lets smooth overlap cutoffs be approximated by genuine
finite tensor Hamiltonians without assuming stationarity of the limiting flow. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.UniformC1PolynomialApproximation
open Set Polynomial
open scoped BigOperators
set_option maxHeartbeats 400000

/-- Explicit polynomial primitive with value zero at the origin. -/
def primitive (p : ℝ[X]) : ℝ[X] :=
  ∑ n∈p.support, Polynomial.monomial (n+1) (p.coeff n/((n+1:ℕ):ℝ))

lemma primitive_derivative (p : ℝ[X]) : (primitive p).derivative=p := by
  calc
    _ = ∑ n∈p.support, Polynomial.monomial n (p.coeff n) := by
      rw [primitive,Polynomial.derivative_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Polynomial.derivative_monomial,Nat.add_sub_cancel,
        div_mul_cancel₀ _ (by exact_mod_cast (Nat.succ_ne_zero n))]
    _ = p := by simpa only [Polynomial.sum_def] using Polynomial.sum_monomial_eq p

lemma primitive_eval_zero (p : ℝ[X]) : (primitive p).eval 0=0 := by
  simp only [primitive,Polynomial.eval_finsetSum]
  apply Finset.sum_eq_zero
  intro n hn
  simp

/-- A literal C¹ scalar cutoff has actual polynomial approximants on every
fixed compact interval, with the constant value and both uniform errors
controlled simultaneously. No approximation oracle is an input. -/
theorem exists_polynomial_C1 (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    {R ε : ℝ} (hR : 0<R) (hε : 0<ε) :
    ∃ p : ℝ[X], p.eval 0=f 0 ∧ ∀ x∈Icc (-R) R,
      |f x-p.eval x|≤ε ∧ |deriv f x-p.derivative.eval x|≤ε := by
  let S:=max (1:ℝ) R
  let δ:=ε/S
  have hS : 0<S := (by norm_num : (0:ℝ)<1).trans_le (le_max_left _ _)
  have hδ : 0<δ := div_pos hε hS
  have hδε : δ≤ε := div_le_self hε.le (le_max_left _ _)
  obtain ⟨q,hq⟩:=exists_polynomial_near_of_continuousOn (-R) R (deriv f)
    hf.continuous_deriv_one.continuousOn δ hδ
  let p:=primitive q+Polynomial.C (f 0)
  have hp0 : p.eval 0=f 0 := by simp [p,primitive_eval_zero]
  have hpd : p.derivative=q := by simp [p,primitive_derivative]
  have hd : Differentiable ℝ f := (contDiff_one_iff_deriv.mp hf).1
  let g:=fun x : ℝ => f x-p.eval x
  have hg (x : ℝ) : HasDerivAt g (deriv f x-p.derivative.eval x) x :=
    (hd x).hasDerivAt.sub (p.hasDerivAt x)
  have hbound : ∀ x∈Icc (-R) R, ‖deriv g x‖≤δ := by
    intro x hx
    rw [(hg x).deriv,Real.norm_eq_abs,hpd,abs_sub_comm]
    exact (hq x hx).le
  have h0 : (0:ℝ)∈Icc (-R) R := ⟨by linarith, hR.le⟩
  have hg0 : g 0=0 := by simp only [g,hp0,sub_self]
  refine ⟨p,hp0,?_⟩
  intro x hx
  have hm:=Convex.norm_image_sub_le_of_norm_deriv_le
    (fun y _ => (hg y).differentiableAt) hbound (convex_Icc (-R) R) h0 hx
  have hxR : |x|≤R := abs_le.mpr hx
  have hδR : δ*R≤ε := by
    calc
      _ ≤ δ*S := mul_le_mul_of_nonneg_left (le_max_right _ _) hδ.le
      _ = ε := by dsimp only [δ];field_simp
  constructor
  · rw [hg0,sub_zero,Real.norm_eq_abs,sub_zero,Real.norm_eq_abs] at hm
    exact hm.trans ((mul_le_mul_of_nonneg_left hxR hδ.le).trans hδR)
  · rw [hpd,abs_sub_comm]
    exact (hq x hx).le.trans hδε

end SlowEquilibration.UniformC1PolynomialApproximation

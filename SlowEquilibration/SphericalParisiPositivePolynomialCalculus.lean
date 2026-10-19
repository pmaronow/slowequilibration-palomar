-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiLabeledCovariance
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add

@[expose] public section

/-! Analytic facts for the actual finite positive-coefficient covariance.
The derivative, interval monotonicity, and degenerate zero-field case
are proved directly from its literal ordered-tensor polynomial. -/

namespace SlowEquilibration.SphericalParisiPositivePolynomialCalculus
noncomputable section
open Set SphericalParisiLabeledCovariance
open scoped BigOperators
set_option maxHeartbeats 500000
variable {σ : Type*} [Fintype σ]

theorem xi_hasDerivAt (d : σ → ℕ) (c : σ → ℝ) (r : ℝ) :
    HasDerivAt (xi d c) (xi1 d c r) r := by
  unfold xi xi1
  simpa only [mul_one,mul_assoc,Pi.pow_apply,id_eq] using
    HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => ((hasDerivAt_id r).pow (d i)).const_mul (c i))

theorem xi_continuous (d : σ → ℕ) (c : σ → ℝ) : Continuous (xi d c) :=
  continuous_iff_continuousAt.mpr (fun r => (xi_hasDerivAt d c r).continuousAt)

def xi2 (d : σ → ℕ) (c : σ → ℝ) (r : ℝ) : ℝ :=
  ∑ i,c i*(d i : ℝ)*((d i-1 : ℕ) : ℝ)*r^(d i-2)

theorem xi1_hasDerivAt (d : σ → ℕ) (c : σ → ℝ) (r : ℝ) :
    HasDerivAt (xi1 d c) (xi2 d c r) r := by
  unfold xi1 xi2
  simpa only [mul_one,mul_assoc,Pi.pow_apply,id_eq,Nat.sub_sub] using
    HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => ((hasDerivAt_id r).pow (d i-1)).const_mul (c i*(d i : ℝ)))

theorem xi1_continuous (d : σ → ℕ) (c : σ → ℝ) : Continuous (xi1 d c) :=
  continuous_iff_continuousAt.mpr (fun r => (xi1_hasDerivAt d c r).continuousAt)

theorem xi2_continuous (d : σ → ℕ) (c : σ → ℝ) : Continuous (xi2 d c) := by
  unfold xi2
  fun_prop

theorem xi_monotoneOn_unitInterval (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0 ≤ c i) : MonotoneOn (xi d c) (Icc (0 : ℝ) 1) := by
  intro r hr s _ hrs
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.1 hrs _) (hc i)

theorem xi1_zero_nonnegative (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0 ≤ c i) : 0 ≤ xi1 d c 0 :=
  xi1_nonnegative d c hc le_rfl

theorem positive_degree_coefficients_zero_of_xi1_one_zero
    (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i,0 ≤ c i)
    (hz : xi1 d c 1=0) : ∀ i,0 < d i → c i=0 := by
  have hs : (∑ i,c i*(d i : ℝ))=0 := by simpa [xi1] using hz
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ Finset.univ) => mul_nonneg (hc i) (Nat.cast_nonneg (d i)))).mp hs
  intro i hi
  exact (mul_eq_zero.mp (hall i (Finset.mem_univ i))).resolve_right
    (Nat.cast_ne_zero.mpr hi.ne')

theorem coefficients_zero_of_xi1_one_zero (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0 ≤ c i) (hd : ∀ i,1 ≤ d i) (hz : xi1 d c 1=0) :
    c=0 := by
  funext i
  exact positive_degree_coefficients_zero_of_xi1_one_zero d c hc hz i
    (lt_of_lt_of_le (by norm_num) (hd i))

end
end SlowEquilibration.SphericalParisiPositivePolynomialCalculus

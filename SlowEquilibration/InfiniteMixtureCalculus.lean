-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.InfiniteMixture
public import SlowEquilibration.Thresholds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Termwise derivative and endpoint continuity theorems for the literal
infinite covariance series, derived from the source summability assumption. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.InfiniteMixture
open Set Filter
open scoped Topology ENNReal
variable (μ : InfiniteMixture)

/-- The actual differentiated coefficient series, valid at both endpoints. -/
def jet (k : ℕ) (r : ℝ) : ℝ :=
  ∑' p : ℕ, μ.coeff p*(p.descFactorial k:ℝ)*r^(p-k)

lemma jet_term_bound {k : ℕ} {r : ℝ} (hr : |r|≤1) (p : ℕ) :
    ‖μ.coeff p*(p.descFactorial k:ℝ)*r^(p-k)‖ ≤ (p:ℝ)^k*μ.coeff p := by
  rw [norm_mul,norm_mul,Real.norm_eq_abs,abs_of_nonneg (μ.nonneg p),
    Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),norm_pow,Real.norm_eq_abs]
  calc
    _ ≤ μ.coeff p*(p.descFactorial k:ℝ)*1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ (abs_nonneg _) hr) (mul_nonneg (μ.nonneg _) (Nat.cast_nonneg _))
    _ ≤ (p:ℝ)^k*μ.coeff p := by
      have h : (p.descFactorial k:ℝ) ≤ (p:ℝ)^k := by exact_mod_cast Nat.descFactorial_le_pow p k
      nlinarith [μ.nonneg p]

theorem summable_jet {k : ℕ} (hk : k≤5) {r : ℝ} (hr : |r|≤1) :
    Summable (fun p : ℕ => μ.coeff p*(p.descFactorial k:ℝ)*r^(p-k)) :=
  .of_norm_bounded (μ.summable_moment hk) (μ.jet_term_bound hr)

/-- Every displayed derivative series converges uniformly on the closed
unit interval, including the fifth derivative. -/
theorem jet_tendstoUniformlyOn {k : ℕ} (hk : k≤5) :
    TendstoUniformlyOn (fun s : Finset ℕ => fun r =>
      ∑ p∈s, μ.coeff p*(p.descFactorial k:ℝ)*r^(p-k)) (μ.jet k) atTop (Icc (-1:ℝ) 1) := by
  exact tendstoUniformlyOn_tsum (μ.summable_moment hk)
    (fun p r hr => μ.jet_term_bound (abs_le.mpr hr) p)

theorem continuousOn_jet {k : ℕ} (hk : k≤5) : ContinuousOn (μ.jet k) (Icc (-1:ℝ) 1) := by
  exact continuousOn_tsum
    (fun p => (continuous_const.mul (continuous_id.pow (p-k))).continuousOn)
    (μ.summable_moment hk) (fun p r hr => μ.jet_term_bound (abs_le.mpr hr) p)

lemma hasDerivAt_jet_term (k p : ℕ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => μ.coeff p*(p.descFactorial k:ℝ)*r^(p-k))
      (μ.coeff p*(p.descFactorial (k+1):ℝ)*r^(p-(k+1))) r := by
  convert (hasDerivAt_pow (p-k) r).const_mul (μ.coeff p*(p.descFactorial k:ℝ)) using 1
  rw [Nat.descFactorial_succ,Nat.cast_mul]
  rw [show p-(k+1)=p-k-1 by omega]
  ring

/-- The infinite series can genuinely be differentiated termwise in the
interior through order five. -/
theorem hasDerivAt_jet {k : ℕ} (hk : k<5) {r : ℝ} (hr : r∈Ioo (-1:ℝ) 1) :
    HasDerivAt (μ.jet k) (μ.jet (k+1) r) r := by
  exact hasDerivAt_tsum_of_isPreconnected (μ.summable_moment (show k+1≤5 by omega))
    isOpen_Ioo (convex_Ioo (-1:ℝ) 1).isPreconnected
    (fun p x _ => μ.hasDerivAt_jet_term k p x)
    (fun p x hx => μ.jet_term_bound (abs_lt.mpr hx).le p)
    (show (0:ℝ)∈Ioo (-1:ℝ) 1 by norm_num)
    (μ.summable_jet (by omega) (by norm_num)) hr

@[simp] theorem jet_zero : μ.jet 0=μ.xi := by
  funext r
  simp [jet,xi]

theorem hasDerivAt_xi {r : ℝ} (hr : r∈Ioo (-1:ℝ) 1) :
    HasDerivAt μ.xi (μ.jet 1 r) r := by simpa using μ.hasDerivAt_jet (k := 0) (by omega) hr

/-- On the interior these series are the literal iterated derivatives of ξ. -/
theorem iteratedDeriv_eq_jet {k : ℕ} (hk : k≤5) {r : ℝ} (hr : r∈Ioo (-1:ℝ) 1) :
    iteratedDeriv k μ.xi r=μ.jet k r := by
  induction k generalizing r with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k μ.xi =ᶠ[𝓝 r] μ.jet k := by
      filter_upwards [isOpen_Ioo.mem_nhds hr] with x hx
      exact ih (by omega) hx
    rw [he.deriv_eq]
    exact (μ.hasDerivAt_jet (by omega) hr).deriv

theorem jet_nonneg {k : ℕ} {r : ℝ} (hr : 0≤r) : 0≤μ.jet k r :=
  tsum_nonneg (fun p => mul_nonneg (mul_nonneg (μ.nonneg _) (Nat.cast_nonneg _)) (pow_nonneg hr _))

theorem abs_jet_le_one {k : ℕ} (hk : k≤5) {r : ℝ} (hr : |r|≤1) : |μ.jet k r|≤μ.jet k 1 := by
  rw [← Real.norm_eq_abs]
  apply (norm_tsum_le_tsum_norm (μ.summable_jet hk hr).norm).trans
  apply ((μ.summable_jet hk hr).norm).tsum_le_tsum
  · intro p
    simp only [norm_mul,norm_pow,Real.norm_eq_abs,abs_of_nonneg (μ.nonneg p),
      abs_of_nonneg (show (0:ℝ)≤(p.descFactorial k:ℝ) from Nat.cast_nonneg _),one_pow,mul_one]
    exact mul_le_of_le_one_right (mul_nonneg (μ.nonneg _) (Nat.cast_nonneg _))
      (pow_le_one₀ (abs_nonneg _) hr)
  · exact μ.summable_jet hk (by norm_num)

end SlowEquilibration.InfiniteMixture

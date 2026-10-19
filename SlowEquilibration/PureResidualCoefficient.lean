-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureRootLocation
public import SlowEquilibration.PureStationarity
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

namespace SlowEquilibration.PureStationarity

noncomputable section
open Set PureScalarStatic
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- Literal pure residual covariance at overlap one. -/
def pureResidualAtOne (p : ℕ) (Q : ℝ) : ℝ :=
  1-Q^p-(p : ℝ)*Q^(p-1)*(1-Q)

/-- Exact finite weighted remainder identity of the actual monomial. -/
theorem pureResidualAtOne_sum (n : ℕ) (Q : ℝ) :
    pureResidualAtOne (n+2) Q =
      (1-Q)^2*(∑ k ∈ Finset.range (n+1), ((k : ℝ)+1)*Q^k) := by
  induction n with
  | zero => norm_num [pureResidualAtOne]; ring
  | succ n ih =>
    have hrec : pureResidualAtOne (n+3) Q = pureResidualAtOne (n+2) Q+
        ((n : ℝ)+2)*Q^(n+1)*(1-Q)^2 := by
      simp only [pureResidualAtOne, show n+3-1 = n+2 by omega,
        show n+2-1 = n+1 by omega, Nat.cast_add, Nat.cast_ofNat, pow_succ]
      ring
    rw [show n+1+2 = n+3 by omega, hrec, ih,
      Finset.sum_range_succ (n := n+1)]
    push_cast
    ring

theorem sum_range_successor_real (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), ((k : ℝ)+1)) = ((n : ℝ)+2)*((n : ℝ)+1)/2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The genuine pure residual is bounded using its exact finite weighted
monomial remainder, with no assumed Taylor inequality. -/
theorem pureResidualAtOne_upper (p : ℕ) (hp : 2 ≤ p) {Q : ℝ}
    (hQ : Q ∈ Icc (0 : ℝ) 1) :
    pureResidualAtOne p Q ≤ ((p : ℝ)*((p : ℝ)-1)/2)*(1-Q)^2 := by
  let n := p-2
  have hpEq : p = n+2 := by dsimp [n]; omega
  rw [hpEq, pureResidualAtOne_sum]
  have hsum : (∑ k ∈ Finset.range (n+1), ((k : ℝ)+1)*Q^k) ≤
      ∑ k ∈ Finset.range (n+1), ((k : ℝ)+1) := by
    apply Finset.sum_le_sum
    intro k hk
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hQ.1 hQ.2)
      (by positivity : 0 ≤ (k : ℝ)+1)
  calc
    _ ≤ (1-Q)^2*(∑ k ∈ Finset.range (n+1), ((k : ℝ)+1)) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = _ := by rw [sum_range_successor_real]; push_cast; ring

/-- A strict exact rational enclosure of the exponential constant needed
in the source residual estimate. Four genuine Taylor terms suffice. -/
theorem exp_half_lt_fiftyThree_thirtySeconds : Real.exp (1/2 : ℝ) < (53/32 : ℝ) := by
  have h := Real.exp_bound' (x := (1/2 : ℝ)) (n := 4)
    (by norm_num) (by norm_num) (by norm_num)
  have hrat : (∑ m ∈ Finset.range 4, (1/2 : ℝ)^m/(m.factorial : ℝ))+
      (1/2 : ℝ)^4*(4+1)/(((4 : ℕ).factorial : ℝ)*4) < (53/32 : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact h.trans_lt hrat

theorem inverseOverlap_pow_lt_exp_half (p : ℕ) (hp : 4 ≤ p) {Q : ℝ}
    (hQ : Q ∈ Ioo (staticOverlap (zParameter p (by omega))) 1) :
    (1/Q)^(p-2) < Real.exp (1/2 : ℝ) := by
  let z := zParameter p (by omega)
  have hz : 0 < z := (zParameter_spec p (by omega)).1
  have hq0 : 0 < Q := (staticOverlap_mem_Ioo hz).1.trans hQ.1
  have hpR : (4 : ℝ) ≤ p := by exact_mod_cast hp
  have hn : ((p-2 : ℕ) : ℝ) = (p : ℝ)-2 := by rw [Nat.cast_sub (by omega : 2 ≤ p)]; norm_num
  have hn0 : (0 : ℝ) < (p-2 : ℕ) := by rw [hn]; linarith
  have hzbound : 2*(((p-2 : ℕ) : ℝ)) < z := by rw [hn]; exact zParameter_gt_twice_shifted p hp
  let θ := 1/Q-1
  have hθ : θ < 1/z := by
    have hθEq : θ = (1-Q)/Q := by dsimp [θ]; field_simp [hq0.ne']
    rw [hθEq]
    apply (div_lt_div_iff₀ hq0 hz).mpr
    have h := (div_lt_iff₀ (by linarith : 0 < 1+z)).mp hQ.1
    nlinarith
  have hscale : ((p-2 : ℕ) : ℝ)*θ < (1/2 : ℝ) := by
    have hm := mul_lt_mul_of_pos_left hθ hn0
    have hdiv : (((p-2 : ℕ) : ℝ))/z < (1/2 : ℝ) :=
      (div_lt_div_iff₀ hz (by norm_num)).mpr (by nlinarith)
    rw [mul_one_div] at hm
    exact hm.trans hdiv
  have hplus : 1+θ = 1/Q := by dsimp [θ]; ring
  have hplus0 : 0 ≤ 1+θ := by rw [hplus]; positivity
  have hpow := pow_le_pow_left₀ hplus0
    (by simpa only [add_comm] using Real.add_one_le_exp θ) (p-2)
  rw [hplus, ← Real.exp_nat_mul] at hpow
  exact hpow.trans_lt (Real.exp_lt_exp.mpr hscale)

/-- The manuscript's strict residual coefficient bound, from the genuine
pure root equation and the proved quantitative root location. -/
theorem pureResidualAtOne_bound_of_root (p : ℕ) (hp : 4 ≤ p) {β Q : ℝ}
    (hQ : Q ∈ Ioo (staticOverlap (zParameter p (by omega))) 1)
    (hroot : β^2*(p : ℝ)*(1+zParameter p (by omega))*Q^(p-2)*(1-Q)^2 = 1) :
    β^2*pureResidualAtOne p Q < (159/320 : ℝ) := by
  let z := zParameter p (by omega)
  have hz : 0 < z := (zParameter_spec p (by omega)).1
  have hq0 : 0 < Q := (staticOverlap_mem_Ioo hz).1.trans hQ.1
  have hpR : (4 : ℝ) ≤ p := by exact_mod_cast hp
  have hupper := mul_le_mul_of_nonneg_left (pureResidualAtOne_upper p (by omega)
    ⟨hq0.le, hQ.2.le⟩) (sq_nonneg β)
  have hcore : β^2*(p : ℝ)*Q^(p-2)*(1-Q)^2 = 1/(1+z) := by
    apply (eq_div_iff (by linarith : 1+z ≠ 0)).mpr
    calc
      (β^2*(p : ℝ)*Q^(p-2)*(1-Q)^2)*(1+z) =
          β^2*(p : ℝ)*(1+z)*Q^(p-2)*(1-Q)^2 := by ring
      _ = 1 := hroot
  have hEq : β^2*((p : ℝ)*((p : ℝ)-1)/2)*(1-Q)^2 =
      (((p : ℝ)-1)/(2*(1+z)))*(1/Q)^(p-2) := by
    rw [div_pow]
    simp only [one_pow, mul_one_div]
    apply (eq_div_iff (pow_ne_zero (p-2) hq0.ne')).mpr
    calc
      _ = ((p : ℝ)-1)/2*(β^2*(p : ℝ)*Q^(p-2)*(1-Q)^2) := by ring
      _ = _ := by
        rw [hcore]
        field_simp [show 1+z ≠ 0 by linarith]
  have hcoeff : ((p : ℝ)-1)/(2*(1+z)) < (3/10 : ℝ) := by
    have hzb := zParameter_gt_twice_shifted p hp
    apply (div_lt_div_iff₀ (by linarith : 0 < 2*(1+z)) (by norm_num)).mpr
    change 2*((p : ℝ)-2) < z at hzb
    nlinarith
  calc
    β^2*pureResidualAtOne p Q ≤ β^2*(((p : ℝ)*((p : ℝ)-1)/2)*(1-Q)^2) := hupper
    _ = (((p : ℝ)-1)/(2*(1+z)))*(1/Q)^(p-2) := by rw [← hEq]; ring
    _ < (3/10 : ℝ)*(1/Q)^(p-2) :=
      mul_lt_mul_of_pos_right hcoeff (pow_pos (div_pos (by norm_num) hq0) _)
    _ < (3/10 : ℝ)*Real.exp (1/2 : ℝ) :=
      mul_lt_mul_of_pos_left (inverseOverlap_pow_lt_exp_half p hp hQ) (by norm_num)
    _ < (3/10 : ℝ)*(53/32 : ℝ) :=
      mul_lt_mul_of_pos_left exp_half_lt_fiftyThree_thirtySeconds (by norm_num)
    _ = (159/320 : ℝ) := by norm_num

/-- The residual bound holds for the actual canonical pure-model law;
the genuine root equation is derived internally from its contact geometry. -/
theorem canonical_pure_residual_bound (p : ℕ) (hp : 4 ≤ p) {β : ℝ}
    (hβ : Thresholds.staticThreshold (fun r : ℝ => r^p) < β) :
    ∃ x ∈ Ioo (0 : ℝ) 1,
      ∃ Q ∈ Ioo (staticOverlap (zParameter p (by omega))) 1,
        (CSParisiMeasure.canonicalMinimizer (FiniteMixture.pure p (by omega) 1 (by positivity)) β).law =
          CrisantiSommers.twoAtom x Q ∧ β^2*pureResidualAtOne p Q < (159/320 : ℝ) := by
  obtain ⟨x, hx, Q, hQ, hlaw, hxformula, hroot, hcurv, hpositive⟩ :=
    canonical_pure_parameters p (by omega) hβ
  exact ⟨x, hx, Q, hQ, hlaw, pureResidualAtOne_bound_of_root p hp hQ hroot⟩

def pureResidualCoefficient (p : ℕ) (β a : ℝ) : ℝ := β^2*pureResidualAtOne p (a^2)

theorem pureResidualCoefficient_eq (p : ℕ) (hp : 2 ≤ p) (β a : ℝ) :
    pureResidualCoefficient p β a =
      β^2*(1-a^(2*p)-(p : ℝ)*a^(2*p-2)*(1-a^2)) := by
  simp only [pureResidualCoefficient, pureResidualAtOne, ← pow_mul,
    show 2*(p-1) = 2*p-2 by omega]

theorem pureResidualAtOne_hasDerivAt (p : ℕ) (hp : 2 ≤ p) (r : ℝ) :
    HasDerivAt (pureResidualAtOne p)
      (-((p : ℝ)*((p : ℝ)-1)*r^(p-2)*(1-r))) r := by
  have h := ((hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_pow p r)).sub
    (((hasDerivAt_pow (p-1) r).const_mul (p : ℝ)).mul
      ((hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_id r)))
  convert h using 1
  · ext s
    rfl
  · dsimp
    rw [show p-1-1 = p-2 by omega, Nat.cast_sub (by omega : 1 ≤ p)]
    simp only [Nat.cast_one]
    ring

/-- Actual ordinary derivative of the literal pure residual coefficient. -/
theorem pureResidualCoefficient_hasDerivAt (p : ℕ) (hp : 2 ≤ p) (β a : ℝ) :
    HasDerivAt (pureResidualCoefficient p β)
      (-2*β^2*(p : ℝ)*((p : ℝ)-1)*a^(2*p-3)*(1-a^2)) a := by
  have h := ((pureResidualAtOne_hasDerivAt p hp (a^2)).comp a (hasDerivAt_pow 2 a)).const_mul (β^2)
  convert h using 1
  · ext s
    rfl
  · dsimp
    have hpow : (a^2)^(p-2)*a = a^(2*p-3) := by
      rw [← pow_mul, ← pow_succ]
      congr 1
      omega
    rw [← hpow]
    ring

theorem pureResidualCoefficient_antitoneOn (p : ℕ) (hp : 2 ≤ p) (β : ℝ) :
    AntitoneOn (pureResidualCoefficient p β) (Icc (0 : ℝ) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
  · intro a ha
    exact (pureResidualCoefficient_hasDerivAt p hp β a).continuousAt.continuousWithinAt
  · intro a ha
    exact (pureResidualCoefficient_hasDerivAt p hp β a).differentiableAt.differentiableWithinAt
  · intro a ha
    have ha' : a ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using ha
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
    have hpm1 : 0 ≤ (p : ℝ)-1 := by linarith
    have ha0 := ha'.1.le
    have hsquare : 0 ≤ 1-a^2 := by nlinarith [ha'.1, ha'.2]
    rw [(pureResidualCoefficient_hasDerivAt p hp β a).deriv]
    have hnonneg : 0 ≤ 2*β^2*(p : ℝ)*((p : ℝ)-1)*a^(2*p-3)*(1-a^2) := by positivity
    nlinarith

theorem pureResidualCoefficient_bound_from_overlap (p : ℕ) (hp : 4 ≤ p) {β Q a : ℝ}
    (hQ : Q ∈ Ioo (staticOverlap (zParameter p (by omega))) 1)
    (hroot : β^2*(p : ℝ)*(1+zParameter p (by omega))*Q^(p-2)*(1-Q)^2 = 1)
    (ha : a ∈ Icc (Real.sqrt Q) 1) :
    pureResidualCoefficient p β a < (159/320 : ℝ) := by
  have hQ0 : 0 < Q := (staticOverlap_mem_Ioo (zParameter_spec p (by omega)).1).1.trans hQ.1
  have hsqrt : Real.sqrt Q ∈ Icc (0 : ℝ) 1 := by
    refine ⟨Real.sqrt_nonneg Q, ?_⟩
    nlinarith [Real.sq_sqrt hQ0.le, Real.sqrt_nonneg Q, hQ.2]
  have hm := pureResidualCoefficient_antitoneOn p (by omega) β hsqrt
    ⟨hsqrt.1.trans ha.1, ha.2⟩ ha.1
  have hb := pureResidualAtOne_bound_of_root p hp hQ hroot
  unfold pureResidualCoefficient at hm
  rw [Real.sq_sqrt hQ0.le] at hm
  exact hm.trans_lt hb

/-- The complete quantitative residual bound applies to every requested
latitude above the actual canonical pure overlap, with the law, parameters,
and root equation all obtained from genuine minimization. -/
theorem canonical_pure_residualCoefficient_bound (p : ℕ) (hp : 4 ≤ p) {β : ℝ}
    (hβ : Thresholds.staticThreshold (fun r : ℝ => r^p) < β) :
    ∃ x ∈ Ioo (0 : ℝ) 1,
      ∃ Q ∈ Ioo (staticOverlap (zParameter p (by omega))) 1,
        (CSParisiMeasure.canonicalMinimizer (FiniteMixture.pure p (by omega) 1 (by positivity)) β).law =
          CrisantiSommers.twoAtom x Q ∧
        ∀ a ∈ Icc (Real.sqrt Q) 1, pureResidualCoefficient p β a < (159/320 : ℝ) := by
  obtain ⟨x, hx, Q, hQ, hlaw, hxformula, hroot, hcurv, hpositive⟩ :=
    canonical_pure_parameters p (by omega) hβ
  exact ⟨x, hx, Q, hQ, hlaw, fun a ha =>
    pureResidualCoefficient_bound_from_overlap p hp hQ hroot ha⟩

end

end SlowEquilibration.PureStationarity

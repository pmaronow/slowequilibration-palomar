-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! Finite numerical weights in the Ghirlanda--Guerra negative-star
recursion. These are elementary scalar calculations for the actual
replicated-probability argument; no stochastic identities are assumed here. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianGGWeights

open Set Filter
open scoped Topology BigOperators

set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Product appearing in the exact n-neighbor GG recursion. -/
def product (a : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range (n-1), (1+a/((k+1 : ℕ) : ℝ))

/-- Exact finite GG weight; n counts neighbors, so n+1 replicas are used. -/
def weight (a : ℝ) (n : ℕ) : ℝ := a/(n:ℝ)*product a n

@[simp] theorem weight_one (a : ℝ) : weight a 1=a := by simp [weight,product]

theorem product_nonneg {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : 0 ≤ product a n := by
  unfold product
  apply Finset.prod_nonneg
  intro k hk
  positivity

theorem product_succ (a : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    product a (n+1) = product a n*(1+a/(n:ℝ)) := by
  unfold product
  rw [show n+1-1=n-1+1 by omega, Finset.prod_range_succ, show n-1+1=n by omega]

theorem weight_succ (a : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    weight a (n+1) = ((n:ℝ)+a)/((n+1 : ℕ):ℝ)*weight a n := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : ((n+1 : ℕ):ℝ) ≠ 0 := by positivity
  unfold weight
  rw [product_succ a hn]
  field_simp

theorem normalized_weight (a : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (n:ℝ)*weight a n = a*product a n := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold weight
  field_simp

/-- One actual dyadic block contributes at least 1+a/2. -/
theorem product_double {a : ℝ} (ha : 0 ≤ a) {n : ℕ} (hn : 1 ≤ n) :
    product a n*(1+a/2) ≤ product a (2*n) := by
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  let c : ℝ := a/(2*(n:ℝ))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hbern : 1+a/2 ≤ (1+c)^n := by
    have hh := one_add_mul_le_pow (show (-2:ℝ) ≤ c by linarith) n
    have heq : 1+(n:ℝ)*c=1+a/2 := by dsimp [c]; field_simp
    rwa [heq] at hh
  have hprod : (1+c)^n ≤ ∏ k ∈ Finset.range n,
      (1+a/((k+(n-1)+1 : ℕ):ℝ)) := by
    have hconst : (1+c)^n=∏ _k ∈ Finset.range n, (1+c) := by simp
    rw [hconst]
    apply Finset.prod_le_prod₀
    · intro k hk
      positivity
    · intro k hk
      have hklt : k<n := Finset.mem_range.mp hk
      have hden : k+(n-1)+1=k+n := by omega
      rw [hden]
      have hdiv : c ≤ a/((k+n : ℕ):ℝ) := by
        dsimp [c]
        exact div_le_div_of_nonneg_left ha (by positivity)
          (by exact_mod_cast (show k+n ≤ 2*n by omega))
      linarith
  have hsplit : product a (2*n) = product a n*
      (∏ k ∈ Finset.range n, (1+a/((k+(n-1)+1 : ℕ):ℝ))) := by
    unfold product
    rw [show 2*n-1=(n-1)+n by omega, Finset.prod_range_add]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    rw [Nat.add_comm (n-1) k]
  rw [hsplit]
  exact mul_le_mul_of_nonneg_left (hbern.trans hprod) (product_nonneg ha n)

/-- The dyadic lower bound uses only finite products and Bernoulli's inequality. -/
theorem product_dyadic {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    (1+a/2)^k ≤ product a (2^k) := by
  induction k with
  | zero => simp [product]
  | succ k ih =>
    have hn : 1 ≤ 2^k := Nat.one_le_pow k 2 (by decide)
    calc
      _ = (1+a/2)^k*(1+a/2) := pow_succ _ _
      _ ≤ product a (2^k)*(1+a/2) := mul_le_mul_of_nonneg_right ih (by positivity)
      _ ≤ product a (2*(2^k)) := product_double ha hn
      _ = _ := by rw [pow_succ]; congr 1; omega

/-- Exact quantitative dyadic lower weight for pair mass at least a₀. -/
theorem weight_dyadic_lower {a a₀ : ℝ} (ha₀ : 0 < a₀) (ha : a₀ ≤ a) (k : ℕ) :
    a*(1+a₀/2)^k ≤ (2^k : ℕ)*weight a (2^k) := by
  have ha0 : 0 ≤ a := ha₀.le.trans ha
  rw [normalized_weight a (Nat.one_le_pow k 2 (by decide))]
  apply mul_le_mul_of_nonneg_left _ ha0
  exact (pow_le_pow_left₀ (by positivity) (by linarith) k).trans (product_dyadic ha0 k)

/-- The exact GG coefficient is a nonnegative contraction for pair mass a∈[0,1]. -/
theorem coefficient_bounds {a : ℝ} (ha : a∈Icc (0:ℝ) 1) (n : ℕ) :
    ((n:ℝ)+a)/((n+1 : ℕ):ℝ)∈Icc (0:ℝ) 1 := by
  have hden : 0 < ((n+1 : ℕ):ℝ) := by positivity
  constructor
  · exact div_nonneg (add_nonneg (Nat.cast_nonneg _) ha.1) hden.le
  · apply (div_le_one hden).mpr
    simp only [Nat.cast_add,Nat.cast_one]
    linarith [ha.2]

/-- Finite GG recursion errors accumulate by their sum, without a uniform
per-replica defect bound. This is suited to averaging actual GG defects. -/
theorem recursion_error_bound {a : ℝ} (ha : a∈Icc (0:ℝ) 1)
    (T d : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) (hT : T 1=a)
    (hGG : ∀ m, 1 ≤ m → m<n →
      |T (m+1)-(((m:ℝ)+a)/((m+1 : ℕ):ℝ))*T m| ≤ d m) :
    |T n-weight a n| ≤ ∑ m ∈ Finset.Ico 1 n, d m := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n=0
    · subst n
      simp [hT]
    · have hn1 : 1 ≤ n := by omega
      have hp := ih hn1 (fun m hm hmn => hGG m hm (by omega))
      let c : ℝ := ((n:ℝ)+a)/((n+1 : ℕ):ℝ)
      have hc0 : 0 ≤ c := (coefficient_bounds ha n).1
      have hc1 : c ≤ 1 := (coefficient_bounds ha n).2
      calc
        _ = |T (n+1)-c*weight a n| := by rw [weight_succ a hn1]
        _ ≤ |T (n+1)-c*T n|+|c*T n-c*weight a n| := abs_sub_le _ _ _
        _ = |T (n+1)-c*T n|+c*|T n-weight a n| := by
          rw [← mul_sub,abs_mul,abs_of_nonneg hc0]
        _ ≤ d n+|T n-weight a n| :=
          add_le_add (hGG n hn1 (by omega)) (mul_le_of_le_one_left (abs_nonneg _) hc1)
        _ ≤ d n+(∑ m ∈ Finset.Ico 1 n, d m) := by linarith
        _ = ∑ m ∈ Finset.Ico 1 (n+1), d m := by
          rw [Finset.sum_Ico_succ_top hn1]
          ring

/-- Finite lower bound on the actual star probabilities from their GG
recursion, with their actual individual defects retained. -/
theorem recursion_lower_bound {a : ℝ} (ha : a∈Icc (0:ℝ) 1)
    (T d : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) (hT : T 1=a)
    (hGG : ∀ m, 1 ≤ m → m<n →
      |T (m+1)-(((m:ℝ)+a)/((m+1 : ℕ):ℝ))*T m| ≤ d m) :
    weight a n-(∑ m ∈ Finset.Ico 1 n, d m) ≤ T n := by
  have h := (abs_le.mp (recursion_error_bound ha T d hn hT hGG)).1
  linarith

/-- Fixed geometric parameter used with a finite dyadic star. -/
def dyadicGamma (k : ℕ) : ℝ := 1-(k:ℝ)/((2^k : ℕ):ℝ)

theorem dyadicGamma_mem {k : ℕ} (hk : 1 ≤ k) : dyadicGamma k∈Ioo (0:ℝ) 1 := by
  have hn : 0 < ((2^k : ℕ):ℝ) := by positivity
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast (show 0<k by omega)
  have hklt : (k:ℝ) < ((2^k : ℕ):ℝ) := by exact_mod_cast (Nat.lt_two_pow_self (n := k))
  unfold dyadicGamma
  constructor
  · have hdiv := (div_lt_one hn).mpr hklt
    linarith
  · have hdiv := div_pos hk0 hn
    linarith

theorem dyadicGamma_pow_le_exp {k : ℕ} (hk : 1 ≤ k) :
    (dyadicGamma k)^(2^k) ≤ Real.exp (-(k:ℝ)) := by
  have hn : ((2^k : ℕ):ℝ) ≠ 0 := by positivity
  have hγ := dyadicGamma_mem hk
  have he : dyadicGamma k ≤ Real.exp (-(k:ℝ)/((2^k : ℕ):ℝ)) := by
    have h := Real.add_one_le_exp (-(k:ℝ)/((2^k : ℕ):ℝ))
    simpa only [dyadicGamma,neg_div,sub_eq_add_neg,add_comm] using h
  have hp := pow_le_pow_left₀ hγ.1.le he (2^k)
  have heq : (Real.exp (-(k:ℝ)/((2^k : ℕ):ℝ)))^(2^k) = Real.exp (-(k:ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  exact hp.trans_eq heq

/-- Exact normalized exponential term in the finite star bound. -/
theorem normalized_dyadicGamma_pow {k : ℕ} (hk : 1 ≤ k) :
    ((2^k : ℕ):ℝ)*(dyadicGamma k)^(2^k) ≤ (2/Real.exp 1)^k := by
  have hp := mul_le_mul_of_nonneg_left (dyadicGamma_pow_le_exp hk)
    (show (0:ℝ) ≤ ((2^k : ℕ):ℝ) by positivity)
  have hek : Real.exp (k:ℝ)=(Real.exp 1)^k := by
    simpa only [mul_one] using Real.exp_nat_mul 1 k
  have heq : ((2^k : ℕ):ℝ)*Real.exp (-(k:ℝ))=(2/Real.exp 1)^k := by
    rw [Real.exp_neg, hek, Nat.cast_pow, Nat.cast_ofNat, div_pow, div_eq_mul_inv]
  exact hp.trans_eq heq

/-- Panchenko's geometric upper at the chosen finite dyadic parameters,
with n times the star probability and no large-n limit premise. -/
theorem normalized_geometric_dyadic {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hk : 1 ≤ k) :
    ((2^k : ℕ):ℝ)*(2*(1-dyadicGamma k)/ε+(dyadicGamma k)^(2^k)) ≤
      2*(k:ℝ)/ε+(2/Real.exp 1)^k := by
  have hpow := normalized_dyadicGamma_pow hk
  have hn : ((2^k : ℕ):ℝ) ≠ 0 := by positivity
  have he : ((2^k : ℕ):ℝ)*(2*(1-dyadicGamma k)/ε) = 2*(k:ℝ)/ε := by
    unfold dyadicGamma
    field_simp
    ring
  rw [mul_add,he]
  linarith

private theorem normalized_geometric_dyadic_le_linear {ε : ℝ} (hε : 0 < ε)
    {k : ℕ} (hk : 1 ≤ k) :
    ((2^k : ℕ):ℝ)*(2*(1-dyadicGamma k)/ε+(dyadicGamma k)^(2^k)) ≤
      2*(k:ℝ)/ε+1 := by
  have he : 2 ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp 1
    norm_num at h ⊢
    exact h
  have hbase : 2/Real.exp 1 ≤ 1 := (div_le_one (Real.exp_pos _)).mpr he
  have hp : (2/Real.exp 1)^k ≤ 1 := pow_le_one₀ (by positivity) hbase
  exact (normalized_geometric_dyadic hε hk).trans (by linarith)

/-- A fixed finite GG test forces pair mass small, with a coefficient
multiplying the SUM of the actual individual recursion defects. The
chosen replica number and coefficient precede a,T,d, so the bound can
be averaged over random perturbation parameters. -/
theorem exists_finite_exclusion {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ n : ℕ, ∃ γ C : ℝ, 2 ≤ n ∧ γ∈Ioo (0:ℝ) 1 ∧ 0 < C ∧
      ∀ (a : ℝ), a∈Icc (0:ℝ) 1 → ∀ (T d : ℕ → ℝ), T 1=a →
      (∀ m, 1 ≤ m → m<n → 0 ≤ d m) →
      (∀ m, 1 ≤ m → m<n → |T (m+1)-(((m:ℝ)+a)/((m+1 : ℕ):ℝ))*T m| ≤ d m) →
      T n ≤ 2*(1-γ)/ε+γ^n →
      a ≤ η+C*(∑ m ∈ Finset.Ico 1 n, d m) := by
  let a₀ : ℝ := η/2
  let q : ℝ := 1+a₀/2
  have ha₀ : 0 < a₀ := by dsimp [a₀]; positivity
  have hq : 1 < q := by dsimp [q]; linarith
  have hlim : Tendsto (fun k : ℕ => (2*(k:ℝ)/ε+1)/q^k) atTop (𝓝 0) := by
    have h1 := (tendsto_pow_const_div_const_pow_of_one_lt 1 hq).const_mul (2/ε)
    have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 hq
    have hh := h1.add h0
    simp only [pow_one,pow_zero,mul_zero,add_zero] at hh
    have he : (fun k : ℕ => (2*(k:ℝ)/ε+1)/q^k) =
        (fun k : ℕ => (2/ε)*((k:ℝ)/q^k)+1/q^k) := by funext k; ring
    rw [he]
    exact hh
  obtain ⟨k,hk,hsmall⟩ := ((eventually_ge_atTop (1:ℕ)).and
    (hlim.eventually (gt_mem_nhds hη))).exists
  let n : ℕ := 2^k
  let C : ℝ := (n:ℝ)/q^k
  have hn : 2 ≤ n := by
    have hlt := Nat.lt_two_pow_self (n := k)
    dsimp [n]
    omega
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hqp : 0 < q^k := pow_pos (by linarith) k
  have hC : 0 < C := div_pos hnpos hqp
  refine ⟨n,dyadicGamma k,C,hn,dyadicGamma_mem hk,hC,?_⟩
  intro a ha T d hT hd hGG hgeom
  let E : ℝ := ∑ m ∈ Finset.Ico 1 n, d m
  have hE : 0 ≤ E := by
    apply Finset.sum_nonneg
    intro m hm
    obtain ⟨hm1,hmn⟩ := Finset.mem_Ico.mp hm
    exact hd m hm1 hmn
  by_cases halow : a<a₀
  · have hCE := mul_nonneg hC.le hE
    dsimp [a₀] at halow
    change a ≤ η+C*E
    linarith
  · have halarge : a₀ ≤ a := le_of_not_gt halow
    have hw := weight_dyadic_lower ha₀ halarge k
    change a*q^k ≤ (n:ℝ)*weight a n at hw
    have herr := recursion_lower_bound ha T d (show 1≤n by omega) hT hGG
    change weight a n-E ≤ T n at herr
    have hscale := mul_le_mul_of_nonneg_left (show weight a n ≤ T n+E by linarith) hnpos.le
    have htop := mul_le_mul_of_nonneg_left hgeom hnpos.le
    have hnumeric := normalized_geometric_dyadic_le_linear hε hk
    change (n:ℝ)*(2*(1-dyadicGamma k)/ε+(dyadicGamma k)^n) ≤ 2*(k:ℝ)/ε+1 at hnumeric
    have hupper : a*q^k ≤ 2*(k:ℝ)/ε+1+(n:ℝ)*E := by nlinarith
    have hsmall' : 2*(k:ℝ)/ε+1 < η*q^k := (div_lt_iff₀ hqp).mp hsmall
    have hbound : a*q^k ≤ η*q^k+(n:ℝ)*E := by linarith
    have hdiv := (le_div_iff₀ hqp).mpr hbound
    change a ≤ η+C*E
    calc
      _ ≤ (η*q^k+(n:ℝ)*E)/q^k := hdiv
      _ = _ := by dsimp [C]; field_simp

end SlowEquilibration.GaussianGGWeights

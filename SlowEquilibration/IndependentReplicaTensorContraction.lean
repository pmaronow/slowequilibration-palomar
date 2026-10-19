-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic

/-! Ordered tensor contractions for two independent copies of a replica
system.  Coordinate tuples are unrestricted functions, so repetitions and
diagonal tensor entries are included.  The mixed-power bound only uses the
individual cross-pair moments; independence among different pairs is not
assumed.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.IndependentReplicaTensorContraction

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 500000

/-- A tensor monomial whose individual tensor slots can belong to different
Gibbs replicas. -/
def replicaMonomial {α κ ι : Type*} [Fintype α]
    (labels : α → κ) (σ : κ → ι → ℝ) (I : α → ι) : ℝ :=
  ∏ a, σ (labels a) (I a)

/-- Summing all ordered tensor indices contracts two replica monomials
exactly to their cross dot products. -/
theorem sum_replicaMonomial_mul {α κ ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (labels : α → κ) (σ τ : κ → ι → ℝ) :
    (∑ I : α → ι, replicaMonomial labels σ I * replicaMonomial labels τ I) =
      ∏ a, ∑ i, σ (labels a) i * τ (labels a) i := by
  classical
  simp only [replicaMonomial, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun a i => σ (labels a) i * τ (labels a) i)).symm

/-- The square of an averaged replicated tensor is represented using two
independent copies of the entire system.  Replicas within either copy can
have any dependence permitted by their common disorder. -/
theorem sum_square_integral_replicaMonomial
    {Ω α κ ι : Type*} [MeasurableSpace Ω] [Fintype α] [DecidableEq α] [Fintype ι]
    (ν : Measure Ω) [SFinite ν] (labels : α → κ) (σ : Ω → κ → ι → ℝ)
    (hi : ∀ I : α → ι, Integrable (fun ω => replicaMonomial labels (σ ω) I) ν) :
    (∑ I : α → ι, (∫ ω, replicaMonomial labels (σ ω) I ∂ν) ^ 2) =
      ∫ z : Ω × Ω, ∏ a, ∑ i, σ z.1 (labels a) i * σ z.2 (labels a) i
        ∂ν.prod ν := by
  classical
  calc
    _ = ∑ I : α → ι, ∫ z : Ω × Ω,
        replicaMonomial labels (σ z.1) I * replicaMonomial labels (σ z.2) I
          ∂ν.prod ν := by
      apply Finset.sum_congr rfl
      intro I _
      simpa only [pow_two] using (integral_prod_mul (μ := ν) (ν := ν)
        (fun ω => replicaMonomial labels (σ ω) I)
        (fun ω => replicaMonomial labels (σ ω) I)).symm
    _ = ∫ z : Ω × Ω, ∑ I : α → ι,
        replicaMonomial labels (σ z.1) I * replicaMonomial labels (σ z.2) I
          ∂ν.prod ν := by
      symm
      apply integral_finsetSum
      intro I _
      simpa only [smul_eq_mul] using (hi I).smul_prod (hi I)
    _ = _ := by
      apply integral_congr_ae
      exact .of_forall fun z => sum_replicaMonomial_mul labels (σ z.1) (σ z.2)

/-- A coarse mixed-power bound that needs no independence of the factors.
It retains the total tensor degree in each one-factor moment. -/
theorem prod_pow_le_sum_pow_total {κ : Type*} [Fintype κ] [Nonempty κ]
    (x : κ → ℝ) (p : κ → ℕ) (hx : ∀ i, 0 ≤ x i) :
    (∏ i, x i ^ p i) ≤ ∑ i, x i ^ (∑ j, p j) := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ x Finset.univ_nonempty
  calc
    _ ≤ ∏ i, x j ^ p i := Finset.prod_le_prod₀
      (fun i _ => pow_nonneg (hx i) _) (fun i _ =>
        pow_le_pow_left₀ (hx i) (hj i (Finset.mem_univ i)) _)
    _ = x j ^ (∑ i, p i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ _ := Finset.single_le_sum (fun i _ => pow_nonneg (hx i) _) (Finset.mem_univ j)

/-- The model normalization cancels the independent-sphere cross moment
at every fixed derivative order because each physical degree is at least
two.  The statement includes quadratic and odd physical degrees. -/
theorem normalized_cross_moment_scale_le_one {N : ℝ} (hN : 1 ≤ N)
    (M k : ℕ) (hdegree : 2 * k ≤ M) :
    N ^ (-((M - k : ℕ) : ℝ)) * N ^ ((M : ℝ) / 2) ≤ 1 := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  rw [← Real.rpow_add hNp]
  apply Real.rpow_le_one_of_one_le_of_nonpos hN
  have hk : k ≤ M := by omega
  rw [Nat.cast_sub hk]
  have hdegree' : 2 * (k : ℝ) ≤ (M : ℝ) := by exact_mod_cast hdegree
  linarith

/-- Finite signed replica expansions preserve a uniform squared tensor
bound.  Expansion coefficients and their number enter only the constant;
neither can depend on the ambient tensor dimension. -/
theorem weighted_expansion_square_sum_le
    {Τ Ι : Type*} [Fintype Τ] [Fintype Ι]
    (c : Τ → ℝ) (b : Τ → Ι → ℝ) {R C : ℝ} (hR : 0 ≤ R)
    (hb : ∀ t, R * (∑ I, b t I ^ 2) ≤ C) :
    R * (∑ I, (∑ t, c t * b t I) ^ 2) ≤
      (Fintype.card Τ : ℝ) * (∑ t, c t ^ 2) * C := by
  classical
  have hpoint (I : Ι) : (∑ t, c t * b t I) ^ 2 ≤
      (Fintype.card Τ : ℝ) * (∑ t, c t ^ 2 * b t I ^ 2) := by
    simpa only [Finset.card_univ, mul_pow] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun t => c t * b t I))
  calc
    _ ≤ R * (∑ I, (Fintype.card Τ : ℝ) * (∑ t, c t ^ 2 * b t I ^ 2)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun I _ => hpoint I) hR
    _ = (Fintype.card Τ : ℝ) *
        (∑ t, c t ^ 2 * (R * ∑ I, b t I ^ 2)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro I _
      ring
    _ ≤ (Fintype.card Τ : ℝ) * (∑ t, c t ^ 2 * C) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hb t) (sq_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

end SlowEquilibration.IndependentReplicaTensorContraction

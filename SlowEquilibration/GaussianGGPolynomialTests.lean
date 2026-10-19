-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianGGCutoffs
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.Normed.Operator.Basic

/-! True finite polynomial extension of continuous GG tests. The
normalized GG discrepancy is a linear functional on continuous overlap
tests with norm at most two. Its finite power-test defects, together with
genuine uniform polynomial approximation, bound every predetermined
negative cutoff. No indicator GG identity is a premise. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianGGPolynomialTests

open Set MeasureTheory
open GaussianGGCutoffs
open scoped Topology BigOperators

set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev Tests := C(Icc (-1:ℝ) 1,ℝ)

def powerTest (k : ℕ) : Tests := ⟨fun r => (r:ℝ)^k, continuous_subtype_val.pow k⟩

def cutoffTest (ε : ℝ) (M : ℕ) (j : Fin M) : Tests :=
  ⟨fun r => cutoff ε M j r, (cutoff_contDiff ε M j).continuous.comp continuous_subtype_val⟩

/-- Literal coefficient expansion of the actual continuous polynomial test. -/
theorem polynomial_test_expansion (P : Polynomial ℝ) {K : ℕ} (hK : P.natDegree ≤ K) :
    P.toContinuousMapOn (Icc (-1:ℝ) 1) =
      ∑ k ∈ Finset.range (K+1), P.coeff k • powerTest k := by
  apply ContinuousMap.ext
  intro r
  change P.eval (r:ℝ) = (ContinuousMap.evalCLM ℝ r)
    (∑ k ∈ Finset.range (K+1), P.coeff k • powerTest k)
  rw [map_sum]
  simp only [map_smul,ContinuousMap.evalCLM_apply,smul_eq_mul]
  exact Polynomial.eval_eq_sum_range' (by omega) (r:ℝ)

/-- Actual finite power-test control extends linearly to every polynomial. -/
theorem polynomial_discrepancy_le (D : Tests →L[ℝ] ℝ) (P : Polynomial ℝ)
    {K : ℕ} (hK : P.natDegree ≤ K) (d : ℕ → ℝ)
    (hpower : ∀ k ∈ Finset.range (K+1), |D (powerTest k)| ≤ d k) :
    |D (P.toContinuousMapOn (Icc (-1:ℝ) 1))| ≤
      ∑ k ∈ Finset.range (K+1), |P.coeff k| * d k := by
  rw [polynomial_test_expansion P hK,map_sum]
  simp only [map_smul,smul_eq_mul]
  calc
    _ ≤ ∑ k ∈ Finset.range (K+1), |P.coeff k*D (powerTest k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun k hk => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hpower k hk) (abs_nonneg _)

/-- A genuine uniform polynomial approximation is an actual sup-norm bound. -/
theorem approximation_norm_le (ε : ℝ) (M : ℕ) (j : Fin M) (P : Polynomial ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (happrox : ∀ r ∈ Icc (-1:ℝ) 1, |P.eval r-cutoff ε M j r| ≤ δ) :
    ‖P.toContinuousMapOn (Icc (-1:ℝ) 1)-cutoffTest ε M j‖ ≤ δ := by
  apply (ContinuousMap.norm_le _ hδ).mpr
  intro r
  rw [Real.norm_eq_abs]
  change |P.eval (r:ℝ)-cutoff ε M j (r:ℝ)| ≤ δ
  exact happrox r r.property

/-- Finite power-GG bounds imply continuous cutoff-GG control with the
exact normalized functional approximation error 2δ. -/
theorem cutoff_discrepancy_le (D : Tests →L[ℝ] ℝ) (hD : ‖D‖ ≤ 2)
    (ε : ℝ) (M : ℕ) (j : Fin M) (P : Polynomial ℝ)
    {K : ℕ} (hK : P.natDegree ≤ K) {δ : ℝ} (hδ : 0 ≤ δ)
    (happrox : ∀ r ∈ Icc (-1:ℝ) 1, |P.eval r-cutoff ε M j r| ≤ δ)
    (d : ℕ → ℝ) (hpower : ∀ k ∈ Finset.range (K+1), |D (powerTest k)| ≤ d k) :
    |D (cutoffTest ε M j)| ≤
      (∑ k ∈ Finset.range (K+1), |P.coeff k| * d k)+2*δ := by
  let ψ := cutoffTest ε M j
  let p := P.toContinuousMapOn (Icc (-1:ℝ) 1)
  have hnorm : ‖ψ-p‖ ≤ δ := by
    rw [norm_sub_rev]
    exact approximation_norm_le ε M j P hδ happrox
  have hb : |D ψ-D p| ≤ 2*δ := by
    rw [← map_sub,← Real.norm_eq_abs]
    exact (D.le_opNorm (ψ-p)).trans
      (mul_le_mul hD hnorm (norm_nonneg _) (by norm_num))
  have hp := polynomial_discrepancy_le D P hK d hpower
  have ht := abs_sub_le (D ψ) (D p) 0
  simp only [sub_zero] at ht
  change |D ψ| ≤ _
  change |D p| ≤ _ at hp
  linarith

/-- Uniform family extension: all approximating tests, powers and finite
coefficients are selected before the GG functional or its actual defects. -/
theorem exists_finite_cutoff_test_extension (ε : ℝ) (M : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ P : Fin M → Polynomial ℝ, ∃ K : ℕ, ∃ C : ℝ, 0 < C ∧
      (∀ j, (∑ k ∈ Finset.range (K+1), |(P j).coeff k|) ≤ C) ∧
      ∀ (D : Tests →L[ℝ] ℝ), ‖D‖ ≤ 2 → ∀ (d : ℕ → ℝ),
      (∀ k ∈ Finset.range (K+1), |D (powerTest k)| ≤ d k) →
      ∀ j, |D (cutoffTest ε M j)| ≤
        (∑ k ∈ Finset.range (K+1), |(P j).coeff k| * d k)+2*δ := by
  obtain ⟨P,K,C,hC,happ,hK,hcoeff⟩ := exists_bounded_polynomial_family ε M hδ
  refine ⟨P,K,C,hC,hcoeff,?_⟩
  intro D hD d hp j
  exact cutoff_discrepancy_le D hD ε M j (P j) (hK j) hδ.le
    (fun r hr => (happ j r hr).le) d hp

end SlowEquilibration.GaussianGGPolynomialTests

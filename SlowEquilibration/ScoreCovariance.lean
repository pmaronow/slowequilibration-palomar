-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.MixtureCurvature
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

namespace SlowEquilibration

open scoped BigOperators
open Set

/-- The exact finite pairwise variance identity, without normalization. -/
theorem finite_weighted_variance_pairwise {ι : Type*} (s : Finset ι)
    (w a : ι → ℝ) :
    (∑ i∈s,w i)*(∑ i∈s,w i*(a i)^2)-(∑ i∈s,w i*a i)^2 =
      (∑ i∈s,∑ j∈s,w i*w j*(a i-a j)^2)/2 := by
  have hsplit : (∑ i∈s,∑ j∈s,w i*w j*(a i-a j)^2)=
      (∑ i∈s,∑ j∈s,w i*(a i)^2*w j)+
      (∑ i∈s,∑ j∈s,w i*(w j*(a j)^2))-
      2*(∑ i∈s,∑ j∈s,(w i*a i)*(w j*a j)) := by
    simp only [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsplit]
  simp only [←Finset.mul_sum,←Finset.sum_mul]
  ring

namespace FiniteMixture

variable (μ : FiniteMixture)

theorem score_first_moment (r : ℝ) :
    r*μ.xi1 r=∑ p∈μ.coeff.support,μ.coeff p*r^p*(p:ℝ) := by
  unfold xi1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp1 : 1 ≤ p := (μ.degree_ge_two hp).trans' (by norm_num)
  have hexp : r*r^(p-1)=r^p := by
    rw [←pow_succ']
    congr 1
    omega
  calc
    _ = μ.coeff p*(r*r^(p-1))*(p:ℝ) := by ring
    _ = _ := by rw [hexp]

theorem score_second_moment (r : ℝ) :
    r*μ.xi1 r+r^2*μ.xi2 r=∑ p∈μ.coeff.support,μ.coeff p*r^p*(p:ℝ)^2 := by
  rw [score_first_moment]
  unfold xi2
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hp2 := μ.degree_ge_two hp
  have hexp : r^2*r^(p-2)=r^p := by
    rw [←pow_add]
    congr 1
    omega
  have hp1 : ((p-1:ℕ):ℝ)=(p:ℝ)-1 := by rw [Nat.cast_sub (by omega)];norm_num
  unfold curvatureCoeff
  rw [hp1]
  calc
    _ = μ.coeff p*r^p*(p:ℝ)+μ.coeff p*(p:ℝ)*((p:ℝ)-1)*(r^2*r^(p-2)) := by ring
    _ = _ := by rw [hexp];ring

/-- The actual value/radial score covariance matrix Σ_Q of the manuscript. -/
noncomputable def scoreCovariance (Q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i=0 then (if j=0 then μ.xi Q else Q*μ.xi1 Q)
    else (if j=0 then Q*μ.xi1 Q else Q*μ.xi1 Q+Q^2*μ.xi2 Q)

theorem scoreCovariance_det_pairwise (Q : ℝ) :
    (μ.scoreCovariance Q).det=
      (∑ p∈μ.coeff.support,∑ k∈μ.coeff.support,
        (μ.coeff p*Q^p)*(μ.coeff k*Q^k)*((p:ℝ)-(k:ℝ))^2)/2 := by
  rw [Matrix.det_fin_two]
  norm_num only [scoreCovariance,Fin.zero_eq_mk,Fin.reduceEq,ite_true,ite_false]
  rw [score_second_moment,score_first_moment]
  change (∑ p∈μ.coeff.support,μ.coeff p*Q^p)*
      (∑ p∈μ.coeff.support,(μ.coeff p*Q^p)*(p:ℝ)^2)-
      (∑ p∈μ.coeff.support,(μ.coeff p*Q^p)*(p:ℝ))*
      (∑ p∈μ.coeff.support,(μ.coeff p*Q^p)*(p:ℝ))=_
  simpa only [pow_two] using finite_weighted_variance_pairwise μ.coeff.support
    (fun p=>μ.coeff p*Q^p) (fun p=>(p:ℝ))

theorem scoreCovariance_det_nonneg {Q : ℝ} (hQ : 0 ≤ Q) :
    0 ≤ (μ.scoreCovariance Q).det := by
  rw [scoreCovariance_det_pairwise]
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro p _
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (mul_nonneg (mul_nonneg (μ.nonneg p) (pow_nonneg hQ _))
      (mul_nonneg (μ.nonneg k) (pow_nonneg hQ _))) (sq_nonneg _)
  · norm_num

/-- Nonpure finite mixtures have a genuinely nonsingular score covariance,
derived from two distinct positive Gaussian degree blocks. -/
theorem scoreCovariance_det_pos {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree<μ.maxDegree) : 0 < (μ.scoreCovariance Q).det := by
  rw [scoreCovariance_det_pairwise]
  apply div_pos _ (by norm_num)
  let p := μ.minDegree
  let k := μ.maxDegree
  have hp : p∈μ.coeff.support := Finset.min'_mem _ _
  have hk : k∈μ.coeff.support := Finset.max'_mem _ _
  have htermpos : 0 < (μ.coeff p*Q^p)*(μ.coeff k*Q^k)*((p:ℝ)-(k:ℝ))^2 := by
    have hpk : (p:ℝ)≠(k:ℝ) := by exact_mod_cast hnp.ne
    exact mul_pos (mul_pos (mul_pos (μ.coeff_pos hp) (pow_pos hQ _))
      (mul_pos (μ.coeff_pos hk) (pow_pos hQ _))) (sq_pos_of_ne_zero (sub_ne_zero.mpr hpk))
  have hnonneg (p k : ℕ) :
      0 ≤ (μ.coeff p*Q^p)*(μ.coeff k*Q^k)*((p:ℝ)-(k:ℝ))^2 := by positivity [μ.nonneg p,μ.nonneg k]
  have hinner := Finset.single_le_sum (fun j _=>hnonneg p j) hk
  have houter := Finset.single_le_sum
    (f:=fun i => ∑ j∈μ.coeff.support,
      (μ.coeff i*Q^i)*(μ.coeff j*Q^j)*((i:ℝ)-(j:ℝ))^2)
    (fun i _=>Finset.sum_nonneg (fun j _=>hnonneg i j)) hp
  exact htermpos.trans_le (hinner.trans houter)

end FiniteMixture
end SlowEquilibration

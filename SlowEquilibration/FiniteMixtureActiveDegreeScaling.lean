-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalActiveDegreeMomentLimit

@[expose] public section
noncomputable section

namespace SlowEquilibration.FiniteMixtureActiveDegreeScaling

open SphericalModel
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000

def scaleActiveDegree (μ : FiniteMixture) (p : Degree μ.maxDegree)
    (s : ℝ) (hs : 0 < s) (hcp : 0 < mixtureCoefficients μ p) :
    FiniteMixture where
  coeff := μ.coeff.update p.val.val (μ.coeff p.val.val*s^2)
  nonneg := by
    intro k
    rw [Finsupp.update_apply]
    split_ifs
    · exact mul_nonneg hcp.le (sq_nonneg s)
    · exact μ.nonneg k
  zero_below_two := by
    intro k hk
    rw [Finsupp.update_apply]
    split_ifs with h
    · have hp : 2 ≤ p.val.val := p.property
      omega
    · exact μ.zero_below_two k hk
  nonzero := by
    intro hz
    have h := congrArg (fun a : ℕ →₀ ℝ => a p.val.val) hz
    simp [Finsupp.update_apply] at h
    rcases h with h | h
    · exact hcp.ne' h
    · exact hs.ne' h

theorem scaleActiveDegree_coeff_self (μ : FiniteMixture)
    (p : Degree μ.maxDegree) (s : ℝ) (hs : 0 < s)
    (hcp : 0 < mixtureCoefficients μ p) :
    (scaleActiveDegree μ p s hs hcp).coeff p.val.val =
      μ.coeff p.val.val*s^2 := by
  change (μ.coeff.update p.val.val (μ.coeff p.val.val*s^2)) p.val.val = _
  simp [Finsupp.update_apply]

theorem scaleActiveDegree_coeff_other (μ : FiniteMixture)
    (p : Degree μ.maxDegree) (s : ℝ) (hs : 0 < s)
    (hcp : 0 < mixtureCoefficients μ p)
    {k : ℕ} (hk : k ≠ p.val.val) :
    (scaleActiveDegree μ p s hs hcp).coeff k = μ.coeff k := by
  change (μ.coeff.update p.val.val (μ.coeff p.val.val*s^2)) k = _
  simp [Finsupp.update_apply, hk]

theorem scaleActiveDegree_support (μ : FiniteMixture)
    (p : Degree μ.maxDegree) (s : ℝ) (hs : 0 < s)
    (hcp : 0 < mixtureCoefficients μ p) :
    (scaleActiveDegree μ p s hs hcp).coeff.support = μ.coeff.support := by
  have hp : p.val.val ∈ μ.coeff.support := by
    exact Finsupp.mem_support_iff.mpr hcp.ne'
  have hval : μ.coeff p.val.val*s^2 ≠ 0 :=
    mul_ne_zero hcp.ne' (pow_ne_zero 2 hs.ne')
  change (μ.coeff.update p.val.val (μ.coeff p.val.val*s^2)).support = _
  rw [Finsupp.support_update_ne_zero μ.coeff p.val.val hval]
  exact Finset.insert_eq_of_mem hp

theorem scaleActiveDegree_maxDegree (μ : FiniteMixture)
    (p : Degree μ.maxDegree) (s : ℝ) (hs : 0 < s)
    (hcp : 0 < mixtureCoefficients μ p) :
    (scaleActiveDegree μ p s hs hcp).maxDegree = μ.maxDegree := by
  unfold FiniteMixture.maxDegree
  congr 1
  exact scaleActiveDegree_support μ p s hs hcp

theorem scaleActiveDegree_xi (μ : FiniteMixture)
    (p : Degree μ.maxDegree) (s : ℝ) (hs : 0 < s)
    (hcp : 0 < mixtureCoefficients μ p) (r : ℝ) :
    (scaleActiveDegree μ p s hs hcp).xi r =
      μ.xi r+(mixtureCoefficients μ p)*(s^2-1)*r^p.val.val := by
  have hp : p.val.val ∈ μ.coeff.support :=
    Finsupp.mem_support_iff.mpr hcp.ne'
  unfold FiniteMixture.xi
  rw [scaleActiveDegree_support]
  rw [← Finset.add_sum_erase μ.coeff.support
    (fun k => (scaleActiveDegree μ p s hs hcp).coeff k * r^k) hp,
    ← Finset.add_sum_erase μ.coeff.support
      (fun k => μ.coeff k*r^k) hp]
  have hsum : (∑ k ∈ μ.coeff.support.erase p.val.val,
      (scaleActiveDegree μ p s hs hcp).coeff k*r^k) =
      ∑ k ∈ μ.coeff.support.erase p.val.val, μ.coeff k*r^k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [scaleActiveDegree_coeff_other μ p s hs hcp
      (Finset.ne_of_mem_erase hk)]
  rw [hsum,scaleActiveDegree_coeff_self]
  dsimp only [mixtureCoefficients]
  ring

end SlowEquilibration.FiniteMixtureActiveDegreeScaling

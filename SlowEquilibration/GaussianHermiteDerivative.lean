-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianMaximalCorrelation

/-! The finite Bessel estimate used by Hermite truncation.  This file keeps
the analytic coefficient identity explicit: it does not assert integration
by parts for a function without hypotheses justifying that identity. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.GaussianHermiteDerivative

open MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open GaussianMaximalCorrelation
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι]

/-- Bessel's inequality in integral notation for the normalized product
Hermite system. -/
theorem finite_coeff_square_sum_le {f : (ι → ℝ) → ℝ}
    (hf : MemLp f 2 (γpi ι)) (s : Finset (ι → ℕ)) :
    ∑ a ∈ s, (coeff f a) ^ 2 ≤ ∫ x, f x ^ 2 ∂γpi ι := by
  have hs := hermite_hasSum_sq hf
  rw [← hs.tsum_eq]
  exact hs.summable.sum_le_tsum s (fun _ _ => sq_nonneg _)

/-- The coordinate raising identity and square integrability of the actual
derivatives imply the finite weighted-energy bound needed by truncation.
Only finitely many coefficients are summed, so no exchange of infinite
weighted sums and integrals is required. -/
theorem finite_weighted_energy_le_of_coeff_identity [DecidableEq ι]
    (f : (ι → ℝ) → ℝ) (g : ι → (ι → ℝ) → ℝ)
    (hg : ∀ i, MemLp (g i) 2 (γpi ι))
    (hcoeff : ∀ i a,
      coeff (g i) a = Real.sqrt (a i + 1 : ℝ) * coeff f (bump i a))
    (s : Finset (ι → ℕ)) :
    ∑ a ∈ s, (degree a : ℝ) * (coeff f a) ^ 2 ≤
      ∑ i, ∫ x, (g i x) ^ 2 ∂γpi ι := by
  classical
  have hcoord (i : ι) :
      ∑ a ∈ s, (a i : ℝ) * (coeff f a) ^ 2 ≤
        ∫ x, (g i x) ^ 2 ∂γpi ι := by
    let t := s.filter (fun a => 0 < a i)
    let lower : (ι → ℕ) → (ι → ℕ) := fun a => Function.update a i (a i - 1)
    have hlower (a : ι → ℕ) (ha : a ∈ t) : bump i (lower a) = a := by
      have ha' : 0 < a i := (Finset.mem_filter.mp ha).2
      ext j
      by_cases hj : j = i
      · subst j
        simp only [bump, lower, Function.update_self]
        omega
      · simp [bump, lower, Function.update_of_ne hj]
    have hinj : ∀ a ∈ t, ∀ b ∈ t, lower a = lower b → a = b := by
      intro a ha b hb hab
      rw [← hlower a ha, ← hlower b hb, hab]
    have hterm (a : ι → ℕ) (ha : a ∈ t) :
        (coeff (g i) (lower a)) ^ 2 = (a i : ℝ) * (coeff f a) ^ 2 := by
      have ha' : 0 < a i := (Finset.mem_filter.mp ha).2
      rw [hcoeff, hlower a ha, mul_pow, Real.sq_sqrt (by positivity)]
      congr 1
      simp only [lower, Function.update_self]
      exact_mod_cast (show a i - 1 + 1 = a i by omega)
    calc
      _ = ∑ a ∈ t, (a i : ℝ) * (coeff f a) ^ 2 := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro a ha hna
        have hz : a i = 0 := by
          have : ¬ 0 < a i := by simpa [t, ha] using hna
          omega
        simp [hz]
      _ = ∑ a ∈ t, (coeff (g i) (lower a)) ^ 2 := by
        exact Finset.sum_congr rfl (fun a ha => (hterm a ha).symm)
      _ = ∑ b ∈ t.image lower, (coeff (g i) b) ^ 2 := by
        rw [Finset.sum_image hinj]
      _ ≤ _ := finite_coeff_square_sum_le (hg i) _
  calc
    _ = ∑ a ∈ s, ∑ i, (a i : ℝ) * (coeff f a) ^ 2 := by
      simp only [degree, Nat.cast_sum, Finset.sum_mul]
    _ = ∑ i, ∑ a ∈ s, (a i : ℝ) * (coeff f a) ^ 2 := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun i _ => hcoord i)

end SlowEquilibration.GaussianHermiteDerivative

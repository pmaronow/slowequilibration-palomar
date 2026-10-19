-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib

/-! A deterministic small positive-overlap collar estimate. The hypotheses
are derivative identities and a curvature bound on a genuine geodesic
critical-pair exponent. They contain no requested negativity conclusion. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PairConditionalDeterminantMoments

private theorem scalar_derivative_upper_bound
    (f f' : ℝ → ℝ) (b M : ℝ) (hb : 0 ≤ b)
    (hderiv : ∀ r ∈ Set.Icc (0 : ℝ) b, HasDerivAt f (f' r) r)
    (hbound : ∀ r ∈ Set.Icc (0 : ℝ) b, f' r ≤ M) :
    f b - f 0 ≤ M*b := by
  rcases hb.eq_or_lt with rfl | hbpos
  · simp
  have hc : ContinuousOn f (Set.Icc (0 : ℝ) b) := by
    intro x hx
    exact (hderiv x hx).continuousAt.continuousWithinAt
  obtain ⟨r,hr,hslope⟩ := exists_hasDerivAt_eq_slope f f' hbpos hc
    (fun x hx => hderiv x (Set.Ioo_subset_Icc_self hx))
  have hrI : r ∈ Set.Icc (0 : ℝ) b := Set.Ioo_subset_Icc_self hr
  have hle : (f b - f 0)/b ≤ M := by
    have heq : f' r = (f b - f 0)/b := by simpa using hslope
    rw [← heq]
    exact hbound r hrI
  exact (div_le_iff₀ hbpos).mp hle

/-- Negative critical-pair slope at zero and an `O(N)` curvature bound force
the actual scalar exponent strictly below zero on a fixed short collar.
The radius is fixed before varying the dimension. -/
theorem source_pair_scalar_critical_collar
    (N C κ θ : ℝ) (hN : 0 < N) (hC : 0 < C) (hκ : 0 < κ)
    (hθ : 0 < θ) (hθsmall : θ < κ/(2*C))
    (s h t : ℝ → ℝ) (hs0 : s 0 = 0) (hh0 : h 0 ≤ -κ*N)
    (hs : ∀ r ∈ Set.Icc (0 : ℝ) θ, HasDerivAt s (h r) r)
    (hh : ∀ r ∈ Set.Icc (0 : ℝ) θ, HasDerivAt h (t r) r)
    (ht : ∀ r ∈ Set.Icc (0 : ℝ) θ, |t r| ≤ C*N) :
    s θ < 0 := by
  have hCN : 0 ≤ C*N := mul_nonneg hC.le hN.le
  have hct : C*θ < κ/2 := by
    calc
      C*θ < C*(κ/(2*C)) := mul_lt_mul_of_pos_left hθsmall hC
      _ = κ/2 := by field_simp
  have hctN : (C*N)*θ < (κ*N)/2 := by
    have hm := mul_lt_mul_of_pos_right hct hN
    nlinarith
  have hbound : ∀ r ∈ Set.Icc (0 : ℝ) θ, t r ≤ C*N := by
    intro r hr
    exact (le_abs_self (t r)).trans (ht r hr)
  have hneg : ∀ r ∈ Set.Icc (0 : ℝ) θ, h r < 0 := by
    intro r hr
    have hdiff := scalar_derivative_upper_bound h t r (C*N) hr.1
      (fun x hx => hh x (Set.Icc_subset_Icc_right hr.2 hx))
      (fun x hx => hbound x (Set.Icc_subset_Icc_right hr.2 hx))
    have hmul : (C*N)*r ≤ (C*N)*θ :=
      mul_le_mul_of_nonneg_left hr.2 hCN
    nlinarith
  have hcont : ContinuousOn s (Set.Icc (0 : ℝ) θ) := by
    intro x hx
    exact (hs x hx).continuousAt.continuousWithinAt
  obtain ⟨r,hr,hslope⟩ := exists_hasDerivAt_eq_slope s h hθ hcont
    (fun x hx => hs x (Set.Ioo_subset_Icc_self hx))
  have hrI : r ∈ Set.Icc (0 : ℝ) θ := Set.Ioo_subset_Icc_self hr
  have hdiv : (s θ - s 0)/θ < 0 := by
    have heq : h r = (s θ - s 0)/θ := by simpa using hslope
    rw [← heq]
    exact hneg r hrI
  have hdiv0 : s θ/θ < 0 := by simpa [hs0] using hdiv
  rcases div_neg_iff.mp hdiv0 with ⟨_,hθneg⟩ | ⟨hsneg,_⟩
  · exact False.elim ((not_lt_of_ge hθ.le) hθneg)
  · exact hsneg

end SlowEquilibration.PairConditionalDeterminantMoments

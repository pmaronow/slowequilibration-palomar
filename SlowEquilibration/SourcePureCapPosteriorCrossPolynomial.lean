-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapPosteriorCrossKernel

/-! A finite-binomial proof that the mixed-latitude pure residual kernel
has the needed quadratic overlap bound. Positivity of the coefficient
sequence makes the proof valid for odd and even degrees. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapPosteriorCrossPolynomial
noncomputable section
open Set FiniteMixture
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

private def sideTerm (p k : ℕ) (q s : ℝ) : ℝ := q^(p-k)*s^k

private theorem residual_sum_side
    (p : ℕ) (hp : 2 ≤ p) (q s : ℝ) :
    (∑ k ∈ Finset.range (p+1), if 2 ≤ k then
      (p.choose k : ℝ)*(sideTerm p k q s)^2 else 0) =
      (q^2+s^2)^p-(q^2)^p-(p : ℝ)*(q^2)^(p-1)*s^2 := by
  have h := sum_binomial_residual p hp 1 (q^2) (s^2) 1
  have h' : (∑ k ∈ Finset.range (p+1), if 2 ≤ k then
      (p.choose k : ℝ)*(q^2)^(p-k)*(s^2)^k else 0) =
      (q^2+s^2)^p-(q^2)^p-(p : ℝ)*(q^2)^(p-1)*s^2 := by
    simpa only [one_mul,mul_one,one_pow] using h
  rw [←h']
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs with h₂
  · dsimp [sideTerm]
    ring_nf
  · rfl

private theorem residual_sum_cross
    (p : ℕ) (hp : 2 ≤ p) (q₁ q₂ s₁ s₂ t : ℝ) :
    (∑ k ∈ Finset.range (p+1), if 2 ≤ k then
      (p.choose k : ℝ)*(sideTerm p k q₁ s₁)*
        (sideTerm p k q₂ s₂)*t^k else 0) =
      (q₁*q₂+s₁*s₂*t)^p-(q₁*q₂)^p-
        (p : ℝ)*(q₁*q₂)^(p-1)*(s₁*s₂)*t := by
  have h := sum_binomial_residual p hp 1 (q₁*q₂) (s₁*s₂) t
  simp only [one_mul] at h
  rw [←h]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs with h₂
  · dsimp [sideTerm]
    rw [mul_pow,mul_pow]
    ring
  · rfl

/-- Cross-latitude residual covariance is at most the arithmetic mean of
its two self-variance residuals, times the transverse overlap squared. -/
theorem pure_cross_binomial_residual_abs_le_average_self
    (p : ℕ) (hp : 2 ≤ p) {q₁ q₂ s₁ s₂ t : ℝ}
    (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂) (ht : |t| ≤ 1) :
    |(q₁*q₂+s₁*s₂*t)^p-(q₁*q₂)^p-
      (p : ℝ)*(q₁*q₂)^(p-1)*(s₁*s₂)*t| ≤
      (((q₁^2+s₁^2)^p-(q₁^2)^p-
          (p : ℝ)*(q₁^2)^(p-1)*s₁^2)+
       ((q₂^2+s₂^2)^p-(q₂^2)^p-
          (p : ℝ)*(q₂^2)^(p-1)*s₂^2))/2*t^2 := by
  let A := sideTerm p
  have hside₁ (k : ℕ) : 0 ≤ A k q₁ s₁ :=
    mul_nonneg (pow_nonneg hq₁ _) (pow_nonneg hs₁ _)
  have hside₂ (k : ℕ) : 0 ≤ A k q₂ s₂ :=
    mul_nonneg (pow_nonneg hq₂ _) (pow_nonneg hs₂ _)
  have hterm (k : ℕ) (hk : k ∈ Finset.range (p+1)) :
      |if 2 ≤ k then (p.choose k : ℝ)*A k q₁ s₁*A k q₂ s₂*t^k else 0| ≤
        (if 2 ≤ k then (p.choose k : ℝ)*
          ((A k q₁ s₁)^2+(A k q₂ s₂)^2)/2*t^2 else 0) := by
    split_ifs with hk₂
    · have hchoose : 0 ≤ (p.choose k : ℝ) := Nat.cast_nonneg _
      have hpow : |t|^k ≤ t^2 := by
        simpa only [sq_abs] using
          pow_le_pow_of_le_one (abs_nonneg t) ht hk₂
      have hAMGM : 2*A k q₁ s₁*A k q₂ s₂ ≤
          (A k q₁ s₁)^2+(A k q₂ s₂)^2 := by
        nlinarith [sq_nonneg (A k q₁ s₁-A k q₂ s₂)]
      rw [abs_mul,abs_mul,abs_mul,abs_pow,
        abs_of_nonneg hchoose,abs_of_nonneg (hside₁ k),
        abs_of_nonneg (hside₂ k)]
      have hfirst : (p.choose k : ℝ)*A k q₁ s₁*A k q₂ s₂*|t|^k ≤
          (p.choose k : ℝ)*A k q₁ s₁*A k q₂ s₂*t^2 :=
        mul_le_mul_of_nonneg_left hpow
          (mul_nonneg (mul_nonneg hchoose (hside₁ k)) (hside₂ k))
      have hsecond : (p.choose k : ℝ)*A k q₁ s₁*A k q₂ s₂*t^2 ≤
          (p.choose k : ℝ)*
            ((A k q₁ s₁)^2+(A k q₂ s₂)^2)/2*t^2 := by
        nlinarith [mul_nonneg (mul_nonneg hchoose (sq_nonneg t))
          (sub_nonneg.mpr hAMGM)]
      exact hfirst.trans hsecond
    · simp
  have hsum := Finset.sum_le_sum hterm
  have hcross := residual_sum_cross p hp q₁ q₂ s₁ s₂ t
  have hself₁ := residual_sum_side p hp q₁ s₁
  have hself₂ := residual_sum_side p hp q₂ s₂
  calc
    _ = |∑ k ∈ Finset.range (p+1), if 2 ≤ k then
          (p.choose k : ℝ)*A k q₁ s₁*A k q₂ s₂*t^k else 0| := by
          rw [hcross]
    _ ≤ ∑ k ∈ Finset.range (p+1),
          |if 2 ≤ k then (p.choose k : ℝ)*A k q₁ s₁*A k q₂ s₂*t^k else 0| :=
            Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (p+1),
          (if 2 ≤ k then (p.choose k : ℝ)*
            ((A k q₁ s₁)^2+(A k q₂ s₂)^2)/2*t^2 else 0) := hsum
    _ = _ := by
      have hfactor : (∑ k ∈ Finset.range (p+1),
          if 2 ≤ k then (p.choose k : ℝ)*
            ((A k q₁ s₁)^2+(A k q₂ s₂)^2)/2*t^2 else 0) =
          (∑ k ∈ Finset.range (p+1),
            if 2 ≤ k then (p.choose k : ℝ)*
              ((A k q₁ s₁)^2+(A k q₂ s₂)^2)/2 else 0)*t^2 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        split_ifs <;> ring
      have hsplit : (∑ k ∈ Finset.range (p+1),
          if 2 ≤ k then (p.choose k : ℝ)*
            ((A k q₁ s₁)^2+(A k q₂ s₂)^2)/2 else 0) =
          ((∑ k ∈ Finset.range (p+1), if 2 ≤ k then
              (p.choose k : ℝ)*(A k q₁ s₁)^2 else 0)+
           (∑ k ∈ Finset.range (p+1), if 2 ≤ k then
              (p.choose k : ℝ)*(A k q₂ s₂)^2 else 0))/2 := by
        rw [←Finset.sum_add_distrib,Finset.sum_div]
        apply Finset.sum_congr rfl
        intro k hk
        split_ifs <;> ring
      rw [hfactor,hsplit,hself₁,hself₂]

end
end SlowEquilibration.SourcePureCapPosteriorCrossPolynomial

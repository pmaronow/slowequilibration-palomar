-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourceUniformMonotoneParameter

/-! Uniform division by a converging nonzero scalar, and the positive lower
bound supplied by a uniformly positive limiting profile. -/
@[expose] public section
namespace SlowEquilibration.SourceUniformScalarRatio
noncomputable section
open Filter Set Metric
open scoped Topology
set_option autoImplicit false

/-- A scalar denominator can be divided out of a uniform limit when the
limiting numerator is bounded on the parameter set. -/
theorem uniformlyOn_div_scalar
    {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {A : ℕ → ℝ} {a M : ℝ}
    {S : Set ℝ}
    (hF : TendstoUniformlyOn F f atTop S)
    (hA : Tendsto A atTop (𝓝 a)) (ha : a ≠ 0) (hM0 : 0 ≤ M)
    (hM : ∀ t ∈ S, |f t| ≤ M) :
    TendstoUniformlyOn (fun n t => F n t / A n)
      (fun t => f t / a) atTop S := by
  have hInv : Tendsto (fun n => (A n)⁻¹) atTop (𝓝 a⁻¹) := hA.inv₀ ha
  have hC : 0 < |a⁻¹|+1 := by positivity
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hden : 0 < M+1 := by linarith
  have hδF : 0 < ε/(2*(|a⁻¹|+1)) := by positivity
  have hδA : 0 < ε/(2*(M+1)) := by positivity
  have hFe := (Metric.tendstoUniformlyOn_iff.mp hF)
    (ε/(2*(|a⁻¹|+1))) hδF
  have hIe := hInv.eventually (Metric.ball_mem_nhds _ (by norm_num : (0:ℝ)<1))
  have hAe := hInv.eventually (Metric.ball_mem_nhds _ hδA)
  filter_upwards [hFe,hIe,hAe] with n hn hni hna t ht
  have hni' : |(A n)⁻¹| < |a⁻¹|+1 := by
    have hdist : |(A n)⁻¹-a⁻¹| < 1 := by simpa [Real.dist_eq] using hni
    calc
      |(A n)⁻¹| = |((A n)⁻¹-a⁻¹)+a⁻¹| := by congr 1; abel
      _ ≤ |(A n)⁻¹-a⁻¹|+|a⁻¹| := abs_add_le _ _
      _ < _ := by linarith
  have hna' : |(A n)⁻¹-a⁻¹| < ε/(2*(M+1)) := by
    simpa [Real.dist_eq] using hna
  have hn' : |F n t-f t| < ε/(2*(|a⁻¹|+1)) := by
    simpa [Real.dist_eq, abs_sub_comm] using hn t ht
  rw [Real.dist_eq, abs_sub_comm (f t/a) (F n t/A n)]
  have heq : F n t / A n - f t/a =
      (F n t-f t)*(A n)⁻¹ + f t*((A n)⁻¹-a⁻¹) := by
    rw [div_eq_mul_inv,div_eq_mul_inv]
    ring
  rw [heq]
  calc
    |(F n t-f t)*(A n)⁻¹+f t*((A n)⁻¹-a⁻¹)| ≤
        |F n t-f t| * |(A n)⁻¹| + |f t| * |(A n)⁻¹-a⁻¹| := by
          simpa [abs_mul] using abs_add_le
            ((F n t-f t)*(A n)⁻¹) (f t*((A n)⁻¹-a⁻¹))
    _ < ε := by
      have h1 : |F n t-f t| * |(A n)⁻¹| < ε/2 := by
        calc
          _ ≤ |F n t-f t| * (|a⁻¹|+1) :=
            mul_le_mul_of_nonneg_left hni'.le (abs_nonneg _)
          _ < ε/(2*(|a⁻¹|+1)) * (|a⁻¹|+1) :=
            (mul_lt_mul_of_pos_right hn' hC)
          _ = ε/2 := by field_simp
      have h2 : |f t| * |(A n)⁻¹-a⁻¹| < ε/2 := by
        calc
          _ ≤ M * |(A n)⁻¹-a⁻¹| :=
            mul_le_mul_of_nonneg_right (hM t ht) (abs_nonneg _)
          _ ≤ (M+1) * |(A n)⁻¹-a⁻¹| := by
            gcongr
            linarith
          _ < (M+1)*(ε/(2*(M+1))) :=
            mul_lt_mul_of_pos_left hna' hden
          _ = ε/2 := by field_simp
      linarith

/-- Uniform convergence to a profile bounded below by a positive constant
gives a simultaneous lower bound for every parameter in the set. -/
theorem eventually_uniform_lower_half
    {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {S : Set ℝ} {c : ℝ}
    (hF : TendstoUniformlyOn F f atTop S)
    (hc : 0 < c) (hf : ∀ t ∈ S, c ≤ f t) :
    ∀ᶠ n : ℕ in atTop, ∀ t ∈ S, c/2 ≤ F n t := by
  have he := (Metric.tendstoUniformlyOn_iff.mp hF) (c/2) (by positivity)
  filter_upwards [he] with n hn t ht
  have hdist : |F n t-f t| < c/2 := by
    simpa [Real.dist_eq, abs_sub_comm] using hn t ht
  rcases abs_lt.mp hdist with ⟨hlo,_⟩
  linarith [hf t ht]

end
end SlowEquilibration.SourceUniformScalarRatio

-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourceGaussianLaplacePerturbed

/-! Integrability of localized Laplace kernels with a varying microscopic
amplitude. This also supplies the hypotheses for monotonicity of integrals. -/
@[expose] public section
namespace SlowEquilibration.SourceGaussianLaplacePerturbedIntegrable
noncomputable section
open Set MeasureTheory SourceGaussianLaplacePerturbed

/-- A subquadratic amplitude envelope is integrable against the strict
quadratic saddle envelope in every finite dimension. -/
theorem integrable_perturbedKernel {φ : ℝ → ℝ} {A : ℕ → ℝ → ℝ}
    {m l r c δ M : ℝ} (hφmeas : Measurable φ)
    (hAmeas : ∀ n, Measurable (A n))
    (hδ : δ < c) (hM : 0 ≤ M)
    (hAbound : ∀ n u, |A n u| ≤ M*Real.exp (δ*u^2))
    (henv : ∀ t ∈ Icc l r, φ t ≤ φ m-c*(t-m)^2)
    (n : ℕ) : Integrable (perturbedKernel φ A m l r n) := by
  let b : ℝ → ℝ := fun u => M*Real.exp (-(c-δ)*u^2)
  have hbi : Integrable b :=
    (integrable_exp_neg_mul_sq (by linarith : 0 < c-δ)).const_mul M
  apply Integrable.mono' hbi
  · apply Measurable.aestronglyMeasurable
    unfold perturbedKernel
    apply Measurable.ite measurableSet_Icc
    · have hA := hAmeas n
      fun_prop (disch := assumption)
    · exact measurable_const
  · apply Filter.Eventually.of_forall
    intro u
    have hnonneg : 0 ≤ b u := mul_nonneg hM (Real.exp_pos _).le
    by_cases hu : u ∈ Icc (Real.sqrt (n+2 : ℕ)*(l-m))
        (Real.sqrt (n+2 : ℕ)*(r-m))
    · have hs : 0 < Real.sqrt (n+2 : ℕ) := by positivity
      have ht : m+u/Real.sqrt (n+2 : ℕ) ∈ Icc l r := by
        rcases hu with ⟨hl,hr⟩
        constructor
        · have h := (le_div_iff₀ hs).mpr (by nlinarith [hl] :
            (l-m)*Real.sqrt (n+2 : ℕ) ≤ u)
          linarith
        · have h := (div_le_iff₀ hs).mpr (by nlinarith [hr] :
            u ≤ (r-m)*Real.sqrt (n+2 : ℕ))
          linarith
      have hsq : ((n+2 : ℕ) : ℝ)*
          ((m+u/Real.sqrt (n+2 : ℕ))-m)^2 = u^2 := by
        rw [add_sub_cancel_left, div_pow,
          Real.sq_sqrt (by positivity : 0 ≤ ((n+2 : ℕ) : ℝ))]
        field_simp
      have hexp : Real.exp ((n+2 : ℕ)*
          (φ (m+u/Real.sqrt (n+2 : ℕ))-φ m)) ≤ Real.exp (-c*u^2) := by
        apply Real.exp_le_exp.mpr
        have hh := henv _ ht
        have hh' : ((n+2 : ℕ) : ℝ)*
            (φ (m+u/Real.sqrt (n+2 : ℕ))-φ m) ≤
            -c*(((n+2 : ℕ) : ℝ)*
              ((m+u/Real.sqrt (n+2 : ℕ))-m)^2) := by
          nlinarith [mul_le_mul_of_nonneg_left hh
            (show 0 ≤ ((n+2 : ℕ) : ℝ) by positivity)]
        rw [hsq] at hh'
        exact hh'
      simp only [perturbedKernel, hu, ↓reduceIte, norm_mul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      calc
        |A n u| * Real.exp ((n+2 : ℕ)*
            (φ (m+u/Real.sqrt (n+2 : ℕ))-φ m)) ≤
            (M*Real.exp (δ*u^2))*Real.exp (-c*u^2) :=
              mul_le_mul (hAbound n u) hexp (Real.exp_pos _).le
                (mul_nonneg hM (Real.exp_pos _).le)
        _ = b u := by
          dsimp [b]
          rw [mul_assoc, ← Real.exp_add]
          congr 1
          ring
    · simp only [perturbedKernel, hu, ↓reduceIte, norm_zero]
      exact hnonneg

end
end SlowEquilibration.SourceGaussianLaplacePerturbedIntegrable

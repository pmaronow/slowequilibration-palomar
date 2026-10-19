-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourceGaussianLaplaceLocal

/-! Gaussian Laplace convergence with varying microscopic amplitudes.
A subquadratic Gaussian allowance accommodates logarithmic perturbations. -/
@[expose] public section
namespace SlowEquilibration.SourceGaussianLaplacePerturbed
noncomputable section
open Filter Set MeasureTheory
open scoped Topology

private theorem sqrt_dim_pos (n : ℕ) : 0 < Real.sqrt (n+2 : ℕ) := by positivity

private theorem scaled_iff (n : ℕ) (m l r u : ℝ) :
    u ∈ Icc (Real.sqrt (n+2 : ℕ)*(l-m)) (Real.sqrt (n+2 : ℕ)*(r-m)) ↔
      m+u/Real.sqrt (n+2 : ℕ) ∈ Icc l r := by
  have hs := sqrt_dim_pos n
  constructor
  · rintro ⟨hl,hr⟩
    have hl' : l-m ≤ u/Real.sqrt (n+2 : ℕ) :=
      (le_div_iff₀ hs).mpr (by nlinarith [hl])
    have hr' : u/Real.sqrt (n+2 : ℕ) ≤ r-m :=
      (div_le_iff₀ hs).mpr (by nlinarith [hr])
    exact ⟨by linarith,by linarith⟩
  · rintro ⟨hl,hr⟩
    have hl' : l-m ≤ u/Real.sqrt (n+2 : ℕ) := by linarith
    have hr' : u/Real.sqrt (n+2 : ℕ) ≤ r-m := by linarith
    have hla := (le_div_iff₀ hs).mp hl'
    have hra := (div_le_iff₀ hs).mp hr'
    exact ⟨by nlinarith [hla], by nlinarith [hra]⟩

private theorem scaled_eventually_mem {l m r u : ℝ} (hl : l < m) (hr : m < r) :
    ∀ᶠ n : ℕ in atTop,
      u ∈ Icc (Real.sqrt (n+2 : ℕ)*(l-m)) (Real.sqrt (n+2 : ℕ)*(r-m)) := by
  have hz := SourceGaussianLaplaceTaylor.scaled_tendsto m u
  filter_upwards [hz.eventually (Ioo_mem_nhds hl hr)] with n hn
  exact (scaled_iff n m l r u).mpr ⟨hn.1.le,hn.2.le⟩

/-- The localized scaled kernel with an `n`-dependent microscopic amplitude. -/
def perturbedKernel (φ : ℝ → ℝ) (A : ℕ → ℝ → ℝ)
    (m l r : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  if u ∈ Icc (Real.sqrt (n+2 : ℕ)*(l-m)) (Real.sqrt (n+2 : ℕ)*(r-m)) then
    A n u * Real.exp ((n+2 : ℕ)*(φ (m+u/Real.sqrt (n+2 : ℕ))-φ m))
  else 0

/-- A Gaussian envelope with any loss smaller than the strict quadratic gap
is enough for exact convergence of the scaled integral on a fixed set. -/
theorem integral_perturbedKernel_tendsto {φ : ℝ → ℝ} {A : ℕ → ℝ → ℝ}
    {m l r q c δ M a₀ : ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Ioo l r)) (hφmeas : Measurable φ)
    (hstat : derivWithin φ (Ioo l r) m = 0)
    (hcurv : iteratedDerivWithin 2 φ (Ioo l r) m = q)
    (hl : l < m) (hr : m < r)
    (hc : 0 < c) (hδ : δ < c) (hM : 0 ≤ M)
    (hAmeas : ∀ n, Measurable (A n))
    (hAlim : ∀ u, Tendsto (fun n => A n u) atTop (𝓝 a₀))
    (hAbound : ∀ n u, |A n u| ≤ M*Real.exp (δ*u^2))
    (henv : ∀ t ∈ Icc l r, φ t ≤ φ m-c*(t-m)^2)
    (S : Set ℝ) :
    Tendsto (fun n : ℕ => ∫ u in S, perturbedKernel φ A m l r n u) atTop
      (𝓝 (∫ u in S, a₀*Real.exp (q*u^2/2))) := by
  let b : ℝ → ℝ := fun u => M*Real.exp (-(c-δ)*u^2)
  have hbi : Integrable b (volume.restrict S) :=
    ((integrable_exp_neg_mul_sq (by linarith : 0 < c-δ)).const_mul M).integrableOn
  have hmeas (n : ℕ) : AEStronglyMeasurable (perturbedKernel φ A m l r n)
      (volume.restrict S) := by
    apply Measurable.aestronglyMeasurable
    unfold perturbedKernel
    apply Measurable.ite measurableSet_Icc
    · have hA := hAmeas n
      fun_prop (disch := assumption)
    · exact measurable_const
  have hbound (n : ℕ) : ∀ᵐ u ∂volume.restrict S,
      ‖perturbedKernel φ A m l r n u‖ ≤ b u := by
    apply Filter.Eventually.of_forall
    intro u
    have hnonneg : 0 ≤ b u := mul_nonneg hM (Real.exp_pos _).le
    by_cases hu : u ∈ Icc (Real.sqrt (n+2 : ℕ)*(l-m))
        (Real.sqrt (n+2 : ℕ)*(r-m))
    · have ht := (scaled_iff n m l r u).mp hu
      have hsq : ((n+2 : ℕ) : ℝ) *
          ((m+u/Real.sqrt (n+2 : ℕ))-m)^2 = u^2 := by
        rw [add_sub_cancel_left, div_pow, Real.sq_sqrt (by positivity : 0 ≤ ((n+2 : ℕ) : ℝ))]
        field_simp
      have hexp : Real.exp ((n+2 : ℕ)*
          (φ (m+u/Real.sqrt (n+2 : ℕ))-φ m)) ≤ Real.exp (-c*u^2) := by
        apply Real.exp_le_exp.mpr
        have hh := henv _ ht
        nlinarith [mul_le_mul_of_nonneg_left hh (show 0 ≤ ((n+2 : ℕ) : ℝ) by positivity)]
      simp only [perturbedKernel, hu, ↓reduceIte, norm_mul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      calc
        |A n u| * Real.exp ((n+2 : ℕ) *
            (φ (m+u/Real.sqrt (n+2 : ℕ))-φ m))
            ≤ (M*Real.exp (δ*u^2))*Real.exp (-c*u^2) :=
              mul_le_mul (hAbound n u) hexp (Real.exp_pos _).le
                (mul_nonneg hM (Real.exp_pos _).le)
        _ = b u := by
          dsimp [b]
          rw [mul_assoc, ← Real.exp_add]
          congr 1
          ring
    · simp only [perturbedKernel, hu, ↓reduceIte, norm_zero]
      exact hnonneg
  have hlim : ∀ᵐ u ∂volume.restrict S,
      Tendsto (fun n => perturbedKernel φ A m l r n u) atTop
        (𝓝 (a₀*Real.exp (q*u^2/2))) := by
    apply Filter.Eventually.of_forall
    intro u
    have he := SourceGaussianLaplaceLocalTaylor.scaled_quadratic_tangent_local hl hr hφ hstat hcurv u
    have hraw : Tendsto
        (fun n : ℕ => A n u *
          Real.exp ((n+2 : ℕ)*(φ (m+u/Real.sqrt (n+2 : ℕ))-φ m)))
        atTop (𝓝 (a₀*Real.exp (q*u^2/2))) :=
      (hAlim u).mul (Real.continuous_exp.continuousAt.tendsto.comp he)
    exact hraw.congr' (by
      filter_upwards [scaled_eventually_mem (u:=u) hl hr]
        with n hn
      simp only [perturbedKernel, hn, ↓reduceIte])
  exact tendsto_integral_of_dominated_convergence b hmeas hbi hbound hlim

/-- Exact total Gaussian mass for a varying amplitude. -/
theorem integral_perturbedKernel_gaussian {φ : ℝ → ℝ} {A : ℕ → ℝ → ℝ}
    {m l r κ c δ M a₀ : ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Ioo l r)) (hφmeas : Measurable φ)
    (hstat : derivWithin φ (Ioo l r) m = 0)
    (hcurv : iteratedDerivWithin 2 φ (Ioo l r) m = -κ)
    (hl : l < m) (hr : m < r)
    (hc : 0 < c) (hδ : δ < c) (hM : 0 ≤ M)
    (hAmeas : ∀ n, Measurable (A n))
    (hAlim : ∀ u, Tendsto (fun n => A n u) atTop (𝓝 a₀))
    (hAbound : ∀ n u, |A n u| ≤ M*Real.exp (δ*u^2))
    (henv : ∀ t ∈ Icc l r, φ t ≤ φ m-c*(t-m)^2) :
    Tendsto (fun n : ℕ => ∫ u, perturbedKernel φ A m l r n u) atTop
      (𝓝 (a₀*Real.sqrt (Real.pi/(κ/2)))) := by
  have h := integral_perturbedKernel_tendsto hφ hφmeas hstat hcurv hl hr hc hδ hM
    hAmeas hAlim hAbound henv Set.univ
  have hg : (∫ u : ℝ, Real.exp ((-κ)*u^2/2)) = Real.sqrt (Real.pi/(κ/2)) := by
    have heq (u : ℝ) : (-κ)*u^2/2 = -(κ/2)*u^2 := by ring
    simp_rw [heq]
    exact integral_gaussian (κ/2)
  simpa only [setIntegral_univ, integral_const_mul, hg] using h

/-- Exact Gaussian mass on every fixed microscopic interval. -/
theorem integral_perturbedKernel_window {φ : ℝ → ℝ} {A : ℕ → ℝ → ℝ}
    {m l r κ c δ M a₀ α β : ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Ioo l r)) (hφmeas : Measurable φ)
    (hstat : derivWithin φ (Ioo l r) m = 0)
    (hcurv : iteratedDerivWithin 2 φ (Ioo l r) m = -κ)
    (hl : l < m) (hr : m < r)
    (hc : 0 < c) (hδ : δ < c) (hM : 0 ≤ M)
    (hAmeas : ∀ n, Measurable (A n))
    (hAlim : ∀ u, Tendsto (fun n => A n u) atTop (𝓝 a₀))
    (hAbound : ∀ n u, |A n u| ≤ M*Real.exp (δ*u^2))
    (henv : ∀ t ∈ Icc l r, φ t ≤ φ m-c*(t-m)^2) :
    Tendsto (fun n : ℕ => ∫ u in Icc α β, perturbedKernel φ A m l r n u) atTop
      (𝓝 (a₀ * ∫ u in Icc α β, Real.exp (-κ*u^2/2))) := by
  have h := integral_perturbedKernel_tendsto hφ hφmeas hstat hcurv hl hr hc hδ hM
    hAmeas hAlim hAbound henv (Icc α β)
  simpa only [neg_mul, neg_div, integral_const_mul] using h

end
end SlowEquilibration.SourceGaussianLaplacePerturbed

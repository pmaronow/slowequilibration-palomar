-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourceGaussianLaplaceTaylor
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! One-dimensional Gaussian Laplace convergence on a fixed scaled region.
The original localization interval moves to all of `ℝ` in microscopic coordinates. -/
@[expose] public section
namespace SlowEquilibration.SourceGaussianLaplaceScaled
noncomputable section
open Filter Set MeasureTheory
open scoped Topology

private theorem dim_pos (n : ℕ) : (0 : ℝ) < (n+2 : ℕ) := by positivity
private theorem sqrt_dim_pos (n : ℕ) : 0 < Real.sqrt (n+2 : ℕ) := by positivity

/-- The rescaled integrand, localized to the original compact interval. -/
def scaledKernel (φ a : ℝ → ℝ) (m l r : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  if u ∈ Icc (Real.sqrt (n+2 : ℕ)*(l-m)) (Real.sqrt (n+2 : ℕ)*(r-m)) then
    a (m+u/Real.sqrt (n+2 : ℕ)) *
      Real.exp ((n+2 : ℕ)*(φ (m+u/Real.sqrt (n+2 : ℕ))-φ m))
  else 0

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

private theorem scaled_kernel_bound {φ a : ℝ → ℝ} {m l r c M : ℝ}
    (hc : 0 < c) (hM : 0 ≤ M)
    (hamp : ∀ t ∈ Icc l r, |a t| ≤ M)
    (henv : ∀ t ∈ Icc l r, φ t ≤ φ m-c*(t-m)^2)
    (n : ℕ) (u : ℝ) :
    ‖scaledKernel φ a m l r n u‖ ≤ M*Real.exp (-c*u^2) := by
  have hnonneg : 0 ≤ M*Real.exp (-c*u^2) := mul_nonneg hM (Real.exp_pos _).le
  by_cases hu : u ∈ Icc (Real.sqrt (n+2 : ℕ)*(l-m))
      (Real.sqrt (n+2 : ℕ)*(r-m))
  · have ht := (scaled_iff n m l r u).mp hu
    have hsq : ((n+2 : ℕ) : ℝ) *
        ((m+u/Real.sqrt (n+2 : ℕ))-m)^2 = u^2 := by
      rw [add_sub_cancel_left, div_pow, Real.sq_sqrt (dim_pos n).le]
      field_simp
    have hexp : Real.exp ((n+2 : ℕ)*
        (φ (m+u/Real.sqrt (n+2 : ℕ))-φ m)) ≤ Real.exp (-c*u^2) := by
      apply Real.exp_le_exp.mpr
      have hh := henv _ ht
      nlinarith [mul_le_mul_of_nonneg_left hh (dim_pos n).le]
    simp only [scaledKernel, hu, ↓reduceIte, norm_mul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hamp _ ht) hexp (Real.exp_pos _).le hM
  · simp only [scaledKernel, hu, ↓reduceIte, norm_zero]
    exact hnonneg

/-- Dominated Gaussian Laplace asymptotics on any fixed measurable microscopic set. -/
theorem integral_scaledKernel_tendsto {φ a : ℝ → ℝ} {m l r q c M : ℝ}
    (hφ : ContDiff ℝ 2 φ) (ha : Continuous a)
    (hstat : deriv φ m = 0) (hcurv : iteratedDeriv 2 φ m = q)
    (hl : l < m) (hr : m < r)
    (hc : 0 < c) (hM : 0 ≤ M)
    (hamp : ∀ t ∈ Icc l r, |a t| ≤ M)
    (henv : ∀ t ∈ Icc l r, φ t ≤ φ m-c*(t-m)^2)
    (S : Set ℝ) :
    Tendsto (fun n : ℕ => ∫ u in S, scaledKernel φ a m l r n u) atTop
      (𝓝 (∫ u in S, a m*Real.exp (q*u^2/2))) := by
  let b : ℝ → ℝ := fun u => M*Real.exp (-c*u^2)
  have hbi : Integrable b (volume.restrict S) :=
    ((integrable_exp_neg_mul_sq hc).const_mul M).integrableOn
  have hmeas (n : ℕ) : AEStronglyMeasurable (scaledKernel φ a m l r n)
      (volume.restrict S) := by
    apply Measurable.aestronglyMeasurable
    unfold scaledKernel
    apply Measurable.ite measurableSet_Icc
    · have hφmeas : Measurable φ := hφ.continuous.measurable
      have hameas : Measurable a := ha.measurable
      fun_prop (disch := assumption)
    · exact measurable_const
  have hbound (n : ℕ) : ∀ᵐ u ∂volume.restrict S,
      ‖scaledKernel φ a m l r n u‖ ≤ b u :=
    Filter.Eventually.of_forall (scaled_kernel_bound hc hM hamp henv n)
  have hlim : ∀ᵐ u ∂volume.restrict S,
      Tendsto (fun n => scaledKernel φ a m l r n u) atTop
        (𝓝 (a m*Real.exp (q*u^2/2))) := by
    apply Filter.Eventually.of_forall
    intro u
    have hz := SourceGaussianLaplaceTaylor.scaled_tendsto m u
    have he := SourceGaussianLaplaceTaylor.scaled_quadratic_tangent hφ hstat hcurv u
    have hraw : Tendsto
        (fun n : ℕ => a (m+u/Real.sqrt (n+2 : ℕ)) *
          Real.exp ((n+2 : ℕ)*(φ (m+u/Real.sqrt (n+2 : ℕ))-φ m)))
        atTop (𝓝 (a m*Real.exp (q*u^2/2))) :=
      (ha.continuousAt.tendsto.comp hz).mul (Real.continuous_exp.continuousAt.tendsto.comp he)
    exact hraw.congr' (by
      filter_upwards [scaled_eventually_mem (u:=u) hl hr] with n hn
      simp only [scaledKernel, hn, ↓reduceIte])
  exact tendsto_integral_of_dominated_convergence b hmeas hbi hbound hlim

/-- The full localized mass has the exact Gaussian prefactor. -/
theorem integral_scaledKernel_gaussian {φ a : ℝ → ℝ} {m l r κ c M : ℝ}
    (hφ : ContDiff ℝ 2 φ) (ha : Continuous a)
    (hstat : deriv φ m = 0) (hcurv : iteratedDeriv 2 φ m = -κ)
    (hl : l < m) (hr : m < r)
    (hc : 0 < c) (hM : 0 ≤ M)
    (hamp : ∀ t ∈ Icc l r, |a t| ≤ M)
    (henv : ∀ t ∈ Icc l r, φ t ≤ φ m-c*(t-m)^2) :
    Tendsto (fun n : ℕ => ∫ u, scaledKernel φ a m l r n u) atTop
      (𝓝 (a m*Real.sqrt (Real.pi/(κ/2)))) := by
  have h := integral_scaledKernel_tendsto hφ ha hstat hcurv hl hr hc hM hamp henv
    Set.univ
  have hg : (∫ u : ℝ, Real.exp ((-κ)*u^2/2)) = Real.sqrt (Real.pi/(κ/2)) := by
    have heq (u : ℝ) : (-κ)*u^2/2 = -(κ/2)*u^2 := by ring
    simp_rw [heq]
    exact integral_gaussian (κ/2)
  simpa only [setIntegral_univ, integral_const_mul, hg] using h

/-- Every fixed microscopic interval converges to its Gaussian mass. -/
theorem integral_scaledKernel_window {φ a : ℝ → ℝ} {m l r κ c M α β : ℝ}
    (hφ : ContDiff ℝ 2 φ) (ha : Continuous a)
    (hstat : deriv φ m = 0) (hcurv : iteratedDeriv 2 φ m = -κ)
    (hl : l < m) (hr : m < r)
    (hc : 0 < c) (hM : 0 ≤ M)
    (hamp : ∀ t ∈ Icc l r, |a t| ≤ M)
    (henv : ∀ t ∈ Icc l r, φ t ≤ φ m-c*(t-m)^2) :
    Tendsto (fun n : ℕ => ∫ u in Icc α β, scaledKernel φ a m l r n u) atTop
      (𝓝 (a m * ∫ u in Icc α β, Real.exp (-κ*u^2/2))) := by
  have h := integral_scaledKernel_tendsto hφ ha hstat hcurv hl hr hc hM hamp henv
    (Icc α β)
  simpa only [neg_mul, neg_div, integral_const_mul] using h

end
end SlowEquilibration.SourceGaussianLaplaceScaled

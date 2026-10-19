-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalEnergy

@[expose] public section

/-! # A single density-oscillation factor in actual spherical Rayleigh quotients

The Gibbs normalization cancels before comparison. All integrals below use
the actual uniform spherical law and the actual tangent gradient. These are
the analytic trial-function estimates used in the source eigenvalue comparison.
-/

namespace SlowEquilibration.SphericalForm
noncomputable section
open MeasureTheory Set
open SphericalModel SphericalAging.HardSphereDynamics
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable {N : ℕ}

def unnormalizedSphereIntegral (β : ℝ) (H f : Vector N → ℝ) : ℝ :=
  ∫ x, Real.exp (β*H x)*f x ∂sphereLaw N

lemma unnormalizedSphereIntegral_integrable (hN : 1 ≤ N) (β : ℝ)
    {H f : Vector N → ℝ} (hH : Continuous H) (hf : Continuous f) :
    Integrable (fun x => Real.exp (β*H x)*f x) (sphereLaw N) :=
  integrable_sphere_of_continuous hN ((Real.continuous_exp.comp
    (continuous_const.mul hH)).mul hf)

lemma integral_gibbsLaw_eq_unnormalized (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) (f : Vector N → ℝ) :
    (∫ x, f x ∂gibbsLaw N β H) = unnormalizedSphereIntegral β H f / partition N β H := by
  rw [integral_gibbsLaw hN β hH]
  unfold gibbsDensity unnormalizedSphereIntegral
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div]

lemma unnormalizedSphereIntegral_nonneg (hN : 1 ≤ N) (β : ℝ)
    (H f : Vector N → ℝ) (hf : ∀ x, OnSphere x → 0 ≤ f x) :
    0 ≤ unnormalizedSphereIntegral β H f := by
  apply integral_nonneg_of_ae
  filter_upwards [sphereLaw_support hN] with x hx
  exact mul_nonneg (Real.exp_pos _).le (hf x ((onSphere_iff_norm_sq x).mpr hx))

/-- Literal unnormalized density comparison, without a second partition
ratio or any comparison of centered variances. -/
theorem unnormalizedSphereIntegral_comparison (hN : 1 ≤ N) (β₀ β₁ : ℝ)
    {H₀ H₁ f : Vector N → ℝ} (hH₀ : Continuous H₀) (hH₁ : Continuous H₁)
    (hf : Continuous f) (hfn : ∀ x, OnSphere x → 0 ≤ f x)
    {l u : ℝ} (hl : ∀ x, OnSphere x → l ≤ β₁*H₁ x-β₀*H₀ x)
    (hu : ∀ x, OnSphere x → β₁*H₁ x-β₀*H₀ x ≤ u) :
    Real.exp l * unnormalizedSphereIntegral β₀ H₀ f ≤
      unnormalizedSphereIntegral β₁ H₁ f ∧
    unnormalizedSphereIntegral β₁ H₁ f ≤
      Real.exp u * unnormalizedSphereIntegral β₀ H₀ f := by
  have hi₀ := unnormalizedSphereIntegral_integrable hN β₀ hH₀ hf
  have hi₁ := unnormalizedSphereIntegral_integrable hN β₁ hH₁ hf
  constructor
  · simp only [unnormalizedSphereIntegral]
    rw [← integral_const_mul]
    apply integral_mono_ae (hi₀.const_mul _) hi₁
    filter_upwards [sphereLaw_support hN] with x hx
    have hs := (onSphere_iff_norm_sq x).mpr hx
    have he : Real.exp l * Real.exp (β₀*H₀ x) ≤ Real.exp (β₁*H₁ x) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith [hl x hs]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right he (hfn x hs)
  · simp only [unnormalizedSphereIntegral]
    rw [← integral_const_mul]
    apply integral_mono_ae hi₁ (hi₀.const_mul _)
    filter_upwards [sphereLaw_support hN] with x hx
    have hs := (onSphere_iff_norm_sq x).mpr hx
    have he : Real.exp (β₁*H₁ x) ≤ Real.exp u * Real.exp (β₀*H₀ x) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith [hu x hs]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right he (hfn x hs)

def smoothSphereRayleigh (β : ℝ) (H f : Vector N → ℝ) : ℝ :=
  dirichletEnergy N β H f / (∫ x, (f x)^2 ∂gibbsLaw N β H)

/-- The actual normalized Gibbs Rayleigh quotient equals its unnormalized
counterpart because the same positive partition cancels exactly. -/
theorem smoothSphereRayleigh_eq_unnormalized (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) (f : Vector N → ℝ) :
    smoothSphereRayleigh β H f =
      unnormalizedSphereIntegral β H (fun x => ‖surfaceGradient f x‖^2) /
      unnormalizedSphereIntegral β H (fun x => (f x)^2) := by
  rw [smoothSphereRayleigh, dirichletEnergy_eq_integral_norm_sq,
    integral_gibbsLaw_eq_unnormalized hN β hH,
    integral_gibbsLaw_eq_unnormalized hN β hH]
  exact div_div_div_cancel_right₀ (partition_pos hN β hH).ne' _ _

/-- Every actual C¹ spherical trial with nonzero L² mass has a Rayleigh
comparison with precisely one exponential oscillation factor. -/
theorem smoothSphereRayleigh_comparison (hN : 1 ≤ N) (β₀ β₁ : ℝ)
    {H₀ H₁ f : Vector N → ℝ} (hH₀ : Continuous H₀) (hH₁ : Continuous H₁)
    (hf : ContDiff ℝ 1 f)
    (hm : 0 < unnormalizedSphereIntegral β₀ H₀ (fun x => (f x)^2))
    {l u : ℝ} (hl : ∀ x, OnSphere x → l ≤ β₁*H₁ x-β₀*H₀ x)
    (hu : ∀ x, OnSphere x → β₁*H₁ x-β₀*H₀ x ≤ u) :
    smoothSphereRayleigh β₁ H₁ f ≤ Real.exp (u-l)*smoothSphereRayleigh β₀ H₀ f := by
  have hmass := unnormalizedSphereIntegral_comparison hN β₀ β₁ hH₀ hH₁
    (hf.continuous.pow 2) (fun _ _ => sq_nonneg _) hl hu
  have henergy := unnormalizedSphereIntegral_comparison hN β₀ β₁ hH₀ hH₁
    ((surfaceGradient_continuous hf).norm.pow 2) (fun _ _ => sq_nonneg _) hl hu
  have hden : 0 < unnormalizedSphereIntegral β₁ H₁ (fun x => (f x)^2) :=
    lt_of_lt_of_le (mul_pos (Real.exp_pos _) hm) hmass.1
  have hnum := unnormalizedSphereIntegral_nonneg hN β₀ H₀
    (fun x => ‖surfaceGradient f x‖^2) (fun _ _ => sq_nonneg _)
  rw [smoothSphereRayleigh_eq_unnormalized hN β₁ hH₁,
    smoothSphereRayleigh_eq_unnormalized hN β₀ hH₀]
  calc
    _ ≤ (Real.exp u * unnormalizedSphereIntegral β₀ H₀
        (fun x => ‖surfaceGradient f x‖^2)) /
        (Real.exp l * unnormalizedSphereIntegral β₀ H₀ (fun x => (f x)^2)) :=
      div_le_div₀ (mul_nonneg (Real.exp_pos _).le hnum) henergy.2
        (mul_pos (Real.exp_pos _) hm) hmass.1
    _ = _ := by rw [Real.exp_sub]; ring

end
end SlowEquilibration.SphericalForm

-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalRayleighComparison

/-! Actual Gibbs measure domination under bounded spherical energy differences. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalModel
open MeasureTheory Set SphericalForm SphericalAging.HardSphereDynamics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- One oscillation factor controls the entire normalized Gibbs measure. -/
theorem gibbsLaw_le_of_sphere_energy_bounds {N : ℕ} (hN : 1 ≤ N)
    (β₀ β₁ : ℝ) {H₀ H₁ : Vector N → ℝ} (hH₀ : Continuous H₀) (hH₁ : Continuous H₁)
    {l u : ℝ} (hl : ∀ x, OnSphere x → l ≤ β₁*H₁ x-β₀*H₀ x)
    (hu : ∀ x, OnSphere x → β₁*H₁ x-β₀*H₀ x ≤ u) :
    gibbsLaw N β₁ H₁ ≤ ENNReal.ofReal (Real.exp (u-l)) • gibbsLaw N β₀ H₀ := by
  have hZ := (unnormalizedSphereIntegral_comparison hN β₀ β₁ hH₀ hH₁
    continuous_const (fun _ _ => zero_le_one) hl hu).1
  simp only [unnormalizedSphereIntegral,mul_one] at hZ
  change Real.exp l*partition N β₀ H₀ ≤ partition N β₁ H₁ at hZ
  have hd : ∀ᵐ x ∂sphereLaw N,gibbsDensity N β₁ H₁ x ≤
      Real.exp (u-l)*gibbsDensity N β₀ H₀ x := by
    filter_upwards [sphereLaw_support hN] with x hx
    have hs := (onSphere_iff_norm_sq x).mpr hx
    have hn : Real.exp (β₁*H₁ x) ≤ Real.exp u*Real.exp (β₀*H₀ x) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [hu x hs])
    unfold gibbsDensity
    calc
      _ ≤ (Real.exp u*Real.exp (β₀*H₀ x))/(Real.exp l*partition N β₀ H₀) :=
        div_le_div₀ (by positivity) hn (mul_pos (Real.exp_pos _) (partition_pos hN β₀ hH₀)) hZ
      _ = _ := by rw [Real.exp_sub];ring
  unfold gibbsLaw
  rw [← withDensity_smul _ (gibbsDensity_continuous β₀ hH₀).measurable.ennreal_ofReal]
  apply withDensity_mono
  filter_upwards [hd] with x hx
  simpa only [Pi.smul_apply,smul_eq_mul,← ENNReal.ofReal_mul (Real.exp_nonneg _)] using
    ENNReal.ofReal_le_ofReal hx

theorem gibbsLaw_real_le_of_sphere_energy_bounds {N : ℕ} (hN : 1 ≤ N)
    (β₀ β₁ : ℝ) {H₀ H₁ : Vector N → ℝ} (hH₀ : Continuous H₀) (hH₁ : Continuous H₁)
    {l u : ℝ} (hl : ∀ x, OnSphere x → l ≤ β₁*H₁ x-β₀*H₀ x)
    (hu : ∀ x, OnSphere x → β₁*H₁ x-β₀*H₀ x ≤ u) (A : Set (Vector N)) :
    (gibbsLaw N β₁ H₁).real A ≤ Real.exp (u-l)*(gibbsLaw N β₀ H₀).real A := by
  let := gibbsLaw_probability hN β₀ hH₀
  let := gibbsLaw_probability hN β₁ hH₁
  have h := gibbsLaw_le_of_sphere_energy_bounds hN β₀ β₁ hH₀ hH₁ hl hu A
  have ht := ENNReal.toReal_mono (show (ENNReal.ofReal (Real.exp (u-l)) • gibbsLaw N β₀ H₀) A ≠ ⊤ by
    simp only [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) h
  simpa only [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_nonneg _),measureReal_def] using ht

end SlowEquilibration.SphericalModel

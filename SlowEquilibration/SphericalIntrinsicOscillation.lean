-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalIntrinsicSpectral
public import SlowEquilibration.SphericalOscillationComparison

/-! Source prop:inf-comparison for genuinely intrinsic potentials, with
their literal spherical oscillation and actual intrinsic spectral data. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalIntrinsicExtension
open Set
open SphericalModel SphericalForm SphericalSpectralComparison
open SphericalAging.HardSphereDynamics SphericalAging.SphericalIntegrationByParts
open scoped Topology Manifold ContDiff
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Literal supremum minus infimum of the intrinsic sphere function. -/
def intrinsicOscillation (n : ℕ) (H : RoundSphere n → ℝ) : ℝ :=
  sSup (range H)-sInf (range H)

theorem sphereValues_eq_intrinsic_of_extension (n : ℕ) (H : RoundSphere n → ℝ)
    (F : Vector (n+1) → ℝ) (he : ∀ x : RoundSphere n, F x=H x) :
    sphereValues F=range H := by
  ext r
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,(onSphere_iff_norm_sq x).mp hx⟩,(he ⟨x,(onSphere_iff_norm_sq x).mp hx⟩).symm⟩
  · rintro ⟨x,rfl⟩
    exact ⟨x,(onSphere_iff_norm_sq _).mpr x.property,he x⟩

theorem sphereOscillation_eq_intrinsic_of_extension (n : ℕ) (H : RoundSphere n → ℝ)
    (F : Vector (n+1) → ℝ) (he : ∀ x : RoundSphere n, F x=H x) :
    sphereOscillation F=intrinsicOscillation n H := by
  simp only [sphereOscillation,intrinsicOscillation,sphereValues_eq_intrinsic_of_extension n H F he]

theorem intrinsic_value_bounds (n : ℕ) (H : RoundSphere n → ℝ)
    (hH : IntrinsicContDiff n 1 H) (x : RoundSphere n) :
    sInf (range H) ≤ H x ∧ H x ≤ sSup (range H) := by
  have h := sphere_value_bounds (show 1 ≤ n+1 by omega)
    (ambientExtension_contDiff n 1 H hH).continuous x ((onSphere_iff_norm_sq _).mpr x.property)
  simpa only [sphereValues_eq_intrinsic_of_extension n H _ (ambientExtension_restrict n H),
    ambientExtension_restrict] using h

theorem intrinsicOscillation_nonneg (n : ℕ) (H : RoundSphere n → ℝ)
    (hH : IntrinsicContDiff n 1 H) : 0 ≤ intrinsicOscillation n H := by
  rw [← sphereOscillation_eq_intrinsic_of_extension n H _ (ambientExtension_restrict n H)]
  exact sphereOscillation_nonneg (by omega) (ambientExtension_contDiff n 1 H hH).continuous

theorem IntrinsicContDiff.add {n : ℕ} {m : ℕ∞} {H V : RoundSphere n → ℝ}
    (hH : IntrinsicContDiff n m H) (hV : IntrinsicContDiff n m V) :
    IntrinsicContDiff n m (H+V) := by
  exact ContMDiff.add hH hV

/-- Every actual intrinsic form eigenvalue obeys the source temperature
comparison with one literal intrinsic oscillation factor. -/
theorem intrinsic_temperature_eigenvalue_comparison (n : ℕ) (hn : 1 ≤ n) (β₀ β₁ : ℝ)
    (H : RoundSphere n → ℝ) (hH : IntrinsicContDiff n 1 H) (k : ℕ) :
    (intrinsicSpectralData n hn β₁ H hH).eigenvalue k ≤
      Real.exp (|β₁-β₀| * intrinsicOscillation n H)*
        (intrinsicSpectralData n hn β₀ H hH).eigenvalue k := by
  have h := temperature_eigenvalue_comparison (show 2 ≤ n+1 by omega) β₀ β₁
    (ambientExtension_contDiff n 1 H hH) k
  simpa only [intrinsicSpectralData,
    sphereOscillation_eq_intrinsic_of_extension n H _ (ambientExtension_restrict n H)] using h

/-- The source Hamiltonian perturbation bound refers to the actual
intrinsic sum H+V. Only restrictions of ambient representatives are used;
no additivity of the chosen extension is assumed. -/
theorem intrinsic_hamiltonian_eigenvalue_comparison (n : ℕ) (hn : 1 ≤ n)
    {β : ℝ} (hβ : 0 ≤ β) (H V : RoundSphere n → ℝ)
    (hH : IntrinsicContDiff n 1 H) (hV : IntrinsicContDiff n 1 V) (k : ℕ) :
    (intrinsicSpectralData n hn β (H+V) (hH.add hV)).eigenvalue k ≤
      Real.exp (β*intrinsicOscillation n V)*(intrinsicSpectralData n hn β H hH).eigenvalue k := by
  have hl : ∀ x : RoundSphere n, β*sInf (range V) ≤ β*(H+V) x-β*H x := by
    intro x
    have h := mul_le_mul_of_nonneg_left (intrinsic_value_bounds n V hV x).1 hβ
    simp only [Pi.add_apply]
    nlinarith
  have hu : ∀ x : RoundSphere n, β*(H+V) x-β*H x ≤ β*sSup (range V) := by
    intro x
    have h := mul_le_mul_of_nonneg_left (intrinsic_value_bounds n V hV x).2 hβ
    simp only [Pi.add_apply]
    nlinarith
  have h := intrinsic_eigenvalue_comparison n hn β β H (H+V) hH (hH.add hV) hl hu k
  have he : β*sSup (range V)-β*sInf (range V)=β*intrinsicOscillation n V := by
    unfold intrinsicOscillation
    ring
  rwa [he] at h

end SlowEquilibration.SphericalIntrinsicExtension

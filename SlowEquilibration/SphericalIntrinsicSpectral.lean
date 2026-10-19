-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalIntrinsicForm
public import SlowEquilibration.SphericalSpectralComparison

/-! The arbitrary intrinsic-potential scope of the actual spherical form
and eigenvalue comparison. Every smooth intrinsic test function belongs to
the actual ambient smooth core through the constructed extension. -/
@[expose] public section
namespace SlowEquilibration.SphericalIntrinsicExtension
open Set
open SphericalModel SphericalForm SphericalSpectralComparison
open SphericalAging.HardSphereDynamics SphericalAging.SphericalIntegrationByParts
open scoped ENNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual smooth form core contains a representative of every genuine
intrinsically smooth sphere function. -/
theorem intrinsic_smooth_core_surjective (n : ℕ) (f : RoundSphere n → ℝ)
    (hf : IntrinsicContDiff n (⊤ : ℕ∞) f) :
    ∃ F : smoothCore (n+1), ∀ x : RoundSphere n, F.1 x=f x :=
  ⟨⟨ambientExtension n f,ambientExtension_contDiff n (⊤ : ℕ∞) f hf⟩,ambientExtension_restrict n f⟩

theorem smooth_core_restrict_intrinsic (n : ℕ) (F : smoothCore (n+1)) :
    IntrinsicContDiff n (⊤ : ℕ∞) (fun x : RoundSphere n => F.1 x) :=
  intrinsicContDiff_restrict n (⊤ : ℕ∞) F.1 (smoothCore_contDiff F)

/-- The normalized spectral data is constructed from the genuine spherical
form for the explicitly extended intrinsic potential. Its Gibbs law and
every smooth form pairing are the actual intrinsic ones by the preceding file. -/
def intrinsicSpectralData (n : ℕ) (hn : 1 ≤ n) (β : ℝ) (H : RoundSphere n → ℝ)
    (hH : IntrinsicContDiff n 1 H) :=
  normalizedSphericalSpectralData (show 2 ≤ n+1 by omega) β (ambientExtension n H)
    (ambientExtension_contDiff n 1 H hH).continuous

/-- Source eigenvalue comparison for genuinely intrinsic C¹ potentials;
in particular this covers every intrinsically C² or smooth potential. -/
theorem intrinsic_eigenvalue_comparison (n : ℕ) (hn : 1 ≤ n) (β₀ β₁ : ℝ)
    (H₀ H₁ : RoundSphere n → ℝ) (hH₀ : IntrinsicContDiff n 1 H₀) (hH₁ : IntrinsicContDiff n 1 H₁)
    {l u : ℝ} (hl : ∀ x : RoundSphere n, l ≤ β₁*H₁ x-β₀*H₀ x)
    (hu : ∀ x : RoundSphere n, β₁*H₁ x-β₀*H₀ x ≤ u) (k : ℕ) :
    (intrinsicSpectralData n hn β₁ H₁ hH₁).eigenvalue k ≤
      Real.exp (u-l)*(intrinsicSpectralData n hn β₀ H₀ hH₀).eigenvalue k := by
  apply normalized_eigenvalue_comparison (show 2 ≤ n+1 by omega) β₀ β₁
    (ambientExtension_contDiff n 1 H₀ hH₀) (ambientExtension_contDiff n 1 H₁ hH₁)
  · intro x hx
    have hx' := (onSphere_iff_norm_sq x).mp hx
    have h := hl ⟨x,hx'⟩
    rw [← ambientExtension_restrict n H₀ ⟨x,hx'⟩,← ambientExtension_restrict n H₁ ⟨x,hx'⟩] at h
    exact h
  · intro x hx
    have hx' := (onSphere_iff_norm_sq x).mp hx
    have h := hu ⟨x,hx'⟩
    rw [← ambientExtension_restrict n H₀ ⟨x,hx'⟩,← ambientExtension_restrict n H₁ ⟨x,hx'⟩] at h
    exact h

end
end SlowEquilibration.SphericalIntrinsicExtension

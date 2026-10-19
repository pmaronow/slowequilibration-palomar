-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalInfiniteSharpTail
public import SlowEquilibration.SphericalInfiniteIntrinsic
public import SlowEquilibration.SphericalIntrinsicOscillation

/-! Actual pathwise spectral truncation of the infinite mixture. The compared
spectra are those of the literal normalized weighted round-sphere forms. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open Set SphericalModel SphericalIntrinsicExtension SphericalForm SphericalSpectralComparison
open SphericalAging.HardSphereDynamics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem partialField_contDiff {N : ℕ} (μ : InfiniteMixture) (P : ℕ) (J : Disorder N) :
    ContDiff ℝ 2 (partialField μ P J) := by
  unfold partialField
  exact ContDiff.sum (fun p _ => (block_contDiff μ p J).of_le le_top)

/-- The finite truncation's actual compact L² spectrum on the same sphere. -/
def partialSpectralData (n : ℕ) (hn : 1≤n) (β : ℝ) (μ : InfiniteMixture)
    (P : ℕ) (J : Disorder (n+1)) :=
  normalizedSphericalSpectralData (show 2≤n+1 by omega) β (partialField μ P J)
    (partialField_contDiff μ P J).continuous

theorem intrinsic_tail_abs_le (n : ℕ) (μ : InfiniteMixture) (P : ℕ)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (x : RoundSphere n) :
    |field μ J x-partialField μ P J x|≤‖tailSphere μ P J‖ := by
  have he : (unitToBall (n+1) (roundToUnit n x)).val=x.val := by
    change Real.sqrt (n+1:ℕ) • ((Real.sqrt (n+1:ℕ))⁻¹ • x.val)=x.val
    rw [smul_smul,mul_inv_cancel₀ (Real.sqrt_pos.mpr (by positivity)).ne',one_smul]
  have hh := (tailSphere μ P J).norm_coe_le_norm (roundToUnit n x)
  change |tailContinuous μ P J (unitToBall (n+1) (roundToUnit n x))|≤_ at hh
  rw [tailContinuous_eq_sub (by omega) μ P J hJ] at hh
  simpa only [he] using hh

/-- Literal infinite-versus-cutoff eigenvalue comparison, with one oscillation
factor and no assumption that the ambient extension preserves addition. -/
theorem infinite_eigenvalue_le_partial_of_tail_bound (n : ℕ) (hn : 1≤n) (μ : InfiniteMixture)
    (P : ℕ) (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ)
    {β h : ℝ} (hβ : 0≤β) (htail : ‖tailSphere μ P J‖≤h*(n+1:ℕ)) (k : ℕ) :
    (infiniteSpectralData n hn β μ J).eigenvalue k≤
      Real.exp (2*β*h*(n+1:ℕ))*(partialSpectralData n hn β μ P J).eigenvalue k := by
  have hr (x : RoundSphere n) : regularAmbientField n μ J x=field μ J x := by
    rw [regularAmbientField,if_pos hJ,ambientExtension_restrict]
    rfl
  have hd (x : Vector (n+1)) (hx : OnSphere x) :
      |regularAmbientField n μ J x-partialField μ P J x|≤h*(n+1:ℕ) := by
    let y : RoundSphere n := ⟨x,(onSphere_iff_norm_sq x).mp hx⟩
    change |regularAmbientField n μ J y-partialField μ P J y|≤_
    rw [hr y]
    exact (intrinsic_tail_abs_le n μ P J hJ y).trans htail
  have hl : ∀ x,OnSphere x → -(β*h*(n+1:ℕ))≤β*regularAmbientField n μ J x-β*partialField μ P J x := by
    intro x hx
    have hh := mul_le_mul_of_nonneg_left (abs_le.mp (hd x hx)).1 hβ
    nlinarith
  have hu : ∀ x,OnSphere x → β*regularAmbientField n μ J x-β*partialField μ P J x≤β*h*(n+1:ℕ) := by
    intro x hx
    have hh := mul_le_mul_of_nonneg_left (abs_le.mp (hd x hx)).2 hβ
    nlinarith
  have he := normalized_eigenvalue_comparison (show 2≤n+1 by omega) β β
    ((partialField_contDiff μ P J).of_le (by norm_num))
    ((regularAmbientField_contDiff n μ J).of_le (by norm_num)) hl hu k
  convert he using 1 <;> congr 2 <;> ring

end SlowEquilibration.SphericalInfiniteModel

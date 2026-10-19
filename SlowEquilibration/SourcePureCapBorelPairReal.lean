-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapBorelPairRadialBound

/-! The arbitrary-Borel pure posterior pair comparison in the ordinary
real integrals used by the original-field Fubini identities. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapBorelPairReal
noncomputable section
open Set Filter MeasureTheory
open SphericalModel SphericalMarkedWindows PureStationarity
open SphericalPureOriginalConditionalBandFubini
open SourcePureCapPosteriorPairIntegrable
open SourcePureCapBorelPairRadialBound
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem pure_original_borel_band_sphere_pair_real_bound
    (p : ℕ) (hp : 2 ≤ p) (β : ℝ)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hsub : pureResidualCoefficient p β a < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+1)), ‖u‖^2=(n+1 : ℕ) →
      ∀ (H : ℝ), ∀ (I : Set ℝ), MeasurableSet I → I ⊆ Ico a 1 →
      (∫ z : Vector (n+1) × Vector (n+1),
        ((overlapRegion u I) ×ˢ (overlapRegion u I)).indicator
          (originalPurePairMeanProfile n p 1 β H u) z
        ∂(sphereLaw (n+1)).prod (sphereLaw (n+1))) ≤
        C * (∫ w : Vector (n+1),
          (overlapRegion u I).indicator
            (originalPureMeanProfile n p 1 β H u) w
          ∂sphereLaw (n+1))^2 := by
  obtain ⟨C,hC,hBound⟩ := pure_original_borel_band_sphere_pair_bound
    p hp β ha hsub
  refine ⟨C,hC,?_⟩
  filter_upwards [hBound] with n hn
  intro u hu H I hI hIcap
  let B := overlapRegion u I
  have hB : MeasurableSet B := overlapRegion_measurable u hI
  have hBB : MeasurableSet (B ×ˢ B) := hB.prod hB
  let P₁ := B.indicator (originalPureMeanProfile n p 1 β H u)
  let P₂ := (B ×ˢ B).indicator (originalPurePairMeanProfile n p 1 β H u)
  have hi₁ : Integrable P₁ (sphereLaw (n+1)) :=
    (integrable_sphere_of_continuous (by omega)
      (originalPureMeanProfile_continuous n p 1 β H u)).indicator hB
  have hi₂ : Integrable P₂ ((sphereLaw (n+1)).prod (sphereLaw (n+1))) :=
    ((memLp_spherePair_continuous (by omega : 1 ≤ n+1)
      (originalPurePairMeanProfile_continuous n p 1 β H u) 1).integrable le_rfl).indicator hBB
  have hnonneg₁ : 0 ≤ᵐ[sphereLaw (n+1)] P₁ := by
    apply Filter.Eventually.of_forall
    intro w
    by_cases hw : w ∈ B
    · simp only [P₁,Set.indicator_of_mem hw,originalPureMeanProfile]
      positivity
    · simp [P₁,Set.indicator_of_notMem hw]
  have hnonneg₂ : 0 ≤ᵐ[(sphereLaw (n+1)).prod (sphereLaw (n+1))] P₂ := by
    apply Filter.Eventually.of_forall
    intro z
    by_cases hz : z ∈ B ×ˢ B
    · simp only [P₂,Set.indicator_of_mem hz]
      unfold originalPurePairMeanProfile originalPureMeanProfile
      positivity
    · simp [P₂,Set.indicator_of_notMem hz]
  have h₁ : 0 ≤ ∫ w, P₁ w ∂sphereLaw (n+1) := integral_nonneg_of_ae hnonneg₁
  have h₂ := ofReal_integral_eq_lintegral_ofReal hi₂ hnonneg₂
  have h₁eq := ofReal_integral_eq_lintegral_ofReal hi₁ hnonneg₁
  have hENN := hn u hu H I hI hIcap
  change (∫⁻ z, ENNReal.ofReal (P₂ z)
      ∂(sphereLaw (n+1)).prod (sphereLaw (n+1))) ≤
    ENNReal.ofReal C * (∫⁻ w, ENNReal.ofReal (P₁ w) ∂sphereLaw (n+1))^2 at hENN
  rw [←h₂,←h₁eq,←ENNReal.ofReal_pow h₁,←ENNReal.ofReal_mul hC.le] at hENN
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hENN

end
end SlowEquilibration.SourcePureCapBorelPairReal

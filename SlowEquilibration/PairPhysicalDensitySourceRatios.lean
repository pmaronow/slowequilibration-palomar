-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PhysicalScoreDensityIdentification

/-! Sharp density ratios with the literal existing one-point densities from
the actual field's Kac--Rice disintegration. The pure case retains two marks
and Jacobian N, while the non-pure case retains four marks and Jacobian N². -/
@[expose] public section
namespace SlowEquilibration.PairObservationSmallOverlap
noncomputable section
open SphericalModel SphericalGaussianJet NormalizedPairObservations
open SphericalSequentialRegression
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Proper energy-only source density ratio. No radial mark or non-purity
assumption appears, so this applies directly to compatible pure marks. -/
theorem uniform_source_pair_value_density_ratio (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hdeg : 4 ≤ μ.minDegree) (M : ℝ) (hM : 0 ≤ M) :
    ∃ ρ0 K : ℝ,0 < ρ0 ∧ 0 < K ∧ ∀ (N m : ℕ) (_hN : 0 < N) (x y : Vector N),
      ‖x‖^2=(N:ℝ) → ‖y‖^2=(N:ℝ) →
      ∀ (e f : Fin m → Vector N),Orthonormal ℝ e → Orthonormal ℝ f →
      (∀ i,inner ℝ (e i) x=0) → (∀ i,inner ℝ (f i) y=0) → |overlap x y| ≤ ρ0 →
      ∀ h1 h2 : ℝ,|h1| ≤ M → |h2| ≤ M →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      |Real.log (physicalPairValueDensity N (residualPairValue c x y e f) h1 h2 /
        ((normalizedValuePdf c x h1).toReal*(normalizedValuePdf c y h2).toReal))| ≤
          K*(N:ℝ)*|overlap x y|^μ.minDegree := by
  obtain ⟨ρ0,K,hρ0,hK,hall⟩:=uniform_physical_value_density_ratio μ hQ hdeg M hM
  refine ⟨ρ0,K,hρ0,hK,?_⟩
  intro N m hN x y hx hy e f he hf htanx htany hρ h1 h2 hh1 hh2
  dsimp only
  rw [← physicalValueDensity_eq_normalizedValuePdf hN μ hQ x hx h1,
    ← physicalValueDensity_eq_normalizedValuePdf hN μ hQ y hy h2]
  exact hall N m hN x y hx hy e f he hf htanx htany hρ h1 h2 hh1 hh2

/-- Non-pure four-mark source density ratio, with genuine N² Jacobian and
both literal actual normalized score densities in its denominator. -/
theorem uniform_source_pair_score_density_ratio (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (hdeg : 4 ≤ μ.minDegree) (M : ℝ) (hM : 0 ≤ M) :
    ∃ ρ0 K : ℝ,0 < ρ0 ∧ 0 < K ∧ ∀ (N m : ℕ) (_hN : 0 < N) (x y : Vector N),
      ‖x‖^2=(N:ℝ) → ‖y‖^2=(N:ℝ) →
      ∀ (e f : Fin m → Vector N),Orthonormal ℝ e → Orthonormal ℝ f →
      (∀ i,inner ℝ (e i) x=0) → (∀ i,inner ℝ (f i) y=0) → |overlap x y| ≤ ρ0 →
      ∀ h1 k1 h2 k2 : ℝ,|h1| ≤ M → |k1| ≤ M → |h2| ≤ M → |k2| ≤ M →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      |Real.log (physicalPairScoreDensity N (residualPairScore c x y e f) h1 k1 h2 k2 /
        ((normalizedScorePdf c x (WithLp.toLp 2 ![h1,k1])).toReal*
          (normalizedScorePdf c y (WithLp.toLp 2 ![h2,k2])).toReal))| ≤
          K*(N:ℝ)*|overlap x y|^μ.minDegree := by
  obtain ⟨ρ0,K,hρ0,hK,hall⟩:=uniform_physical_score_density_ratio μ hQ hnp hdeg M hM
  refine ⟨ρ0,K,hρ0,hK,?_⟩
  intro N m hN x y hx hy e f he hf htanx htany hρ h1 k1 h2 k2 hh1 hk1 hh2 hk2
  dsimp only
  rw [← physicalScoreDensity_eq_normalizedScorePdf hN μ hQ hnp x hx h1 k1,
    ← physicalScoreDensity_eq_normalizedScorePdf hN μ hQ hnp y hy h2 k2]
  exact hall N m hN x y hx hy e f he hf htanx htany hρ h1 k1 h2 k2 hh1 hk1 hh2 hk2

end
end SlowEquilibration.PairObservationSmallOverlap

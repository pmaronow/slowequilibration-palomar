-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetPairMoment

@[expose] public section

/-! Whole two-point quadratic-bank law under the literal physical mixed
Palm kernel, including integrability of its exponential moments. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open ConditionedDeterminantMoments
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option linter.style.haveILetI false

theorem quadraticLatitudeJetPair_physicalMixedPalm_map
    {n : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a : ℝ) (u : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (ω ω' : Vector (n+2))
    (hω : inner ℝ ω u=0) (hω' : inner ℝ ω' u=0)
    (z : EuclideanSpace ℝ (Fin 2)) :
    (mixedLaw μ Q u hu z).map (quadraticLatitudeJetPair μ a u ω ω') =
      (disorderLaw (n+2) μ.maxDegree).map
        (quadraticLatitudeJetPair μ a u ω ω') := by
  let F := fun J : Disorder (n+2) μ.maxDegree =>
    flatQuadraticLatitudeJetFamily μ a u ![ω,ω'] (euclideanDisorder J)
  have hF : Measurable F := by
    unfold F
    exact (flatQuadraticLatitudeJetFamily μ a u ![ω,ω']).continuous.measurable.comp
      ((PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Coordinate (n+2) μ.maxDegree => ℝ)).symm.continuous.measurable.comp
        (flatDisorder_measurable (n+2) μ.maxDegree))
  let g : EuclideanSpace ℝ (Fin 2) → ℝ := fun v => v 0+v 1
  have hg : Measurable g := by fun_prop
  have hmap := quadraticLatitudeJetFamily_physicalMixedPalm_marginal
    μ hμ Q a u hu ![ω,ω'] (by intro i; fin_cases i <;> assumption) z
  change (mixedLaw μ Q u hu z).map F=(disorderLaw (n+2) μ.maxDegree).map F at hmap
  have hh := congrArg (fun ν : Measure (EuclideanSpace ℝ (Fin 2)) => ν.map g) hmap
  rw [Measure.map_map hg hF, Measure.map_map hg hF] at hh
  have hpoint : g ∘ F = quadraticLatitudeJetPair μ a u ω ω' := by
    funext J
    simp [g,F,quadraticLatitudeJetPair]
  rw [hpoint] at hh
  exact hh

theorem quadraticLatitudeJetPair_physicalMixedPalm_hasGaussianLaw
    {n : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a : ℝ) (u : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (ω ω' : Vector (n+2))
    (hω : inner ℝ ω u=0) (hω' : inner ℝ ω' u=0)
    (z : EuclideanSpace ℝ (Fin 2)) :
    HasGaussianLaw (quadraticLatitudeJetPair μ a u ω ω')
      (mixedLaw μ Q u hu z) := by
  have hG := quadraticLatitudeJetPair_hasGaussianLaw μ a u ω ω'
  have hmap := quadraticLatitudeJetPair_physicalMixedPalm_map
    μ hμ Q a u hu ω ω' hω hω' z
  haveI : IsGaussian ((mixedLaw μ Q u hu z).map
      (quadraticLatitudeJetPair μ a u ω ω')) := by
    rw [hmap]
    exact hG.isGaussian_map
  have hm : Measurable (quadraticLatitudeJetPair μ a u ω ω') := by
    convert ((((1-a^2)/2) • jetCLM (mixtureCoefficients μ) 2 (a • u) ![ω,ω] +
      ((1-a^2)/2) • jetCLM (mixtureCoefficients μ) 2 (a • u) ![ω',ω']).continuous.measurable) using 1
    funext J
    simp [quadraticLatitudeJetPair,quadraticLatitudeJet]
  exact IsGaussian.hasGaussianLaw hm.aemeasurable

theorem quadraticLatitudeJetPair_physicalMixedPalm_exp_integrable
    {n : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a β : ℝ) (u : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (ω ω' : Vector (n+2))
    (hω : inner ℝ ω u=0) (hω' : inner ℝ ω' u=0)
    (z : EuclideanSpace ℝ (Fin 2)) :
    Integrable (fun J => Real.exp (β*quadraticLatitudeJetPair μ a u ω ω' J))
      (mixedLaw μ Q u hu z) := by
  have hG := quadraticLatitudeJetPair_physicalMixedPalm_hasGaussianLaw
    μ hμ Q a u hu ω ω' hω hω' z
  exact (show HasLaw (quadraticLatitudeJetPair μ a u ω ω')
      (gaussianReal (∫ J,quadraticLatitudeJetPair μ a u ω ω' J
        ∂mixedLaw μ Q u hu z)
        (variance (quadraticLatitudeJetPair μ a u ω ω')
          (mixedLaw μ Q u hu z)).toNNReal)
      (mixedLaw μ Q u hu z) from
      ⟨hG.aemeasurable,hG.map_eq_gaussianReal⟩).integrable_comp
        (integrable_exp_mul_gaussianReal β)

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance

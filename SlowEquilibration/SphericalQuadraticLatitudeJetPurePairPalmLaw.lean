-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetPurePalmMarginal
public import SlowEquilibration.SphericalQuadraticLatitudeJetPairMoment

@[expose] public section

/-! Every two-point original Y₂ latitude probe has its full centered
Gaussian law under the exact proper-pure scalar-value Palm posterior. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open SphericalMarkedWindows
open SphericalTAPCriticalAnalyticNeighborhood
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option linter.style.haveILetI false

theorem quadraticLatitudeJetPair_physicalPurePalm_map
    {n : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a : ℝ) (u : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (ω ω' : Vector (n+2))
    (hω : inner ℝ ω u=0) (hω' : inner ℝ ω' u=0)
    (b : ℝ) :
    (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b).map
      (quadraticLatitudeJetPair μ a u ω ω') =
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
  have hmap := quadraticLatitudeJetFamily_physicalPurePalm_marginal
    μ hμ Q a u hu ![ω,ω'] (by intro i; fin_cases i <;> assumption) b
  change (valueConditionedLaw
      (centerCoefficients (mixtureCoefficients μ) Q) u hu b).map F =
    (disorderLaw (n+2) μ.maxDegree).map F at hmap
  have hh := congrArg (fun ν : Measure (EuclideanSpace ℝ (Fin 2)) => ν.map g) hmap
  rw [Measure.map_map hg hF, Measure.map_map hg hF] at hh
  have hpoint : g ∘ F = quadraticLatitudeJetPair μ a u ω ω' := by
    funext J
    simp [g,F,quadraticLatitudeJetPair]
  rw [hpoint] at hh
  exact hh

theorem quadraticLatitudeJetPair_physicalPurePalm_exp_integrable
    {n : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a β : ℝ) (u : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (ω ω' : Vector (n+2))
    (hω : inner ℝ ω u=0) (hω' : inner ℝ ω' u=0)
    (b : ℝ) :
    Integrable (fun J => Real.exp (β*quadraticLatitudeJetPair μ a u ω ω' J))
      (valueConditionedLaw
        (centerCoefficients (mixtureCoefficients μ) Q) u hu b) := by
  let ν := valueConditionedLaw
    (centerCoefficients (mixtureCoefficients μ) Q) u hu b
  have hmap := quadraticLatitudeJetPair_physicalPurePalm_map
    μ hμ Q a u hu ω ω' hω hω' b
  have hm : Measurable (quadraticLatitudeJetPair μ a u ω ω') := by
    convert ((((1-a^2)/2) • jetCLM (mixtureCoefficients μ) 2 (a • u) ![ω,ω] +
      ((1-a^2)/2) • jetCLM (mixtureCoefficients μ) 2 (a • u) ![ω',ω']).continuous.measurable) using 1
    funext J
    simp [quadraticLatitudeJetPair,quadraticLatitudeJet]
  have hG := quadraticLatitudeJetPair_hasGaussianLaw μ a u ω ω'
  have hLaw : HasLaw (quadraticLatitudeJetPair μ a u ω ω')
      (gaussianReal (∫ J,quadraticLatitudeJetPair μ a u ω ω' J
        ∂disorderLaw (n+2) μ.maxDegree)
        (variance (quadraticLatitudeJetPair μ a u ω ω')
          (disorderLaw (n+2) μ.maxDegree)).toNNReal) ν := by
    refine ⟨hm.aemeasurable,?_⟩
    rw [hmap]
    exact hG.map_eq_gaussianReal
  exact hLaw.integrable_comp (integrable_exp_mul_gaussianReal β)

theorem quadraticLatitudeJetPair_physicalPurePalm_exp_integral
    {n : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a β : ℝ) (u : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (ω ω' : Vector (n+2))
    (hω : inner ℝ ω u=0) (hω' : inner ℝ ω' u=0)
    (b : ℝ) :
    (∫ J, Real.exp (β*quadraticLatitudeJetPair μ a u ω ω' J)
      ∂valueConditionedLaw
        (centerCoefficients (mixtureCoefficients μ) Q) u hu b) =
      Real.exp (β^2*((n+2:ℕ):ℝ)*sourceQuadraticLatitudeVariance μ a *
        ((overlap ω ω)^2 + 2*(overlap ω ω')^2 + (overlap ω' ω')^2)/2) := by
  have hm : Measurable (quadraticLatitudeJetPair μ a u ω ω') := by
    convert ((((1-a^2)/2) • jetCLM (mixtureCoefficients μ) 2 (a • u) ![ω,ω] +
      ((1-a^2)/2) • jetCLM (mixtureCoefficients μ) 2 (a • u) ![ω',ω']).continuous.measurable) using 1
    funext J
    simp [quadraticLatitudeJetPair,quadraticLatitudeJet]
  have hmap := quadraticLatitudeJetPair_physicalPurePalm_map
    μ hμ Q a u hu ω ω' hω hω' b
  have hint := congrArg (fun ν : Measure ℝ =>
    ∫ t, Real.exp (β*t) ∂ν) hmap
  have hg : StronglyMeasurable (fun t : ℝ => Real.exp (β*t)) := by
    fun_prop
  rw [integral_map hm.aemeasurable hg.aestronglyMeasurable,
    integral_map hm.aemeasurable hg.aestronglyMeasurable] at hint
  change (∫ J, Real.exp (β*quadraticLatitudeJetPair μ a u ω ω' J)
    ∂valueConditionedLaw
      (centerCoefficients (mixtureCoefficients μ) Q) u hu b) = _
  rw [hint]
  exact quadraticLatitudeJetPair_exp_integral (by omega) μ a β u ω ω' hu hω hω'

theorem quadraticLatitudeJetPair_physicalPurePalm_exp_integral_transverse
    {d : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a β : ℝ) (u : Vector (d+2))
    (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (y z : Vector (d+1))
    (hy : ‖y‖^2=((d+1:ℕ):ℝ)) (hz : ‖z‖^2=((d+1:ℕ):ℝ))
    (b : ℝ) :
    (∫ J, Real.exp (β*quadraticLatitudeJetPair μ a u
      (quadraticBankDirection (d+1) u y)
      (quadraticBankDirection (d+1) u z) J)
      ∂valueConditionedLaw
        (centerCoefficients (mixtureCoefficients μ) Q) u hu b) =
      Real.exp (β^2*((d+2:ℕ):ℝ)*sourceQuadraticLatitudeVariance μ a *
        (1+(overlap y z)^2)) := by
  rw [quadraticLatitudeJetPair_physicalPurePalm_exp_integral
    μ hμ Q a β u hu _ _
    (quadraticBankDirection_tangent u hu y)
    (quadraticBankDirection_tangent u hu z) b]
  rw [overlap_self (by omega) _
      (quadraticBankDirection_norm_sq (by omega) u y hy),
    overlap_self (by omega) _
      (quadraticBankDirection_norm_sq (by omega) u z hz),
    quadraticBankDirection_overlap (by omega)]
  congr 1
  ring

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance

-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalWeightedVariationalOperator

/-! Exact uniqueness and literal integral pairing of the actual weighted
operator on the completed spherical graph. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal BoundedContinuousFunction InnerProductSpace BigOperators
namespace SlowEquilibration.SphericalForm
open SphericalModel
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

theorem boundedMultiplication_pairing (μ : Measure (Vector N)) (ρ : Vector N→ᵇℝ)
    (u v : Lp ℝ 2 μ) :
    inner ℝ (BoundedContinuousL2Multiplication.operator μ ρ u) v=
      ∫ x,ρ x*u x*v x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [BoundedContinuousL2Multiplication.operator_ae μ ρ u] with x hx
  simp only [RCLike.inner_apply,conj_trivial,hx]
  ring

theorem sphericalWeightedOperator_integral (hN : 1≤N) (β : ℝ) (H : Vector N→ℝ)
    (hH : Continuous H) (ρ σ : Vector N→ᵇℝ) (u v : sphericalSobolevGraph hN β H hH) :
    inner ℝ (sphericalWeightedOperator hN β H hH ρ σ u) v=
      (∑ ij : Fin N×Fin N,∫ x,ρ x*u.val.snd ij x*v.val.snd ij x ∂gibbsLaw N β H)+
      ∫ x,σ x*u.val.fst x*v.val.fst x ∂gibbsLaw N β H := by
  rw [sphericalWeightedOperator_inner]
  simp only [boundedMultiplication_pairing]

theorem sphericalWeightedSolution_unique (hN : 1≤N) (β : ℝ) (H : Vector N→ℝ)
    (hH : Continuous H) (ρ σ : Vector N→ᵇℝ) (c : ℝ) (hc : 0<c)
    (hρ : ∀ᵐ x ∂gibbsLaw N β H,c≤ρ x) (hσ : ∀ᵐ x ∂gibbsLaw N β H,c≤σ x)
    (f : Lp ℝ 2 (gibbsLaw N β H)) (u : sphericalSobolevGraph hN β H hH)
    (hu : ∀ v,inner ℝ (sphericalWeightedOperator hN β H hH ρ σ u) v=inner ℝ f v.val.fst) :
    u=sphericalWeightedSolution hN β H hH ρ σ f := by
  let s := sphericalWeightedSolution hN β H hH ρ σ f
  have hz : inner ℝ (sphericalWeightedOperator hN β H hH ρ σ (u-s)) (u-s)=0 := by
    rw [map_sub,inner_sub_left,hu,sphericalWeightedSolution_equation hN β H hH ρ σ c hc hρ hσ]
    exact sub_self _
  have hnorm := sphericalWeightedOperator_coercive hN β H hH ρ σ c hρ hσ (u-s)
  rw [hz] at hnorm
  have hm : c*‖u-s‖^2=0 := le_antisymm hnorm (mul_nonneg hc.le (sq_nonneg _))
  have hsq := (mul_eq_zero.mp hm).resolve_left (ne_of_gt hc)
  have hn : ‖u-s‖=0 := by nlinarith [norm_nonneg (u-s),hsq]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

end SlowEquilibration.SphericalForm

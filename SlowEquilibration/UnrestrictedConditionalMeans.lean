-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConditionedDeterminantMoments
public import SlowEquilibration.GOEAllShiftPositivity

/-! Every-target positive ordinary conditional intrinsic determinant means,
with proper pure conditioning and no outside-edge restriction. -/

@[expose] public section
namespace SlowEquilibration.UnrestrictedConditionalMeans

noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet GOERawMoments GOEPhysicalPotential
open ConditionedDeterminantMoments UnrestrictedConditionedDeterminants
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual physical mean μ_(m,N)(k) is positive at every real k. -/
theorem physicalMean_all_shift_pos (n : ℕ) {N : ℕ} (hN : 0 < N)
    {b : ℝ} (hb : 0 < b) (k : ℝ) : 0 < physicalMean n N b k := by
  have h := GOEAllShiftPositivity.abs_determinant_mean_pos (n+1) hN hb k
  simpa only [shifted_abs_det,physicalMean] using h

/-- Actual nonpure whole-coefficient posterior mean equals the literal
ordinary physical GOE expectation and is positive for EVERY score target. -/
theorem mixed_conditional_mean {n : ℕ} (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (x : Vector (n+2)) (hx : ‖x‖^2=(n+2 : ℕ)) (z : EuclideanSpace ℝ (Fin 2)) :
    Integrable (intrinsicDet μ Q x) (mixedLaw μ Q x hx z) ∧
    (∫ J,intrinsicDet μ Q x J ∂mixedLaw μ Q x hx z)=
      physicalMean n (n+2) (Q^2*μ.xi2 Q) (z 1) ∧
    0 < ∫ J,intrinsicDet μ Q x J ∂mixedLaw μ Q x hx z := by
  have hi := mixed_intrinsicDet_integrable μ hQ hnp x hx z
  have he := determinant_mean_eq_of_law (mixed_intrinsicDet_hasLaw μ hQ hnp x hx z)
  refine ⟨hi,he,?_⟩
  rw [he]
  exact physicalMean_all_shift_pos n (by omega)
    (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)) _

/-- Proper pure value/tangent conditioning has a positive ordinary determinant
mean at every h, with true radial shift ph and redundant radial data omitted. -/
theorem pure_conditional_mean {n : ℕ} (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) {Q : ℝ} (hQ : 0 < Q)
    (x : Vector (n+2)) (hx : ‖x‖^2=(n+2 : ℕ)) (h : ℝ) :
    let μ := FiniteMixture.pure p hp alpha halpha
    Integrable (intrinsicDet μ Q x) (pureLaw p hp alpha halpha Q x hx h) ∧
    (∫ J,intrinsicDet μ Q x J ∂pureLaw p hp alpha halpha Q x hx h)=
      physicalMean n (n+2) (Q^2*μ.xi2 Q) ((p:ℝ)*h) ∧
    0 < ∫ J,intrinsicDet μ Q x J ∂pureLaw p hp alpha halpha Q x hx h := by
  let μ := FiniteMixture.pure p hp alpha halpha
  have hi := pure_intrinsicDet_integrable p hp alpha halpha hQ x hx h
  have he := determinant_mean_eq_of_law (pure_intrinsicDet_hasLaw p hp alpha halpha hQ x hx h)
  refine ⟨hi,he,?_⟩
  rw [he]
  exact physicalMean_all_shift_pos n (by omega)
    (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)) _

end
end SlowEquilibration.UnrestrictedConditionalMeans

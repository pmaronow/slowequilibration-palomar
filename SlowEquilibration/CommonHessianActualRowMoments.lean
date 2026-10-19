-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianRowMoments
public import SlowEquilibration.CommonHessianValueRowRegressionBounds
public import SlowEquilibration.GaussianNormShiftMoment

/-! Ordinary common-row moments under the original tensor posterior. The
centered covariance and actual small-overlap regression mean are both proved.
-/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianRegressionCovariance SphericalConditionalMatrices
open NormalizedPairObservations PairHessianMean PairObservationNormBounds GaussianObservationCoercivity
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

theorem actual_common_row_mixed_norm_moments {N P m k d : ℕ}
    (hN : 0 < N) (hmN : m ≤ N) (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (hb : 0 < secondCovariance c 1) (hd : 3 ≤ d)
    (hdeg : ∀ p, c p ≠ 0 → d ≤ p.val.val)
    (x y v : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) (hy : ‖y‖ ^ 2 = (N : ℝ))
    (hv : ‖v‖ = 1) (hvtan : inner ℝ v x = 0)
    (e : Fin m → Vector N) (he : Orthonormal ℝ e)
    (htanx : ∀ i, inner ℝ (e i) x = 0) (htany : ∀ i, inner ℝ (e i) y = 0)
    (hve : ∀ i, inner ℝ (e i) v = 0)
    (f g : Fin k → Vector N) (hg : Orthonormal ℝ g) (hr : |overlap x y| ≤ 1)
    {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hA : Surjective (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)))
    (hinv : ‖(gram (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g))).inverse‖ ≤ 1 / δ)
    (w : WithLp 2 (MixedObservationSpace k × MixedObservationSpace k))
    (hw : ‖w‖ ≤ M * Real.sqrt (N : ℝ)) :
    let A := pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)
    ∀ r : ℕ,
      Integrable (fun J : Disorder N P => ‖actualObservation (commonRowCLM c x e v) J‖ ^ r)
        (coefficientKernel A w) ∧
      (∫ J, ‖actualObservation (commonRowCLM c x e v) J‖ ^ r ∂coefficientKernel A w) ≤
        (2 : ℝ) ^ r * ((r.factorial : ℝ) *
          Real.exp (Real.sqrt (secondCovariance c 1) + secondCovariance c 1 / 2) +
          ((profileBound c * M / δ) * |overlap x y| ^ (d - 2)) ^ r) := by
  dsimp only
  intro r
  have hC := conditional_common_row_norm_moments hN hmN c hc hb x hx e he htanx v hv hvtan hve _ hA r
  have hm := common_row_pair_mixed_lift_norm hN c hc hd hdeg x y v hy hv hvtan e he
    htanx htany f g hg hr hδ hM hinv w hw
  exact coefficientKernel_norm_moment_of_centered_moment _ (commonRowCLM c x e v) w r hC.1 hC.2 hm

theorem actual_common_row_value_norm_moments {N P m k d : ℕ}
    (hN : 0 < N) (hmN : m ≤ N) (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (hb : 0 < secondCovariance c 1) (hd : 3 ≤ d)
    (hdeg : ∀ p, c p ≠ 0 → d ≤ p.val.val)
    (x y v : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) (hy : ‖y‖ ^ 2 = (N : ℝ))
    (hv : ‖v‖ = 1) (hvtan : inner ℝ v x = 0)
    (e : Fin m → Vector N) (he : Orthonormal ℝ e)
    (htanx : ∀ i, inner ℝ (e i) x = 0) (htany : ∀ i, inner ℝ (e i) y = 0)
    (hve : ∀ i, inner ℝ (e i) v = 0)
    (f g : Fin k → Vector N) (hg : Orthonormal ℝ g) (hr : |overlap x y| ≤ 1)
    {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hA : Surjective (pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)))
    (hinv : ‖(gram (pairHilbert (singleValueObservation c x f) (singleValueObservation c y g))).inverse‖ ≤ 1 / δ)
    (w : WithLp 2 (ValueObservationSpace k × ValueObservationSpace k))
    (hw : ‖w‖ ≤ M * Real.sqrt (N : ℝ)) :
    let A := pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)
    ∀ r : ℕ,
      Integrable (fun J : Disorder N P => ‖actualObservation (commonRowCLM c x e v) J‖ ^ r)
        (coefficientKernel A w) ∧
      (∫ J, ‖actualObservation (commonRowCLM c x e v) J‖ ^ r ∂coefficientKernel A w) ≤
        (2 : ℝ) ^ r * ((r.factorial : ℝ) *
          Real.exp (Real.sqrt (secondCovariance c 1) + secondCovariance c 1 / 2) +
          ((profileBound c * M / δ) * |overlap x y| ^ (d - 2)) ^ r) := by
  dsimp only
  intro r
  have hC := conditional_common_row_norm_moments hN hmN c hc hb x hx e he htanx v hv hvtan hve _ hA r
  have hm := common_row_pair_value_lift_norm hN c hc hd hdeg x y v hy hv hvtan e he
    htanx htany f g hg hr hδ hM hinv w hw
  exact coefficientKernel_norm_moment_of_centered_moment _ (commonRowCLM c x e v) w r hC.1 hC.2 hm

end
end SlowEquilibration.SphericalCommonHessianRegression

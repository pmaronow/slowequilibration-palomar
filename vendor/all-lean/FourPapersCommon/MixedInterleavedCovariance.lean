module
public import FourPapersCommon.MixedSecondInterpolationMismatchAlgebra
public import Targets.Section5InterleavedOffDiagonalBound

@[expose] public section

/-! The genuine disorder Hessian trace under all three actual field modes:
independent, shared, and opposite. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set SpinGlass SpinGlass.Targets
open scoped BigOperators
namespace FourPapersCommon
variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

theorem mixedConstrainedSecond_mixed_trace (hn : 0 < n) (ξ : AdmissibleEvenMixture)
    (sk : MixedDisorder (Ω := Ω) n ξ) (U : EnergySpace n) (u : ℝ)
    [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i) (j : ℕ) (x y : Fin n → ℝ) :
    (∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
      mixedConstrainedSecond mode m v j U (sk.hU.w i) (sk.hU.w i) u x y) =
      n * (2 * (ξ.value 1 + ξ.value u) -
        mixedReplicaMoment mode m v 0 j U u (fun p q => mixedPairCovariance ξ p.1 q.1) x y +
        ∑ l : Fin j, m l * (
          mixedReplicaMoment mode m v l (j - l) U u (fun p q => mixedPairCovariance ξ p.1 q.1) x y -
          mixedReplicaMoment mode m v (l + 1) (j - (l + 1)) U u
            (fun p q => mixedPairCovariance ξ p.1 q.1) x y)) := by
  simp only [mixedConstrainedSecond,
    mixedConstrainedCascadeDD_disorder_eq_replica U _ _ u mode m v hm hv j x y,
    mixedReplicaHessianExpression]
  rw [sum_weighted_covariance, sum_weighted_diagonal, mixedReplicaBilinear_contraction]
  simp_rw [mixedReplicaBilinear_contraction, mixedPairCovariance_spectral_sum ξ sk,
    mixedPairCovariance_self hn ξ, mixedReplicaMoment_const_mul]
  rw [← Finset.sum_mul, sum_mixedConstrainedGibbs U u mode m v hm hv j x y, one_mul]
  simp_rw [← mul_sub (n : ℝ), mul_left_comm (m _) (n : ℝ)]
  rw [← Finset.mul_sum]
  ring

theorem integrable_mixedConstrainedSecond_mixed_trace
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (sk : MixedDisorder (Ω := Ω) n ξ)
    {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (m v : ℕ → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (j : ℕ) (x y : Fin n → ℝ) :
    Integrable (fun ω => ∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
      mixedConstrainedSecond mode m v j (Z ω) (sk.hU.w i) (sk.hU.w i) u x y) := by
  simp_rw [mixedConstrainedSecond_mixed_trace hn ξ sk _ u mode m v hm hv j x y]
  apply Integrable.const_mul
  apply Integrable.add
  · exact (integrable_const _).sub
      (integrable_mixedReplicaMoment hZ u mode m v hm hv 0 j _ x y)
  · exact integrable_finsetSum _ fun l _ => ((integrable_mixedReplicaMoment hZ u mode m v hm hv
      l (j - l) _ x y).sub (integrable_mixedReplicaMoment hZ u mode m v hm hv
        (l + 1) (j - (l + 1)) _ x y)).const_mul (m l)

end FourPapersCommon

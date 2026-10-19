module
public import FourPapersCommon.MixedSecondInterpolationCovariance
public import Targets.Section5ReplicaDerivative

@[expose] public section

/-! Actual mixed disorder and independent/shared heat contractions under one
normalized split-replica law. All covariance entries refer to physical overlaps. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter Topology Set SpinGlass SpinGlass.Targets
open scoped BigOperators
namespace FourPapersCommon
universe u
variable {n : ℕ} {Ω : Type u} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

/-- Explicit overlap form of the normalized trace-plus-heat derivative.
The supplied `a` is the actual variance velocity, not a new hypothesis on the
derivative. The split index is measured from the innermost level. -/
noncomputable def mixedAveragedReplicaPressureDerivative (Z : Ω → EnergySpace n)
    (ξ : AdmissibleEvenMixture) (u t : ℝ) (m v a : ℕ → ℝ) (d J : ℕ) (x y : Fin n → ℝ) : ℝ :=
  t / 2 * (2 * (ξ.value 1 + ξ.value u) -
    averagedConstrainedReplicaMoment Z m v d 0 J u (fun p q => mixedPairCovariance ξ p.1 q.1) x y +
    ∑ l : Fin J, m l *
      (averagedConstrainedReplicaMoment Z m v d l (J - l) u
        (fun p q => mixedPairCovariance ξ p.1 q.1) x y -
      averagedConstrainedReplicaMoment Z m v d (l + 1) (J - (l + 1)) u
        (fun p q => mixedPairCovariance ξ p.1 q.1) x y)) +
  ∑ l : Fin J, a l / 2 * averagedConstrainedReplicaHeatExpression Z m v d l (J - l) u
    (if l < d then 2 else 2 * (1 + u))
    (fun p q => pairFieldCovariance 1 1 (if l < d then 0 else 1) p.1 q.1) x y

/-- Site normalization cancels exactly N and N/2 in the checked contractions. -/
theorem normalized_mixed_trace_heat_eq_replica
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (t : ℝ) (sk : MixedDisorder (Ω := Ω) n ξ)
    {Z : Ω → EnergySpace n} (hZ : Measurable Z)
    (u : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (m v a : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (hv : ∀ i, 0 ≤ v i)
    (d J : ℕ) (ha : ∀ l < J, ¬0 < v l → a l = 0) (x y : Fin n → ℝ) :
    (1 / (n : ℝ)) * (t / 2 * (∫ ω, ∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
      constrainedPairFieldCascadeSecond m v d J (Z ω) (sk.hU.w i) (sk.hU.w i) u x y) +
      ∑ l : Fin J, a l * (if 0 < v l then
        ∫ ω, constrainedLevelVarianceD (Z ω) u m v d l (J - (l + 1)) (v l) x y else 0)) =
      mixedAveragedReplicaPressureDerivative Z ξ u t m v a d J x y := by
  have hN : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have he (l : Fin J) : a l * (if 0 < v l then
      ∫ ω, constrainedLevelVarianceD (Z ω) u m v d l (J - (l + 1)) (v l) x y else 0) =
      (n : ℝ) * (a l / 2 * averagedConstrainedReplicaHeatExpression Z m v d l (J - l) u
        (if l < d then 2 else 2 * (1 + u))
        (fun p q => pairFieldCovariance 1 1 (if l < d then 0 else 1) p.1 q.1) x y) := by
    by_cases hp : 0 < v l
    · rw [if_pos hp]
      have hi : J - (l + 1) + 1 = J - l := by omega
      by_cases hl : (l : ℕ) < d
      · rw [integral_constrainedLevelVarianceD_independent_overlap hn hZ u m v hm hv d l
          (J - (l + 1)) hl x y, hi, if_pos hl, if_pos hl]
        ring
      · rw [integral_constrainedLevelVarianceD_shared_overlap hn hZ u m v hm hv d l
          (J - (l + 1)) hl x y, hi, if_neg hl, if_neg hl]
        ring
    · simp only [ha l l.isLt hp, zero_mul, zero_div, mul_zero]
  rw [integral_constrainedPairFieldCascadeSecond_mixed_trace hn ξ sk hZ u m v hm hv d J x y]
  simp_rw [he]
  rw [← Finset.mul_sum]
  unfold mixedAveragedReplicaPressureDerivative
  field_simp


end FourPapersCommon

module
public import FourPapersCommon.MixedSecondInterpolationMismatchTelescope

@[expose] public section

/-! Genuine normalized replica correction bound with independent physical
constraint and trial endpoint. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set SpinGlass SpinGlass.Targets
open scoped BigOperators
namespace FourPapersCommon
universe u
variable {n : ℕ} {Ω : Type u} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Exact covariance identity for the actual averaged pressure derivative,
with the original independent/shared cutoff and all physical coefficients. -/
theorem mixedAveragedReplicaPressureDerivative_eq_covariance_mismatch
    (Z : Ω → EnergySpace n) (ξ : AdmissibleEvenMixture) (u v t : ℝ) (m ρ V : ℕ → ℝ) (τ κ : ℕ)
    (hm0 : m 0 = 0) (hmκ : m κ = 1)
    (hρ0 : ρ 0 = 0) (hρ1 : ρ (κ + 1) = 1) (hτ : τ ≤ κ + 1) (hu : ρ τ = v)
    (x y : Fin n → ℝ) :
    mixedAveragedReplicaPressureDerivative Z ξ u t (fun j => m (κ - j)) V
      (fun j => -(t * (ξ.first (ρ (κ - j + 1)) - ξ.first (ρ (κ - j))))) (κ + 1 - τ) (κ + 1) x y =
      mixedPairCovarianceExpressionMismatch ξ t u v m ρ (fun p => ρ (min p τ)) κ
        (fun p => averagedConstrainedCascadeReplica Z u (fun j => m (κ - j)) V
          (κ + 1 - τ) (κ - p) (κ + 1 - (κ - p)) x y) + t*ξ.tangentRemainder u v := by
  let μ := fun i => averagedConstrainedCascadeReplica Z u (fun j => m (κ - j)) V
    (κ + 1 - τ) i (κ + 1 - i) x y
  let A := fun i => ∑ p, ∑ q, μ i p q * mixedPairCovariance ξ p.1 q.1
  let B := fun i l => ∑ p, ∑ q, μ i p q *
    pairFieldCovariance 1 1 (if κ - l < τ then 1 else 0) p.1 q.1
  let H := fun l =>
    ((if κ - l < τ then 2 * (1 + u) else 2) - B 0 l +
      ∑ i : Fin l, m (κ - i) * (B i l - B (i + 1) l)) + m (κ - l) * B l l
  have hc (l : Fin (κ + 1)) :
      (if (l : ℕ) < κ + 1 - τ then (0 : ℝ) else 1) =
        (if κ - l < τ then 1 else 0) := by
    have hl := l.isLt
    split_ifs <;> first | rfl | omega
  have hd (l : Fin (κ + 1)) :
      (if (l : ℕ) < κ + 1 - τ then (2 : ℝ) else 2 * (1 + u)) =
        (if κ - l < τ then 2 * (1 + u) else 2) := by
    have hl := l.isLt
    split_ifs <;> first | rfl | omega
  have hh (l : Fin (κ + 1)) :
      averagedConstrainedReplicaHeatExpression Z (fun j => m (κ - j)) V (κ + 1 - τ)
        l (κ + 1 - l) u (if (l : ℕ) < κ + 1 - τ then 2 else 2 * (1 + u))
        (fun p q => pairFieldCovariance 1 1
          (if (l : ℕ) < κ + 1 - τ then 0 else 1) p.1 q.1) x y = H l := by
    have hi : (l : ℕ) + (κ + 1 - l) = κ + 1 := by omega
    simp only [averagedConstrainedReplicaHeatExpression, hi, hc, hd,
      averagedConstrainedReplicaMoment, H, B, μ, Nat.sub_zero]
  have hsum := mixedPairCovarianceExpressionMismatch_eq_trace_sub_heat ξ t u v m ρ τ κ
    hm0 hmκ hρ0 hρ1 hτ hu μ
  change t / 2 *
    ((2 * (ξ.value 1 + ξ.value u) - A 0 + ∑ i : Fin (κ + 1),
        m (κ - i) * (A i - A (i + 1))) -
      ∑ l : Fin (κ + 1), (ξ.first (ρ (κ - l + 1)) - ξ.first (ρ (κ - l))) * H l) = _ at hsum
  rw [← hsum]
  unfold mixedAveragedReplicaPressureDerivative
  simp_rw [hh]
  change t / 2 *
    (2 * (ξ.value 1 + ξ.value u) - A 0 + ∑ i : Fin (κ + 1),
      m (κ - i) * (A i - A (i + 1))) +
    (∑ l : Fin (κ + 1), -(t * (ξ.first (ρ (κ - l + 1)) - ξ.first (ρ (κ - l)))) / 2 * H l) = _
  have he (l : Fin (κ + 1)) :
      -(t * (ξ.first (ρ (κ - l + 1)) - ξ.first (ρ (κ - l)))) / 2 * H l =
        -(t / 2) * ((ξ.first (ρ (κ - l + 1)) - ξ.first (ρ (κ - l))) * H l) := by ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  ring

/-- The actual covariance derivative is bounded by the deterministic
correction. Positivity and normalization come from the actual averaged split
weights. Repeated masses and zero variances are allowed. -/
theorem mixedAveragedReplicaPressureDerivative_le_mismatch
    (hn : 0 < n)
    {Z : Ω → EnergySpace n} (hZ : Measurable Z) (ξ : AdmissibleEvenMixture) (u v : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (m ρ V : ℕ → ℝ) (τ κ : ℕ)
    (hm0 : m 0 = 0) (hmκ : m κ = 1)
    (hm : ∀ i, 0 ≤ m (κ - i)) (hv : ∀ i, 0 ≤ V i)
    (hmono : ∀ p < κ, m p ≤ m (p + 1))
    (hρ0 : ρ 0 = 0) (hρ1 : ρ (κ + 1) = 1) (hτ : τ ≤ κ + 1) (hu : ρ τ = v)
    (hρ : ∀ p≤κ+1, ρ p ∈ Set.Icc (-1 : ℝ) 1)
    [Nonempty (AT.ConstrainedPair n u)] (x y : Fin n → ℝ) :
    mixedAveragedReplicaPressureDerivative Z ξ u t (fun j => m (κ - j)) V
      (fun j => -(t * (ξ.first (ρ (κ - j + 1)) - ξ.first (ρ (κ - j))))) (κ + 1 - τ) (κ + 1) x y ≤
      -t * mixedPairCascadeCorrection ξ m ρ (fun p => ρ (min p τ)) κ + t*ξ.tangentRemainder u v := by
  rw [mixedAveragedReplicaPressureDerivative_eq_covariance_mismatch Z ξ u v t m ρ V τ κ
    hm0 hmκ hρ0 hρ1 hτ hu x y]
  apply add_le_add _ le_rfl
  apply mixedPairCovarianceExpressionMismatch_le hn ξ u v ht m ρ (fun p => ρ (min p τ)) κ hmκ hmono
    hρ0 (by simpa using hρ0) hρ1 (by simpa only [min_eq_right hτ] using hu)
  · intro p _ a b
    exact averagedConstrainedCascadeReplica_nonneg Z u (fun j => m (κ - j)) V hm hv
      (κ + 1 - τ) (κ - p) (κ + 1 - (κ - p)) x y a b
  · intro p _
    exact sum_averagedConstrainedCascadeReplica hZ u (fun j => m (κ - j)) V hm hv
      (κ + 1 - τ) (κ - p) (κ + 1 - (κ - p)) x y

  · intro p hp
    exact hρ (p+1) (by omega)
  · intro p hp
    exact hρ (min (p+1) τ) (by omega)

end FourPapersCommon

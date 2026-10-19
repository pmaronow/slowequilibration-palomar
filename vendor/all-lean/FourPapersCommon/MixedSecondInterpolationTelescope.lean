module
public import FourPapersCommon.MixedSecondInterpolationAlgebra
public import FourPapersCommon.MixedSecondInterpolationTrace

@[expose] public section

/-! The covariance telescope of the genuine mixed second interpolation.
The diagonal field contribution retains the physical constrained overlap. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set SpinGlass SpinGlass.Targets
open scoped BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 800000

 theorem sum_mixedPairField_heat_diagonal (ξ : AdmissibleEvenMixture) (u : ℝ)
    (ρ : ℕ → ℝ) (τ κ : ℕ) (hρ0 : ρ 0=0) (hρ1 : ρ (κ+1)=1)
    (hτ : τ≤κ+1) (hu : ρ τ=u) :
    (∑ l ∈ Finset.range (κ+1), (ξ.first (ρ (κ-l+1))-ξ.first (ρ (κ-l))) *
      (if κ-l<τ then 2*(1+u) else 2))=2*(ξ.first 1+u*ξ.first u) := by
  let F := fun p => 2*(ξ.first (ρ p)+u*ξ.first (ρ (min p τ)))
  have he (p : ℕ) : (ξ.first (ρ (p+1))-ξ.first (ρ p))*
      (if p<τ then 2*(1+u) else 2)=F (p+1)-F p := by
    by_cases hp : p<τ
    · simp only [F, if_pos hp, min_eq_left (by omega : p+1≤τ), min_eq_left (by omega : p≤τ)]
      ring
    · simp only [F, if_neg hp, min_eq_right (by omega : τ≤p+1), min_eq_right (by omega : τ≤p)]
      ring
  simp_rw [he]
  have hrev := Finset.sum_range_reflect (fun p => F (p+1)-F p) (κ+1)
  simp only [Nat.add_sub_cancel] at hrev
  rw [hrev, Finset.sum_range_sub]
  simp only [F, hρ0, hρ1, min_eq_right hτ, Nat.zero_min, hu, ξ.first_zero]
  ring

theorem mixedPairCovarianceExpression_eq_trace_sub_heat {n : ℕ}
    (ξ : AdmissibleEvenMixture) (t u : ℝ) (m ρ : ℕ → ℝ) (τ κ : ℕ)
    (hm0 : m 0 = 0) (hmκ : m κ = 1)
    (hρ0 : ρ 0 = 0) (hρ1 : ρ (κ + 1) = 1) (hτ : τ ≤ κ + 1) (hu : ρ τ = u)
    (μ : ℕ → AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) :
    let A := fun i => ∑ p, ∑ q, μ i p q * mixedPairCovariance ξ p.1 q.1
    let B := fun i l => ∑ p, ∑ q, μ i p q *
      pairFieldCovariance 1 1 (if κ - l < τ then 1 else 0) p.1 q.1
    t / 2 *
      ((2 * (ξ.value 1 + ξ.value u) - A 0 + ∑ i : Fin (κ + 1),
          m (κ - i) * (A i - A (i + 1))) -
        ∑ l : Fin (κ + 1), (ξ.first (ρ (κ - l + 1)) - ξ.first (ρ (κ - l))) *
          (((if κ - l < τ then 2 * (1 + u) else 2) - B 0 l +
              ∑ i : Fin l, m (κ - i) * (B i l - B (i + 1) l)) +
            m (κ - l) * B l l)) =
      mixedPairCovarianceExpression ξ t u m ρ (fun p => ρ (min p τ)) κ
        (fun p => μ (κ - p)) := by
  dsimp only
  let A := fun i => ∑ p, ∑ q, μ i p q * mixedPairCovariance ξ p.1 q.1
  let B := fun i l => ∑ p, ∑ q, μ i p q *
    pairFieldCovariance 1 1 (if κ - l < τ then 1 else 0) p.1 q.1
  let a := fun l => (ξ.first (ρ (κ - l + 1)) - ξ.first (ρ (κ - l)))
  let D := fun l => if κ - l < τ then 2 * (1 + u) else 2
  change t / 2 *
    ((2 * (ξ.value 1 + ξ.value u) - A 0 + ∑ i : Fin (κ + 1),
        m (κ - i) * (A i - A (i + 1))) -
      ∑ l : Fin (κ + 1), a l *
        ((D l - B 0 l + ∑ i : Fin l, m (κ - i) * (B i l - B (i + 1) l)) +
          m (κ - l) * B l l)) = _
  rw [replicaTrace_sub_weighted_heat_fin (fun i => m (κ - i)) A a D B
    (2 * (ξ.value 1 + ξ.value u)) κ (by simpa using hmκ) (by simpa using hm0)]
  have hd : (∑ l : Fin (κ + 1), a l * D l) = 2 * (ξ.first 1 + u * ξ.first u) := by
    rw [Fin.sum_univ_eq_sum_range (fun l => a l * D l) (κ + 1)]
    exact sum_mixedPairField_heat_diagonal ξ u ρ τ κ hρ0 hρ1 hτ hu
  rw [hd]
  have hb (i : ℕ) : replicaHeatTail (fun i l => a l * B i l) (κ + 1) i =
      ∑ p, ∑ q, μ i p q *
        pairFieldCovariance 1 (ξ.first (ρ (κ + 1 - i))) (ξ.first (ρ (min (κ + 1 - i) τ))) p.1 q.1 :=
    by
      simpa only [one_pow, one_mul] using replicaHeatTail_pairFieldCovariance 1
        (fun p => ξ.first (ρ p)) (by rw [hρ0, ξ.first_zero]) τ κ i μ
  simp_rw [hb]
  let X := fun i => A i - ∑ p, ∑ q, μ i p q *
    pairFieldCovariance 1 (ξ.first (ρ (κ + 1 - i))) (ξ.first (ρ (min (κ + 1 - i) τ))) p.1 q.1
  change t / 2 * (2 * (ξ.value 1 + ξ.value u) - 2 * (ξ.first 1 + u * ξ.first u) +
    ∑ i : Fin κ, (m (κ - (i + 1)) - m (κ - i)) * X (i + 1)) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (m (κ - (i + 1)) - m (κ - i)) * X (i + 1)) κ,
    replicaMassGap_reverse]
  have hx (p : ℕ) (hp : p < κ) : X (κ - p) =
      ∑ a, ∑ b, μ (κ - p) a b *
        (mixedPairCovariance ξ a.1 b.1 -
          pairFieldCovariance 1 (ξ.first (ρ (p + 1))) (ξ.first (ρ (min (p + 1) τ))) a.1 b.1) := by
    have hi : κ + 1 - (κ - p) = p + 1 := by omega
    simp only [X, A, hi, mul_sub, Finset.sum_sub_distrib]
  simp_rw [mixedPairCovarianceExpression]
  have hs := Finset.sum_congr rfl (fun p hp =>
    congrArg (fun z => (m p - m (p + 1)) * z) (hx p (Finset.mem_range.mp hp)))
  rw [hs]
  simp only [AdmissibleEvenMixture.correction]
  ring

end FourPapersCommon

module
public import FourPapersCommon.MixedInterleavedCovariance

@[expose] public section

/-! The arbitrary-mode mixed trace telescope. Trial covariance increments
are exact derivatives of the physical mixed covariance. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set SpinGlass SpinGlass.Targets
open scoped BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 800000

theorem mixedPairCovarianceExpression_eq_trace_sub_increment_heat_mismatch {n : ℕ}
    (ξ : AdmissibleEvenMixture) (t u v : ℝ) (m ρ c : ℕ → ℝ) (κ : ℕ)
    (hm0 : m 0 = 0) (hmκ : m κ = 1)
    (hρ0 : ρ 0 = 0) (hc0 : c 0 = 0) (hρ1 : ρ (κ + 1) = 1)
    (hc1 : c (κ + 1) = v)
    (μ : ℕ → AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) :
    let A := fun i => ∑ p, ∑ q, μ i p q * mixedPairCovariance ξ p.1 q.1
    let B := fun i l => ∑ p, ∑ q, μ i p q *
      pairFieldCovariance 1 (ξ.first (ρ (κ - l + 1)) - ξ.first (ρ (κ - l)))
        (ξ.first (c (κ - l + 1)) - ξ.first (c (κ - l))) p.1 q.1
    let D := fun l => 2 *
      ((ξ.first (ρ (κ - l + 1)) - ξ.first (ρ (κ - l))) + u * (ξ.first (c (κ - l + 1)) - ξ.first (c (κ - l))))
    t / 2 *
      ((2 * (ξ.value 1 + ξ.value u) - A 0 + ∑ i : Fin (κ + 1),
          m (κ - i) * (A i - A (i + 1))) -
        ∑ l : Fin (κ + 1),
          ((D l - B 0 l + ∑ i : Fin l, m (κ - i) * (B i l - B (i + 1) l)) +
            m (κ - l) * B l l)) =
      mixedPairCovarianceExpressionMismatch ξ t u v m ρ c κ (fun p => μ (κ - p)) +
        t * ξ.tangentRemainder u v := by
  dsimp only
  let A := fun i => ∑ p, ∑ q, μ i p q * mixedPairCovariance ξ p.1 q.1
  let B := fun i l => ∑ p, ∑ q, μ i p q *
    pairFieldCovariance 1 (ξ.first (ρ (κ - l + 1)) - ξ.first (ρ (κ - l)))
      (ξ.first (c (κ - l + 1)) - ξ.first (c (κ - l))) p.1 q.1
  let D := fun l => 2 *
    ((ξ.first (ρ (κ - l + 1)) - ξ.first (ρ (κ - l))) + u * (ξ.first (c (κ - l + 1)) - ξ.first (c (κ - l))))
  change t / 2 *
    ((2 * (ξ.value 1 + ξ.value u) - A 0 + ∑ i : Fin (κ + 1),
      m (κ - i) * (A i - A (i + 1))) -
      ∑ l : Fin (κ + 1),
        ((D l - B 0 l + ∑ i : Fin l, m (κ - i) * (B i l - B (i + 1) l)) +
          m (κ - l) * B l l)) = _
  have H := replicaTrace_sub_weighted_heat_fin (fun i => m (κ - i)) A (fun _ => 1) D B
    (2 * (ξ.value 1 + ξ.value u)) κ (by simpa using hmκ) (by simpa using hm0)
  simp only [one_mul] at H
  rw [H]
  have hd : (∑ l : Fin (κ + 1), D l) = 2 * (ξ.first 1 + u * ξ.first v) := by
    let F := fun p=>2*(ξ.first (ρ p)+u*ξ.first (c p))
    have he (l : ℕ) : D l=F (κ-l+1)-F (κ-l) := by dsimp [D,F]; ring
    simp_rw [he]
    rw [Fin.sum_univ_eq_sum_range (fun l=>F (κ-l+1)-F (κ-l)) (κ+1)]
    have hrev:=Finset.sum_range_reflect (fun p=>F (p+1)-F p) (κ+1)
    simp only [Nat.add_sub_cancel] at hrev
    rw [hrev,Finset.sum_range_sub]
    simp only [F,hρ0,hc0,hρ1,hc1,ξ.first_zero,mul_zero,add_zero,sub_zero,mul_zero]
  rw [hd]
  have hb (i : ℕ) : replicaHeatTail B (κ + 1) i =
      ∑ p, ∑ q, μ i p q *
        pairFieldCovariance 1 (ξ.first (ρ (κ + 1 - i))) (ξ.first (c (κ + 1 - i))) p.1 q.1 :=
    by
      exact replicaHeatTail_pairField_increments 1 (fun p=>ξ.first (ρ p))
        (fun p=>ξ.first (c p)) (by rw [hρ0,ξ.first_zero]) (by rw [hc0,ξ.first_zero]) κ i μ
  simp_rw [hb]
  let X := fun i => A i - ∑ p, ∑ q, μ i p q *
    pairFieldCovariance 1 (ξ.first (ρ (κ + 1 - i))) (ξ.first (c (κ + 1 - i))) p.1 q.1
  change t / 2 * (2 * (ξ.value 1 + ξ.value u) - 2 * (ξ.first 1 + u * ξ.first v) +
    ∑ i : Fin κ, (m (κ - (i + 1)) - m (κ - i)) * X (i + 1)) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (m (κ - (i + 1)) - m (κ - i)) * X (i + 1)) κ,
    replicaMassGap_reverse]
  have hx (p : ℕ) (hp : p < κ) : X (κ - p) =
      ∑ a, ∑ b, μ (κ - p) a b *
        (mixedPairCovariance ξ a.1 b.1 -
          pairFieldCovariance 1 (ξ.first (ρ (p + 1))) (ξ.first (c (p + 1))) a.1 b.1) := by
    have hi : κ + 1 - (κ - p) = p + 1 := by omega
    simp only [X, A, hi, mul_sub, Finset.sum_sub_distrib]
  simp_rw [mixedPairCovarianceExpressionMismatch]
  have hs := Finset.sum_congr rfl (fun p hp =>
    congrArg (fun z => (m p - m (p + 1)) * z)
      (hx p (Finset.mem_range.mp hp)))
  rw [hs]
  simp only [AdmissibleEvenMixture.correction,AdmissibleEvenMixture.tangentRemainder]
  ring

end FourPapersCommon

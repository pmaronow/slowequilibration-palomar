module
public import FourPapersCommon.MixedInterleavedTelescope

@[expose] public section

/-! Exact mixed covariance identification for the real Gaussian field modes.
The physical constraint and trial endpoint remain independent. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set SpinGlass SpinGlass.Targets
open scoped BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 800000

theorem mixedConstrained_mixed_trace_sub_heat_eq_covariance_mismatch
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {n : ℕ}
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (sk : MixedDisorder (Ω := Ω) n ξ)
    (U : EnergySpace n) (t u v : ℝ) [Nonempty (AT.ConstrainedPair n u)]
    (mode : ℕ → Section5GaussianMode) (M ρ c w : ℕ → ℝ) (κ : ℕ)
    (hm : ∀ i, 0 ≤ M (κ - i)) (hv : ∀ i, 0 ≤ w i)
    (hm0 : M 0 = 0) (hmκ : M κ = 1)
    (hρ0 : ρ 0 = 0) (hc0 : c 0 = 0) (hρ1 : ρ (κ + 1) = 1) (hc1 : c (κ + 1) = v)
    (hinc : ∀ l < κ + 1, ξ.first (c (κ - l + 1)) - ξ.first (c (κ - l)) =
      (ξ.first (ρ (κ - l + 1)) - ξ.first (ρ (κ - l))) * (mode l).correlation)
    (x y : Fin n → ℝ) :
    (1 / (n : ℝ)) *
      (t / 2 * (∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
          mixedConstrainedSecond mode (fun i => M (κ - i)) w (κ + 1)
            U (sk.hU.w i) (sk.hU.w i) u x y) -
        t * ∑ l : Fin (κ + 1), (ξ.first (ρ (κ - l + 1)) - ξ.first (ρ (κ - l))) *
          mixedLevelVarianceD U u mode (fun i => M (κ - i)) w l
            (κ + 1 - (l + 1)) (w l) x y) =
      mixedPairCovarianceExpressionMismatch ξ t u v M ρ c κ
        (fun p => mixedConstrainedReplica mode (fun i => M (κ - i)) w
          (κ - p) (κ + 1 - (κ - p)) U u x y) + t * ξ.tangentRemainder u v := by
  let m := fun i => M (κ - i)
  let μ := fun i => mixedConstrainedReplica mode m w i (κ + 1 - i) U u x y
  let A := fun i => mixedReplicaMoment mode m w i (κ + 1 - i) U u
    (fun p q => mixedPairCovariance ξ p.1 q.1) x y
  let B := fun i l => mixedReplicaMoment mode m w i (κ + 1 - i) U u
    (fun p q => pairFieldCovariance 1 (ξ.first (ρ (κ - l + 1)) - ξ.first (ρ (κ - l)))
      (ξ.first (c (κ - l + 1)) - ξ.first (c (κ - l))) p.1 q.1) x y
  let D := fun l => 2 * ((ξ.first (ρ (κ - l + 1)) - ξ.first (ρ (κ - l))) +
    u * (ξ.first (c (κ - l + 1)) - ξ.first (c (κ - l))))
  have hheat (l : Fin (κ + 1)) :
      (ξ.first (ρ (κ - l + 1)) - ξ.first (ρ (κ - l))) *
        mixedLevelVarianceD U u mode m w l (κ + 1 - (l + 1)) (w l) x y =
      (n : ℝ) / 2 * ((D l - B 0 l + ∑ i : Fin l, m i * (B i l - B (i + 1) l)) +
        m l * B l l) := by
    rw [mixedLevelVarianceD_overlap hn U u mode m w hm hv]
    have hsum : (l : ℕ) + (κ + 1 - (l + 1) + 1) = κ + 1 := by omega
    have hrest : κ + 1 - (l + 1) + 1 = κ + 1 - l := by omega
    have hK (p q : AT.ConstrainedPair n u) :
        pairFieldCovariance 1 (ξ.first (ρ (κ - l + 1)) - ξ.first (ρ (κ - l)))
          (ξ.first (c (κ - l + 1)) - ξ.first (c (κ - l))) p.1 q.1 =
        ((ξ.first (ρ (κ - l + 1)) - ξ.first (ρ (κ - l)))) *
          pairFieldCovariance 1 1 (mode l).correlation p.1 q.1 := by
      rw [hinc l l.isLt]
      simp [pairFieldCovariance, pairTrialMatrix, Fin.sum_univ_two]
      ring
    have hD : D l = ((ξ.first (ρ (κ - l + 1)) - ξ.first (ρ (κ - l)))) *
        (2 * (1 + (mode l).correlation * u)) := by
      dsimp [D]
      rw [hinc l l.isLt]
      ring
    have HH := mixedReplicaHeatExpression_const_mul mode m w l
      (κ + 1 - (l + 1) + 1) U u (2 * (1 + (mode l).correlation * u))
      ((ξ.first (ρ (κ - l + 1)) - ξ.first (ρ (κ - l))))
      (fun p q => pairFieldCovariance 1 1 (mode l).correlation p.1 q.1) x y
    rw [← hD] at HH
    simp_rw [← hK] at HH
    rw [mixedReplicaHeatExpression, hsum, hrest] at HH
    change (D l - B 0 l + ∑ i : Fin l, m i * (B i l - B (i + 1) l)) + m l * B l l = _ at HH
    rw [HH, hrest]
    ring
  rw [mixedConstrainedSecond_mixed_trace hn ξ sk U u mode m w hm hv]
  change (1 / (n : ℝ)) *
    (t / 2 * (n * (2 * (ξ.value 1 + ξ.value u) - A 0 +
      ∑ i : Fin (κ + 1), m i * (A i - A (i + 1)))) -
      t * ∑ l : Fin (κ + 1), (ξ.first (ρ (κ - l + 1)) - ξ.first (ρ (κ - l))) *
        mixedLevelVarianceD U u mode m w l (κ + 1 - (l + 1)) (w l) x y) = _
  simp_rw [hheat]
  rw [← Finset.mul_sum]
  have hnR : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have H := mixedPairCovarianceExpression_eq_trace_sub_increment_heat_mismatch ξ t u v M ρ c κ
    hm0 hmκ hρ0 hc0 hρ1 hc1 μ
  change t / 2 * ((2 * (ξ.value 1 + ξ.value u) - A 0 +
    ∑ i : Fin (κ + 1), m i * (A i - A (i + 1))) -
      ∑ l : Fin (κ + 1), ((D l - B 0 l + ∑ i : Fin l, m i * (B i l - B (i + 1) l)) +
        m l * B l l)) = _ at H
  rw [← H]
  change (1 / (n : ℝ)) * (t / 2 * (n * _) - t * (n / 2 * _)) = _
  field_simp [hnR]

end FourPapersCommon

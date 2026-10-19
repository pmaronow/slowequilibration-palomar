module
public import FourPapersCommon.MixedSecondInterpolationIdentity

@[expose] public section

/-! Independent actual constraint and trial overlap. The exact cost of their
mismatch is the genuine convex tangent remainder, not a clock-overlap square. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set SpinGlass SpinGlass.Targets
open scoped BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 800000

 def mixedPairCovarianceExpressionMismatch {n : ℕ} (ξ : AdmissibleEvenMixture)
    (t u v : ℝ) (m ρ c : ℕ→ℝ) (κ : ℕ)
    (μ : ℕ→AT.ConstrainedPair n u→AT.ConstrainedPair n u→ℝ) : ℝ :=
  t/2*(-2*(ξ.correction 1+ξ.correction v)+∑l∈Finset.range κ,
    (m l-m (l+1))*∑p,∑q,μ l p q*(mixedPairCovariance ξ p.1 q.1-
      pairFieldCovariance 1 (ξ.first (ρ (l+1))) (ξ.first (c (l+1))) p.1 q.1))

theorem mixedPairCovarianceExpressionMismatch_eq {n : ℕ} (ξ : AdmissibleEvenMixture) (t u v : ℝ)
    (m ρ c : ℕ → ℝ) (κ : ℕ) (hm : m κ = 1)
    (hρ0 : ρ 0 = 0) (hc0 : c 0 = 0) (hρ1 : ρ (κ + 1) = 1) (hc1 : c (κ + 1) = v)
    (μ : ℕ → AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ)
    (hμ : ∀ l < κ, ∑ p, ∑ q, μ l p q = 1) :
    mixedPairCovarianceExpressionMismatch ξ t u v m ρ c κ μ =
      -t * mixedPairCascadeCorrection ξ m ρ c κ - mixedPairCovarianceRemainder ξ t u m ρ c κ μ := by
  classical
  have he (l : ℕ) (hl : l < κ) :
      (∑ p, ∑ q, μ l p q * (mixedPairCovariance ξ p.1 q.1 -
        pairFieldCovariance 1 (ξ.first (ρ (l + 1))) (ξ.first (c (l + 1))) p.1 q.1)) =
      (∑ p, ∑ q, μ l p q * mixedPairCovarianceDefect ξ (ρ (l + 1)) (c (l + 1)) p.1 q.1) -
        2 * mixedPairTrialEnergy ξ (ρ (l + 1)) (c (l + 1)) := by
    simp_rw [mixedPairCovariance_completion, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hμ l hl, one_mul]
    unfold mixedPairTrialEnergy
    ring
  unfold mixedPairCovarianceExpressionMismatch mixedPairCovarianceRemainder
  rw [mixedPairCascadeCorrection_telescope ξ m ρ c κ hm hρ0 hc0, hρ1, hc1]
  have hs := Finset.sum_congr rfl (fun l hl => congrArg (fun x => (m l - m (l + 1)) * x)
    (he l (Finset.mem_range.mp hl)))
  rw [hs]
  have hd (l : ℕ) : (m l - m (l + 1)) *
      ((∑ p, ∑ q, μ l p q * mixedPairCovarianceDefect ξ (ρ (l + 1)) (c (l + 1)) p.1 q.1) -
        2 * mixedPairTrialEnergy ξ (ρ (l + 1)) (c (l + 1))) =
      2 * ((m (l + 1) - m l) * mixedPairTrialEnergy ξ (ρ (l + 1)) (c (l + 1))) -
      (m (l + 1) - m l) * ∑ p, ∑ q,
        μ l p q * mixedPairCovarianceDefect ξ (ρ (l + 1)) (c (l + 1)) p.1 q.1 := by ring
  simp_rw [hd, Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold mixedPairTrialEnergy
  ring

theorem mixedPairCovarianceExpressionMismatch_le {n : ℕ} (hn : 0 < n) (ξ : AdmissibleEvenMixture) (u v : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (m ρ c : ℕ → ℝ) (κ : ℕ) (hm : m κ = 1) (hmono : ∀ l < κ, m l ≤ m (l + 1))
    (hρ0 : ρ 0 = 0) (hc0 : c 0 = 0) (hρ1 : ρ (κ + 1) = 1) (hc1 : c (κ + 1) = v)
    (μ : ℕ → AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ)
    (hμ0 : ∀ l < κ, ∀ p q, 0 ≤ μ l p q) (hμ1 : ∀ l < κ, ∑ p, ∑ q, μ l p q = 1)
    (hρ : ∀ l < κ, ρ (l + 1) ∈ Set.Icc (-1 : ℝ) 1)
    (hc : ∀ l < κ, c (l + 1) ∈ Set.Icc (-1 : ℝ) 1) :
    mixedPairCovarianceExpressionMismatch ξ t u v m ρ c κ μ ≤ -t * mixedPairCascadeCorrection ξ m ρ c κ := by
  rw [mixedPairCovarianceExpressionMismatch_eq ξ t u v m ρ c κ hm hρ0 hc0 hρ1 hc1 μ hμ1]
  exact sub_le_self _ (mixedPairCovarianceRemainder_nonneg hn ξ u ht m ρ c κ hmono μ hμ0 hρ hc)

end FourPapersCommon

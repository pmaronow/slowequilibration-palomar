module
public import FourPapersCommon.MixedSecondInterpolationCovariance
public import Targets.CoupledCovarianceTelescope

@[expose] public section

/-! Exact theta correction and nonnegative tangent remainder for the actual
mixed second interpolation. These finite identities preserve physical overlaps. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real SpinGlass SpinGlass.Targets
open scoped BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 800000

/-- Half the quadratic energy of the symmetric two-replica trial matrix. -/
noncomputable def mixedPairTrialEnergy (ξ : AdmissibleEvenMixture) (q c : ℝ) : ℝ := ξ.correction q + ξ.correction c

/-- The correction in Theorem 3.1, with forward level indices. -/
noncomputable def mixedPairCascadeCorrection (ξ : AdmissibleEvenMixture) (m ρ c : ℕ → ℝ) (κ : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (κ + 1), m p *
    (mixedPairTrialEnergy ξ (ρ (p + 1)) (c (p + 1)) - mixedPairTrialEnergy ξ (ρ p) (c p))

/-- Summation by parts is reused from Mathlib, with the zero initial energy. -/
theorem mixedPairCascadeCorrection_telescope (ξ : AdmissibleEvenMixture) (m ρ c : ℕ → ℝ) (κ : ℕ)
    (hm : m κ = 1) (hρ : ρ 0 = 0) (hc : c 0 = 0) :
    mixedPairCascadeCorrection ξ m ρ c κ = mixedPairTrialEnergy ξ (ρ (κ + 1)) (c (κ + 1)) -
      ∑ l ∈ Finset.range κ, (m (l + 1) - m l) * mixedPairTrialEnergy ξ (ρ (l + 1)) (c (l + 1)) := by
  have H := Finset.sum_range_by_parts m
    (fun p => mixedPairTrialEnergy ξ (ρ (p + 1)) (c (p + 1)) - mixedPairTrialEnergy ξ (ρ p) (c p)) (κ + 1)
  have hz : mixedPairTrialEnergy ξ (ρ 0) (c 0) = 0 := by simp [mixedPairTrialEnergy, AdmissibleEvenMixture.correction, hρ, hc, ξ.value_zero, ξ.first_zero]
  simp_rw [Finset.sum_range_sub (fun p => mixedPairTrialEnergy ξ (ρ p) (c p))] at H
  simp only [hz, sub_zero, Nat.add_sub_cancel, hm, smul_eq_mul, one_mul] at H
  exact H

/-- The explicit covariance expression obtained after the intended nested IBP.
Index l of mu represents the paper's measure mu_(l+1). -/
noncomputable def mixedPairCovarianceExpression {n : ℕ} (ξ : AdmissibleEvenMixture) (t u : ℝ)
    (m ρ c : ℕ → ℝ) (κ : ℕ)
    (μ : ℕ → AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) : ℝ :=
  t / 2 * (-2 * (ξ.correction 1 + ξ.correction u) + ∑ l ∈ Finset.range κ,
    (m l - m (l + 1)) * ∑ p, ∑ q, μ l p q *
      (mixedPairCovariance ξ p.1 q.1 - pairFieldCovariance 1 (ξ.first (ρ (l + 1))) (ξ.first (c (l + 1))) p.1 q.1))

/-- The algebraic square remainder; it is not yet a theorem about eta'. -/
noncomputable def mixedPairCovarianceRemainder {n : ℕ} (ξ : AdmissibleEvenMixture) (t u : ℝ)
    (m ρ c : ℕ → ℝ) (κ : ℕ)
    (μ : ℕ → AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ) : ℝ :=
  t / 2 * ∑ l ∈ Finset.range κ, (m (l + 1) - m l) * ∑ p, ∑ q,
    μ l p q * mixedPairCovarianceDefect ξ (ρ (l + 1)) (c (l + 1)) p.1 q.1

theorem mixedPairCovarianceRemainder_nonneg {n : ℕ} (hn : 0 < n) (ξ : AdmissibleEvenMixture) (u : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (m ρ c : ℕ → ℝ) (κ : ℕ) (hm : ∀ l < κ, m l ≤ m (l + 1))
    (μ : ℕ → AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ)
    (hμ : ∀ l < κ, ∀ p q, 0 ≤ μ l p q)
    (hρ : ∀ l < κ, ρ (l + 1) ∈ Set.Icc (-1 : ℝ) 1)
    (hc : ∀ l < κ, c (l + 1) ∈ Set.Icc (-1 : ℝ) 1) : 0 ≤ mixedPairCovarianceRemainder ξ t u m ρ c κ μ := by
  apply mul_nonneg (div_nonneg ht (by norm_num))
  apply Finset.sum_nonneg
  intro l hl
  have hl' := Finset.mem_range.mp hl
  apply mul_nonneg (sub_nonneg.mpr (hm l hl'))
  apply Finset.sum_nonneg
  intro p _
  apply Finset.sum_nonneg
  intro q _
  exact mul_nonneg (hμ l hl' p q) (mixedPairCovarianceDefect_nonneg hn ξ (hρ l hl') (hc l hl') _ _)

/-- Exact completion of the four overlap squares and the two telescoping sums.
All hypotheses concern explicit finite coefficients and weights, not eta'. -/
theorem mixedPairCovarianceExpression_eq {n : ℕ} (ξ : AdmissibleEvenMixture) (t u : ℝ)
    (m ρ c : ℕ → ℝ) (κ : ℕ) (hm : m κ = 1)
    (hρ0 : ρ 0 = 0) (hc0 : c 0 = 0) (hρ1 : ρ (κ + 1) = 1) (hc1 : c (κ + 1) = u)
    (μ : ℕ → AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ)
    (hμ : ∀ l < κ, ∑ p, ∑ q, μ l p q = 1) :
    mixedPairCovarianceExpression ξ t u m ρ c κ μ =
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
  unfold mixedPairCovarianceExpression mixedPairCovarianceRemainder
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

theorem mixedPairCovarianceExpression_le {n : ℕ} (hn : 0 < n) (ξ : AdmissibleEvenMixture) (u : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (m ρ c : ℕ → ℝ) (κ : ℕ) (hm : m κ = 1) (hmono : ∀ l < κ, m l ≤ m (l + 1))
    (hρ0 : ρ 0 = 0) (hc0 : c 0 = 0) (hρ1 : ρ (κ + 1) = 1) (hc1 : c (κ + 1) = u)
    (μ : ℕ → AT.ConstrainedPair n u → AT.ConstrainedPair n u → ℝ)
    (hμ0 : ∀ l < κ, ∀ p q, 0 ≤ μ l p q) (hμ1 : ∀ l < κ, ∑ p, ∑ q, μ l p q = 1)
    (hρ : ∀ l < κ, ρ (l + 1) ∈ Set.Icc (-1 : ℝ) 1)
    (hc : ∀ l < κ, c (l + 1) ∈ Set.Icc (-1 : ℝ) 1) :
    mixedPairCovarianceExpression ξ t u m ρ c κ μ ≤ -t * mixedPairCascadeCorrection ξ m ρ c κ := by
  rw [mixedPairCovarianceExpression_eq ξ t u m ρ c κ hm hρ0 hc0 hρ1 hc1 μ hμ1]
  exact sub_le_self _ (mixedPairCovarianceRemainder_nonneg hn ξ u ht m ρ c κ hmono μ hμ0 hρ hc)


end FourPapersCommon
